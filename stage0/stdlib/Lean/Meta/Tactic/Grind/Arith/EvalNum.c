// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.EvalNum
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.IntInstTesters import Lean.Meta.NatInstTesters
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_checkExp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_checkExp___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_checkExp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "exponent "};
static const lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_checkExp___closed__1_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_checkExp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__2;
static const lean_string_object l_Lean_Meta_Grind_Arith_checkExp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = " exceeds threshold for exponentiation `(exp := "};
static const lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_checkExp___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_checkExp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__4;
static const lean_string_object l_Lean_Meta_Grind_Arith_checkExp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ")`"};
static const lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_checkExp___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_checkExp___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__6;
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 81, 163, 94, 71, 156, 90, 186)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natAbs"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4_value),LEAN_SCALAR_PTR_LITERAL(255, 186, 174, 182, 213, 167, 94, 168)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6_value),LEAN_SCALAR_PTR_LITERAL(147, 74, 209, 32, 95, 50, 220, 192)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNatCastInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 224, 75, 57, 255, 108, 159, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2_value),LEAN_SCALAR_PTR_LITERAL(19, 237, 167, 212, 100, 179, 19, 112)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9_value;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHSubInt___redArg(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulInt___redArg(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHDivInt___redArg(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHModInt___redArg(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHPowInt___redArg(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstNegInt___redArg(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddNat___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulNat___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHSubNat___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHDivNat___redArg(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHModNat___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHPowNat___redArg(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalNat_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalNat_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalInt_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalInt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_checkExp___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_checkExp___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_checkExp___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_checkExp___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_88; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Meta_Grind_Arith_checkExp___lam__0(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_18 = lean_ctor_get(x_17, 0);
x_88 = !lean_is_exclusive(x_17);
if (x_88 == 0)
{
x_19 = x_17;
x_20 = x_88;
goto block_87;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_21, 7);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_nat_dec_lt(x_22, x_1);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_24 = ((lean_object*)(l_Lean_Meta_Grind_Arith_checkExp___closed__0));
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_24);
x_25 = x_19;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
else
{
lean_object* x_28; 
lean_del_object(x_19);
x_28 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_78; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lean_Meta_Grind_Arith_checkExp___lam__0(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_31 = lean_ctor_get(x_30, 0);
x_78 = !lean_is_exclusive(x_30);
if (x_78 == 0)
{
x_32 = x_30;
x_33 = x_78;
goto block_77;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_76; 
x_34 = lean_ctor_get(x_31, 0);
x_76 = !lean_is_exclusive(x_31);
if (x_76 == 0)
{
x_35 = x_31;
x_36 = x_76;
goto block_75;
}
else
{
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_box(0);
x_36 = x_76;
goto block_75;
}
block_75:
{
uint8_t x_37; 
x_37 = lean_ctor_get_uint8(x_34, sizeof(void*)*11 + 15);
lean_dec(x_34);
if (x_37 == 0)
{
lean_del_object(x_35);
lean_del_object(x_32);
lean_dec(x_1);
goto block_14;
}
else
{
lean_object* x_38; 
x_38 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_ctor_get(x_39, 7);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_obj_once(&l_Lean_Meta_Grind_Arith_checkExp___closed__2, &l_Lean_Meta_Grind_Arith_checkExp___closed__2_once, _init_l_Lean_Meta_Grind_Arith_checkExp___closed__2);
x_42 = l_Nat_reprFast(x_1);
if (x_36 == 0)
{
lean_ctor_set_tag(x_35, 3);
lean_ctor_set(x_35, 0, x_42);
x_43 = x_35;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_66, 0, x_42);
x_43 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = l_Lean_MessageData_ofFormat(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_obj_once(&l_Lean_Meta_Grind_Arith_checkExp___closed__4, &l_Lean_Meta_Grind_Arith_checkExp___closed__4_once, _init_l_Lean_Meta_Grind_Arith_checkExp___closed__4);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Nat_reprFast(x_40);
if (x_33 == 0)
{
lean_ctor_set_tag(x_32, 3);
lean_ctor_set(x_32, 0, x_48);
x_49 = x_32;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_64, 0, x_48);
x_49 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = l_Lean_MessageData_ofFormat(x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_obj_once(&l_Lean_Meta_Grind_Arith_checkExp___closed__6, &l_Lean_Meta_Grind_Arith_checkExp___closed__6_once, _init_l_Lean_Meta_Grind_Arith_checkExp___closed__6);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Meta_Grind_reportIssue(x_53, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_54) == 0)
{
lean_dec_ref(x_54);
goto block_14;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
x_55 = lean_ctor_get(x_54, 0);
x_62 = !lean_is_exclusive(x_54);
if (x_62 == 0)
{
x_56 = x_54;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_74; 
lean_del_object(x_35);
lean_del_object(x_32);
lean_dec(x_1);
x_67 = lean_ctor_get(x_38, 0);
x_74 = !lean_is_exclusive(x_38);
if (x_74 == 0)
{
x_68 = x_38;
x_69 = x_74;
goto block_73;
}
else
{
lean_inc(x_67);
lean_dec(x_38);
x_68 = lean_box(0);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_69 == 0)
{
x_70 = x_68;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_67);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_86; 
lean_dec(x_1);
x_79 = lean_ctor_get(x_28, 0);
x_86 = !lean_is_exclusive(x_28);
if (x_86 == 0)
{
x_80 = x_28;
x_81 = x_86;
goto block_85;
}
else
{
lean_inc(x_79);
lean_dec(x_28);
x_80 = lean_box(0);
x_81 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_82; 
if (x_81 == 0)
{
x_82 = x_80;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_79);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_96; 
lean_dec(x_1);
x_89 = lean_ctor_get(x_15, 0);
x_96 = !lean_is_exclusive(x_15);
if (x_96 == 0)
{
x_90 = x_15;
x_91 = x_96;
goto block_95;
}
else
{
lean_inc(x_89);
lean_dec(x_15);
x_90 = lean_box(0);
x_91 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_92; 
if (x_91 == 0)
{
x_92 = x_90;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_89);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_checkExp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_75; 
lean_inc_ref(x_1);
x_75 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_8);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_446; 
x_76 = lean_ctor_get(x_75, 0);
x_446 = !lean_is_exclusive(x_75);
if (x_446 == 0)
{
x_77 = x_75;
x_78 = x_446;
goto block_445;
}
else
{
lean_inc(x_76);
lean_dec(x_75);
x_77 = lean_box(0);
x_78 = x_446;
goto block_445;
}
block_445:
{
lean_object* x_84; uint8_t x_85; 
x_84 = l_Lean_Expr_cleanupAnnotations(x_76);
x_85 = l_Lean_Expr_isApp(x_84);
if (x_85 == 0)
{
lean_dec_ref(x_84);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
goto block_83;
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_84, 1);
lean_inc_ref(x_86);
x_87 = l_Lean_Expr_appFnCleanup___redArg(x_84);
x_88 = l_Lean_Expr_isApp(x_87);
if (x_88 == 0)
{
lean_dec_ref(x_87);
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
goto block_83;
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_ctor_get(x_87, 1);
lean_inc_ref(x_89);
x_90 = l_Lean_Expr_appFnCleanup___redArg(x_87);
x_91 = l_Lean_Expr_isApp(x_90);
if (x_91 == 0)
{
lean_dec_ref(x_90);
lean_dec_ref(x_89);
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
goto block_83;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_92 = lean_ctor_get(x_90, 1);
lean_inc_ref(x_92);
x_93 = l_Lean_Expr_appFnCleanup___redArg(x_90);
x_94 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3));
x_95 = l_Lean_Expr_isConstOf(x_93, x_94);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6));
x_97 = l_Lean_Expr_isConstOf(x_93, x_96);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12));
x_99 = l_Lean_Expr_isConstOf(x_93, x_98);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; 
lean_dec_ref(x_1);
x_100 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9));
x_101 = l_Lean_Expr_isConstOf(x_93, x_100);
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = l_Lean_Expr_isApp(x_93);
if (x_102 == 0)
{
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec_ref(x_89);
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
goto block_83;
}
else
{
lean_object* x_103; uint8_t x_104; 
x_103 = l_Lean_Expr_appFnCleanup___redArg(x_93);
x_104 = l_Lean_Expr_isApp(x_103);
if (x_104 == 0)
{
lean_dec_ref(x_103);
lean_dec_ref(x_92);
lean_dec_ref(x_89);
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
goto block_83;
}
else
{
lean_object* x_105; uint8_t x_106; 
x_105 = l_Lean_Expr_appFnCleanup___redArg(x_103);
x_106 = l_Lean_Expr_isApp(x_105);
if (x_106 == 0)
{
lean_dec_ref(x_105);
lean_dec_ref(x_92);
lean_dec_ref(x_89);
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
goto block_83;
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = l_Lean_Expr_appFnCleanup___redArg(x_105);
x_108 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15));
x_109 = l_Lean_Expr_isConstOf(x_107, x_108);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18));
x_111 = l_Lean_Expr_isConstOf(x_107, x_110);
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21));
x_113 = l_Lean_Expr_isConstOf(x_107, x_112);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27));
x_115 = l_Lean_Expr_isConstOf(x_107, x_114);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24));
x_117 = l_Lean_Expr_isConstOf(x_107, x_116);
if (x_117 == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30));
x_119 = l_Lean_Expr_isConstOf(x_107, x_118);
lean_dec_ref(x_107);
if (x_119 == 0)
{
lean_dec_ref(x_92);
lean_dec_ref(x_89);
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
goto block_83;
}
else
{
lean_object* x_120; 
lean_del_object(x_77);
x_120 = l_Lean_Meta_Structural_isInstHAddInt___redArg(x_92, x_8);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_152; 
x_121 = lean_ctor_get(x_120, 0);
x_152 = !lean_is_exclusive(x_120);
if (x_152 == 0)
{
x_122 = x_120;
x_123 = x_152;
goto block_151;
}
else
{
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_box(0);
x_123 = x_152;
goto block_151;
}
block_151:
{
uint8_t x_124; 
x_124 = lean_unbox(x_121);
lean_dec(x_121);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
lean_dec_ref(x_89);
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_125 = lean_box(0);
if (x_123 == 0)
{
lean_ctor_set(x_122, 0, x_125);
x_126 = x_122;
goto block_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_125);
x_126 = x_128;
goto block_127;
}
block_127:
{
return x_126;
}
}
else
{
lean_object* x_129; 
lean_del_object(x_122);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_129 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
if (lean_obj_tag(x_130) == 0)
{
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_129;
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec_ref(x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec_ref(x_130);
x_132 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_86, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
if (lean_obj_tag(x_133) == 0)
{
lean_dec(x_131);
return x_132;
}
else
{
lean_object* x_134; uint8_t x_135; uint8_t x_149; 
x_149 = !lean_is_exclusive(x_132);
if (x_149 == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_132, 0);
lean_dec(x_150);
x_134 = x_132;
x_135 = x_149;
goto block_148;
}
else
{
lean_dec(x_132);
x_134 = lean_box(0);
x_135 = x_149;
goto block_148;
}
block_148:
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_147; 
x_136 = lean_ctor_get(x_133, 0);
x_147 = !lean_is_exclusive(x_133);
if (x_147 == 0)
{
x_137 = x_133;
x_138 = x_147;
goto block_146;
}
else
{
lean_inc(x_136);
lean_dec(x_133);
x_137 = lean_box(0);
x_138 = x_147;
goto block_146;
}
block_146:
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_int_add(x_131, x_136);
lean_dec(x_136);
lean_dec(x_131);
if (x_138 == 0)
{
lean_ctor_set(x_137, 0, x_139);
x_140 = x_137;
goto block_144;
}
else
{
lean_object* x_145; 
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_139);
x_140 = x_145;
goto block_144;
}
block_144:
{
lean_object* x_141; 
if (x_135 == 0)
{
lean_ctor_set(x_134, 0, x_140);
x_141 = x_134;
goto block_142;
}
else
{
lean_object* x_143; 
x_143 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_143, 0, x_140);
x_141 = x_143;
goto block_142;
}
block_142:
{
return x_141;
}
}
}
}
}
}
else
{
lean_dec(x_131);
return x_132;
}
}
}
else
{
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_129;
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_160; 
lean_dec_ref(x_89);
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_153 = lean_ctor_get(x_120, 0);
x_160 = !lean_is_exclusive(x_120);
if (x_160 == 0)
{
x_154 = x_120;
x_155 = x_160;
goto block_159;
}
else
{
lean_inc(x_153);
lean_dec(x_120);
x_154 = lean_box(0);
x_155 = x_160;
goto block_159;
}
block_159:
{
lean_object* x_156; 
if (x_155 == 0)
{
x_156 = x_154;
goto block_157;
}
else
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_153);
x_156 = x_158;
goto block_157;
}
block_157:
{
return x_156;
}
}
}
}
}
else
{
lean_object* x_161; 
lean_dec_ref(x_107);
lean_del_object(x_77);
x_161 = l_Lean_Meta_Structural_isInstHSubInt___redArg(x_92, x_8);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; uint8_t x_164; uint8_t x_193; 
x_162 = lean_ctor_get(x_161, 0);
x_193 = !lean_is_exclusive(x_161);
if (x_193 == 0)
{
x_163 = x_161;
x_164 = x_193;
goto block_192;
}
else
{
lean_inc(x_162);
lean_dec(x_161);
x_163 = lean_box(0);
x_164 = x_193;
goto block_192;
}
block_192:
{
uint8_t x_165; 
x_165 = lean_unbox(x_162);
lean_dec(x_162);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
lean_dec_ref(x_89);
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_166 = lean_box(0);
if (x_164 == 0)
{
lean_ctor_set(x_163, 0, x_166);
x_167 = x_163;
goto block_168;
}
else
{
lean_object* x_169; 
x_169 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_169, 0, x_166);
x_167 = x_169;
goto block_168;
}
block_168:
{
return x_167;
}
}
else
{
lean_object* x_170; 
lean_del_object(x_163);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_170 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
if (lean_obj_tag(x_171) == 0)
{
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_170;
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec_ref(x_170);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_dec_ref(x_171);
x_173 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_86, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
if (lean_obj_tag(x_174) == 0)
{
lean_dec(x_172);
return x_173;
}
else
{
lean_object* x_175; uint8_t x_176; uint8_t x_190; 
x_190 = !lean_is_exclusive(x_173);
if (x_190 == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_173, 0);
lean_dec(x_191);
x_175 = x_173;
x_176 = x_190;
goto block_189;
}
else
{
lean_dec(x_173);
x_175 = lean_box(0);
x_176 = x_190;
goto block_189;
}
block_189:
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; uint8_t x_188; 
x_177 = lean_ctor_get(x_174, 0);
x_188 = !lean_is_exclusive(x_174);
if (x_188 == 0)
{
x_178 = x_174;
x_179 = x_188;
goto block_187;
}
else
{
lean_inc(x_177);
lean_dec(x_174);
x_178 = lean_box(0);
x_179 = x_188;
goto block_187;
}
block_187:
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_int_sub(x_172, x_177);
lean_dec(x_177);
lean_dec(x_172);
if (x_179 == 0)
{
lean_ctor_set(x_178, 0, x_180);
x_181 = x_178;
goto block_185;
}
else
{
lean_object* x_186; 
x_186 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_186, 0, x_180);
x_181 = x_186;
goto block_185;
}
block_185:
{
lean_object* x_182; 
if (x_176 == 0)
{
lean_ctor_set(x_175, 0, x_181);
x_182 = x_175;
goto block_183;
}
else
{
lean_object* x_184; 
x_184 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_184, 0, x_181);
x_182 = x_184;
goto block_183;
}
block_183:
{
return x_182;
}
}
}
}
}
}
else
{
lean_dec(x_172);
return x_173;
}
}
}
else
{
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_170;
}
}
}
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; uint8_t x_201; 
lean_dec_ref(x_89);
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_194 = lean_ctor_get(x_161, 0);
x_201 = !lean_is_exclusive(x_161);
if (x_201 == 0)
{
x_195 = x_161;
x_196 = x_201;
goto block_200;
}
else
{
lean_inc(x_194);
lean_dec(x_161);
x_195 = lean_box(0);
x_196 = x_201;
goto block_200;
}
block_200:
{
lean_object* x_197; 
if (x_196 == 0)
{
x_197 = x_195;
goto block_198;
}
else
{
lean_object* x_199; 
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_194);
x_197 = x_199;
goto block_198;
}
block_198:
{
return x_197;
}
}
}
}
}
else
{
lean_object* x_202; 
lean_dec_ref(x_107);
lean_del_object(x_77);
x_202 = l_Lean_Meta_Structural_isInstHMulInt___redArg(x_92, x_8);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; uint8_t x_234; 
x_203 = lean_ctor_get(x_202, 0);
x_234 = !lean_is_exclusive(x_202);
if (x_234 == 0)
{
x_204 = x_202;
x_205 = x_234;
goto block_233;
}
else
{
lean_inc(x_203);
lean_dec(x_202);
x_204 = lean_box(0);
x_205 = x_234;
goto block_233;
}
block_233:
{
uint8_t x_206; 
x_206 = lean_unbox(x_203);
lean_dec(x_203);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; 
lean_dec_ref(x_89);
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_207 = lean_box(0);
if (x_205 == 0)
{
lean_ctor_set(x_204, 0, x_207);
x_208 = x_204;
goto block_209;
}
else
{
lean_object* x_210; 
x_210 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_210, 0, x_207);
x_208 = x_210;
goto block_209;
}
block_209:
{
return x_208;
}
}
else
{
lean_object* x_211; 
lean_del_object(x_204);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_211 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
if (lean_obj_tag(x_212) == 0)
{
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_211;
}
else
{
lean_object* x_213; lean_object* x_214; 
lean_dec_ref(x_211);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
lean_dec_ref(x_212);
x_214 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_86, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
if (lean_obj_tag(x_215) == 0)
{
lean_dec(x_213);
return x_214;
}
else
{
lean_object* x_216; uint8_t x_217; uint8_t x_231; 
x_231 = !lean_is_exclusive(x_214);
if (x_231 == 0)
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_214, 0);
lean_dec(x_232);
x_216 = x_214;
x_217 = x_231;
goto block_230;
}
else
{
lean_dec(x_214);
x_216 = lean_box(0);
x_217 = x_231;
goto block_230;
}
block_230:
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; uint8_t x_229; 
x_218 = lean_ctor_get(x_215, 0);
x_229 = !lean_is_exclusive(x_215);
if (x_229 == 0)
{
x_219 = x_215;
x_220 = x_229;
goto block_228;
}
else
{
lean_inc(x_218);
lean_dec(x_215);
x_219 = lean_box(0);
x_220 = x_229;
goto block_228;
}
block_228:
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_int_mul(x_213, x_218);
lean_dec(x_218);
lean_dec(x_213);
if (x_220 == 0)
{
lean_ctor_set(x_219, 0, x_221);
x_222 = x_219;
goto block_226;
}
else
{
lean_object* x_227; 
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_221);
x_222 = x_227;
goto block_226;
}
block_226:
{
lean_object* x_223; 
if (x_217 == 0)
{
lean_ctor_set(x_216, 0, x_222);
x_223 = x_216;
goto block_224;
}
else
{
lean_object* x_225; 
x_225 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_225, 0, x_222);
x_223 = x_225;
goto block_224;
}
block_224:
{
return x_223;
}
}
}
}
}
}
else
{
lean_dec(x_213);
return x_214;
}
}
}
else
{
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_211;
}
}
}
}
else
{
lean_object* x_235; lean_object* x_236; uint8_t x_237; uint8_t x_242; 
lean_dec_ref(x_89);
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_235 = lean_ctor_get(x_202, 0);
x_242 = !lean_is_exclusive(x_202);
if (x_242 == 0)
{
x_236 = x_202;
x_237 = x_242;
goto block_241;
}
else
{
lean_inc(x_235);
lean_dec(x_202);
x_236 = lean_box(0);
x_237 = x_242;
goto block_241;
}
block_241:
{
lean_object* x_238; 
if (x_237 == 0)
{
x_238 = x_236;
goto block_239;
}
else
{
lean_object* x_240; 
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_235);
x_238 = x_240;
goto block_239;
}
block_239:
{
return x_238;
}
}
}
}
}
else
{
lean_object* x_243; 
lean_dec_ref(x_107);
lean_del_object(x_77);
x_243 = l_Lean_Meta_Structural_isInstHDivInt___redArg(x_92, x_8);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; uint8_t x_246; uint8_t x_275; 
x_244 = lean_ctor_get(x_243, 0);
x_275 = !lean_is_exclusive(x_243);
if (x_275 == 0)
{
x_245 = x_243;
x_246 = x_275;
goto block_274;
}
else
{
lean_inc(x_244);
lean_dec(x_243);
x_245 = lean_box(0);
x_246 = x_275;
goto block_274;
}
block_274:
{
uint8_t x_247; 
x_247 = lean_unbox(x_244);
lean_dec(x_244);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; 
lean_dec_ref(x_89);
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_248 = lean_box(0);
if (x_246 == 0)
{
lean_ctor_set(x_245, 0, x_248);
x_249 = x_245;
goto block_250;
}
else
{
lean_object* x_251; 
x_251 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_251, 0, x_248);
x_249 = x_251;
goto block_250;
}
block_250:
{
return x_249;
}
}
else
{
lean_object* x_252; 
lean_del_object(x_245);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_252 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
if (lean_obj_tag(x_253) == 0)
{
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_252;
}
else
{
lean_object* x_254; lean_object* x_255; 
lean_dec_ref(x_252);
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec_ref(x_253);
x_255 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_86, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
if (lean_obj_tag(x_256) == 0)
{
lean_dec(x_254);
return x_255;
}
else
{
lean_object* x_257; uint8_t x_258; uint8_t x_272; 
x_272 = !lean_is_exclusive(x_255);
if (x_272 == 0)
{
lean_object* x_273; 
x_273 = lean_ctor_get(x_255, 0);
lean_dec(x_273);
x_257 = x_255;
x_258 = x_272;
goto block_271;
}
else
{
lean_dec(x_255);
x_257 = lean_box(0);
x_258 = x_272;
goto block_271;
}
block_271:
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; uint8_t x_270; 
x_259 = lean_ctor_get(x_256, 0);
x_270 = !lean_is_exclusive(x_256);
if (x_270 == 0)
{
x_260 = x_256;
x_261 = x_270;
goto block_269;
}
else
{
lean_inc(x_259);
lean_dec(x_256);
x_260 = lean_box(0);
x_261 = x_270;
goto block_269;
}
block_269:
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_int_ediv(x_254, x_259);
lean_dec(x_259);
lean_dec(x_254);
if (x_261 == 0)
{
lean_ctor_set(x_260, 0, x_262);
x_263 = x_260;
goto block_267;
}
else
{
lean_object* x_268; 
x_268 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_268, 0, x_262);
x_263 = x_268;
goto block_267;
}
block_267:
{
lean_object* x_264; 
if (x_258 == 0)
{
lean_ctor_set(x_257, 0, x_263);
x_264 = x_257;
goto block_265;
}
else
{
lean_object* x_266; 
x_266 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_266, 0, x_263);
x_264 = x_266;
goto block_265;
}
block_265:
{
return x_264;
}
}
}
}
}
}
else
{
lean_dec(x_254);
return x_255;
}
}
}
else
{
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_252;
}
}
}
}
else
{
lean_object* x_276; lean_object* x_277; uint8_t x_278; uint8_t x_283; 
lean_dec_ref(x_89);
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_276 = lean_ctor_get(x_243, 0);
x_283 = !lean_is_exclusive(x_243);
if (x_283 == 0)
{
x_277 = x_243;
x_278 = x_283;
goto block_282;
}
else
{
lean_inc(x_276);
lean_dec(x_243);
x_277 = lean_box(0);
x_278 = x_283;
goto block_282;
}
block_282:
{
lean_object* x_279; 
if (x_278 == 0)
{
x_279 = x_277;
goto block_280;
}
else
{
lean_object* x_281; 
x_281 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_281, 0, x_276);
x_279 = x_281;
goto block_280;
}
block_280:
{
return x_279;
}
}
}
}
}
else
{
lean_object* x_284; 
lean_dec_ref(x_107);
lean_del_object(x_77);
x_284 = l_Lean_Meta_Structural_isInstHModInt___redArg(x_92, x_8);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; uint8_t x_287; uint8_t x_316; 
x_285 = lean_ctor_get(x_284, 0);
x_316 = !lean_is_exclusive(x_284);
if (x_316 == 0)
{
x_286 = x_284;
x_287 = x_316;
goto block_315;
}
else
{
lean_inc(x_285);
lean_dec(x_284);
x_286 = lean_box(0);
x_287 = x_316;
goto block_315;
}
block_315:
{
uint8_t x_288; 
x_288 = lean_unbox(x_285);
lean_dec(x_285);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; 
lean_dec_ref(x_89);
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_289 = lean_box(0);
if (x_287 == 0)
{
lean_ctor_set(x_286, 0, x_289);
x_290 = x_286;
goto block_291;
}
else
{
lean_object* x_292; 
x_292 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_292, 0, x_289);
x_290 = x_292;
goto block_291;
}
block_291:
{
return x_290;
}
}
else
{
lean_object* x_293; 
lean_del_object(x_286);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_293 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
if (lean_obj_tag(x_294) == 0)
{
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_293;
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_dec_ref(x_293);
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
lean_dec_ref(x_294);
x_296 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_86, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
if (lean_obj_tag(x_297) == 0)
{
lean_dec(x_295);
return x_296;
}
else
{
lean_object* x_298; uint8_t x_299; uint8_t x_313; 
x_313 = !lean_is_exclusive(x_296);
if (x_313 == 0)
{
lean_object* x_314; 
x_314 = lean_ctor_get(x_296, 0);
lean_dec(x_314);
x_298 = x_296;
x_299 = x_313;
goto block_312;
}
else
{
lean_dec(x_296);
x_298 = lean_box(0);
x_299 = x_313;
goto block_312;
}
block_312:
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; uint8_t x_311; 
x_300 = lean_ctor_get(x_297, 0);
x_311 = !lean_is_exclusive(x_297);
if (x_311 == 0)
{
x_301 = x_297;
x_302 = x_311;
goto block_310;
}
else
{
lean_inc(x_300);
lean_dec(x_297);
x_301 = lean_box(0);
x_302 = x_311;
goto block_310;
}
block_310:
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_int_emod(x_295, x_300);
lean_dec(x_300);
lean_dec(x_295);
if (x_302 == 0)
{
lean_ctor_set(x_301, 0, x_303);
x_304 = x_301;
goto block_308;
}
else
{
lean_object* x_309; 
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_303);
x_304 = x_309;
goto block_308;
}
block_308:
{
lean_object* x_305; 
if (x_299 == 0)
{
lean_ctor_set(x_298, 0, x_304);
x_305 = x_298;
goto block_306;
}
else
{
lean_object* x_307; 
x_307 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_307, 0, x_304);
x_305 = x_307;
goto block_306;
}
block_306:
{
return x_305;
}
}
}
}
}
}
else
{
lean_dec(x_295);
return x_296;
}
}
}
else
{
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_293;
}
}
}
}
else
{
lean_object* x_317; lean_object* x_318; uint8_t x_319; uint8_t x_324; 
lean_dec_ref(x_89);
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_317 = lean_ctor_get(x_284, 0);
x_324 = !lean_is_exclusive(x_284);
if (x_324 == 0)
{
x_318 = x_284;
x_319 = x_324;
goto block_323;
}
else
{
lean_inc(x_317);
lean_dec(x_284);
x_318 = lean_box(0);
x_319 = x_324;
goto block_323;
}
block_323:
{
lean_object* x_320; 
if (x_319 == 0)
{
x_320 = x_318;
goto block_321;
}
else
{
lean_object* x_322; 
x_322 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_322, 0, x_317);
x_320 = x_322;
goto block_321;
}
block_321:
{
return x_320;
}
}
}
}
}
else
{
lean_object* x_325; 
lean_dec_ref(x_107);
lean_del_object(x_77);
x_325 = l_Lean_Meta_Structural_isInstHPowInt___redArg(x_92, x_8);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; uint8_t x_328; uint8_t x_387; 
x_326 = lean_ctor_get(x_325, 0);
x_387 = !lean_is_exclusive(x_325);
if (x_387 == 0)
{
x_327 = x_325;
x_328 = x_387;
goto block_386;
}
else
{
lean_inc(x_326);
lean_dec(x_325);
x_327 = lean_box(0);
x_328 = x_387;
goto block_386;
}
block_386:
{
uint8_t x_329; 
x_329 = lean_unbox(x_326);
lean_dec(x_326);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; 
lean_dec_ref(x_89);
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_330 = lean_box(0);
if (x_328 == 0)
{
lean_ctor_set(x_327, 0, x_330);
x_331 = x_327;
goto block_332;
}
else
{
lean_object* x_333; 
x_333 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_333, 0, x_330);
x_331 = x_333;
goto block_332;
}
block_332:
{
return x_331;
}
}
else
{
lean_object* x_334; 
lean_del_object(x_327);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_334 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; 
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
if (lean_obj_tag(x_335) == 0)
{
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_334;
}
else
{
lean_object* x_336; lean_object* x_337; 
lean_dec_ref(x_334);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
lean_dec_ref(x_335);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_337 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_86, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; uint8_t x_340; uint8_t x_377; 
x_338 = lean_ctor_get(x_337, 0);
x_377 = !lean_is_exclusive(x_337);
if (x_377 == 0)
{
x_339 = x_337;
x_340 = x_377;
goto block_376;
}
else
{
lean_inc(x_338);
lean_dec(x_337);
x_339 = lean_box(0);
x_340 = x_377;
goto block_376;
}
block_376:
{
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_341; lean_object* x_342; 
lean_dec(x_336);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_341 = lean_box(0);
if (x_340 == 0)
{
lean_ctor_set(x_339, 0, x_341);
x_342 = x_339;
goto block_343;
}
else
{
lean_object* x_344; 
x_344 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_344, 0, x_341);
x_342 = x_344;
goto block_343;
}
block_343:
{
return x_342;
}
}
else
{
lean_object* x_345; lean_object* x_346; 
lean_del_object(x_339);
x_345 = lean_ctor_get(x_338, 0);
lean_inc(x_345);
lean_dec_ref(x_338);
lean_inc(x_345);
x_346 = l_Lean_Meta_Grind_Arith_checkExp(x_345, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; uint8_t x_349; uint8_t x_367; 
x_347 = lean_ctor_get(x_346, 0);
x_367 = !lean_is_exclusive(x_346);
if (x_367 == 0)
{
x_348 = x_346;
x_349 = x_367;
goto block_366;
}
else
{
lean_inc(x_347);
lean_dec(x_346);
x_348 = lean_box(0);
x_349 = x_367;
goto block_366;
}
block_366:
{
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_350; lean_object* x_351; 
lean_dec(x_345);
lean_dec(x_336);
x_350 = lean_box(0);
if (x_349 == 0)
{
lean_ctor_set(x_348, 0, x_350);
x_351 = x_348;
goto block_352;
}
else
{
lean_object* x_353; 
x_353 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_353, 0, x_350);
x_351 = x_353;
goto block_352;
}
block_352:
{
return x_351;
}
}
else
{
lean_object* x_354; uint8_t x_355; uint8_t x_364; 
x_364 = !lean_is_exclusive(x_347);
if (x_364 == 0)
{
lean_object* x_365; 
x_365 = lean_ctor_get(x_347, 0);
lean_dec(x_365);
x_354 = x_347;
x_355 = x_364;
goto block_363;
}
else
{
lean_dec(x_347);
x_354 = lean_box(0);
x_355 = x_364;
goto block_363;
}
block_363:
{
lean_object* x_356; lean_object* x_357; 
x_356 = l_Int_pow(x_336, x_345);
lean_dec(x_345);
lean_dec(x_336);
if (x_355 == 0)
{
lean_ctor_set(x_354, 0, x_356);
x_357 = x_354;
goto block_361;
}
else
{
lean_object* x_362; 
x_362 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_362, 0, x_356);
x_357 = x_362;
goto block_361;
}
block_361:
{
lean_object* x_358; 
if (x_349 == 0)
{
lean_ctor_set(x_348, 0, x_357);
x_358 = x_348;
goto block_359;
}
else
{
lean_object* x_360; 
x_360 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_360, 0, x_357);
x_358 = x_360;
goto block_359;
}
block_359:
{
return x_358;
}
}
}
}
}
}
else
{
lean_object* x_368; lean_object* x_369; uint8_t x_370; uint8_t x_375; 
lean_dec(x_345);
lean_dec(x_336);
x_368 = lean_ctor_get(x_346, 0);
x_375 = !lean_is_exclusive(x_346);
if (x_375 == 0)
{
x_369 = x_346;
x_370 = x_375;
goto block_374;
}
else
{
lean_inc(x_368);
lean_dec(x_346);
x_369 = lean_box(0);
x_370 = x_375;
goto block_374;
}
block_374:
{
lean_object* x_371; 
if (x_370 == 0)
{
x_371 = x_369;
goto block_372;
}
else
{
lean_object* x_373; 
x_373 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_373, 0, x_368);
x_371 = x_373;
goto block_372;
}
block_372:
{
return x_371;
}
}
}
}
}
}
else
{
lean_object* x_378; lean_object* x_379; uint8_t x_380; uint8_t x_385; 
lean_dec(x_336);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_378 = lean_ctor_get(x_337, 0);
x_385 = !lean_is_exclusive(x_337);
if (x_385 == 0)
{
x_379 = x_337;
x_380 = x_385;
goto block_384;
}
else
{
lean_inc(x_378);
lean_dec(x_337);
x_379 = lean_box(0);
x_380 = x_385;
goto block_384;
}
block_384:
{
lean_object* x_381; 
if (x_380 == 0)
{
x_381 = x_379;
goto block_382;
}
else
{
lean_object* x_383; 
x_383 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_383, 0, x_378);
x_381 = x_383;
goto block_382;
}
block_382:
{
return x_381;
}
}
}
}
}
else
{
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_334;
}
}
}
}
else
{
lean_object* x_388; lean_object* x_389; uint8_t x_390; uint8_t x_395; 
lean_dec_ref(x_89);
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_388 = lean_ctor_get(x_325, 0);
x_395 = !lean_is_exclusive(x_325);
if (x_395 == 0)
{
x_389 = x_325;
x_390 = x_395;
goto block_394;
}
else
{
lean_inc(x_388);
lean_dec(x_325);
x_389 = lean_box(0);
x_390 = x_395;
goto block_394;
}
block_394:
{
lean_object* x_391; 
if (x_390 == 0)
{
x_391 = x_389;
goto block_392;
}
else
{
lean_object* x_393; 
x_393 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_393, 0, x_388);
x_391 = x_393;
goto block_392;
}
block_392:
{
return x_391;
}
}
}
}
}
}
}
}
else
{
lean_object* x_396; 
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_del_object(x_77);
x_396 = l_Lean_Meta_Structural_isInstNegInt___redArg(x_89, x_8);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; lean_object* x_398; uint8_t x_399; uint8_t x_425; 
x_397 = lean_ctor_get(x_396, 0);
x_425 = !lean_is_exclusive(x_396);
if (x_425 == 0)
{
x_398 = x_396;
x_399 = x_425;
goto block_424;
}
else
{
lean_inc(x_397);
lean_dec(x_396);
x_398 = lean_box(0);
x_399 = x_425;
goto block_424;
}
block_424:
{
uint8_t x_400; 
x_400 = lean_unbox(x_397);
lean_dec(x_397);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; 
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_401 = lean_box(0);
if (x_399 == 0)
{
lean_ctor_set(x_398, 0, x_401);
x_402 = x_398;
goto block_403;
}
else
{
lean_object* x_404; 
x_404 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_404, 0, x_401);
x_402 = x_404;
goto block_403;
}
block_403:
{
return x_402;
}
}
else
{
lean_object* x_405; 
lean_del_object(x_398);
x_405 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_86, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
if (lean_obj_tag(x_406) == 0)
{
return x_405;
}
else
{
lean_object* x_407; uint8_t x_408; uint8_t x_422; 
x_422 = !lean_is_exclusive(x_405);
if (x_422 == 0)
{
lean_object* x_423; 
x_423 = lean_ctor_get(x_405, 0);
lean_dec(x_423);
x_407 = x_405;
x_408 = x_422;
goto block_421;
}
else
{
lean_dec(x_405);
x_407 = lean_box(0);
x_408 = x_422;
goto block_421;
}
block_421:
{
lean_object* x_409; lean_object* x_410; uint8_t x_411; uint8_t x_420; 
x_409 = lean_ctor_get(x_406, 0);
x_420 = !lean_is_exclusive(x_406);
if (x_420 == 0)
{
x_410 = x_406;
x_411 = x_420;
goto block_419;
}
else
{
lean_inc(x_409);
lean_dec(x_406);
x_410 = lean_box(0);
x_411 = x_420;
goto block_419;
}
block_419:
{
lean_object* x_412; lean_object* x_413; 
x_412 = lean_int_neg(x_409);
lean_dec(x_409);
if (x_411 == 0)
{
lean_ctor_set(x_410, 0, x_412);
x_413 = x_410;
goto block_417;
}
else
{
lean_object* x_418; 
x_418 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_418, 0, x_412);
x_413 = x_418;
goto block_417;
}
block_417:
{
lean_object* x_414; 
if (x_408 == 0)
{
lean_ctor_set(x_407, 0, x_413);
x_414 = x_407;
goto block_415;
}
else
{
lean_object* x_416; 
x_416 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_416, 0, x_413);
x_414 = x_416;
goto block_415;
}
block_415:
{
return x_414;
}
}
}
}
}
}
else
{
return x_405;
}
}
}
}
else
{
lean_object* x_426; lean_object* x_427; uint8_t x_428; uint8_t x_433; 
lean_dec_ref(x_86);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_426 = lean_ctor_get(x_396, 0);
x_433 = !lean_is_exclusive(x_396);
if (x_433 == 0)
{
x_427 = x_396;
x_428 = x_433;
goto block_432;
}
else
{
lean_inc(x_426);
lean_dec(x_396);
x_427 = lean_box(0);
x_428 = x_433;
goto block_432;
}
block_432:
{
lean_object* x_429; 
if (x_428 == 0)
{
x_429 = x_427;
goto block_430;
}
else
{
lean_object* x_431; 
x_431 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_431, 0, x_426);
x_429 = x_431;
goto block_430;
}
block_430:
{
return x_429;
}
}
}
}
}
else
{
lean_object* x_434; 
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec_ref(x_89);
lean_dec_ref(x_86);
lean_del_object(x_77);
x_434 = l_Lean_Meta_getIntValue_x3f(x_1, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; 
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
if (lean_obj_tag(x_435) == 1)
{
lean_dec_ref(x_435);
return x_434;
}
else
{
lean_object* x_436; uint8_t x_437; uint8_t x_443; 
lean_dec(x_435);
x_443 = !lean_is_exclusive(x_434);
if (x_443 == 0)
{
lean_object* x_444; 
x_444 = lean_ctor_get(x_434, 0);
lean_dec(x_444);
x_436 = x_434;
x_437 = x_443;
goto block_442;
}
else
{
lean_dec(x_434);
x_436 = lean_box(0);
x_437 = x_443;
goto block_442;
}
block_442:
{
lean_object* x_438; lean_object* x_439; 
x_438 = lean_box(0);
if (x_437 == 0)
{
lean_ctor_set(x_436, 0, x_438);
x_439 = x_436;
goto block_440;
}
else
{
lean_object* x_441; 
x_441 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_441, 0, x_438);
x_439 = x_441;
goto block_440;
}
block_440:
{
return x_439;
}
}
}
}
else
{
return x_434;
}
}
}
else
{
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_del_object(x_77);
lean_dec_ref(x_1);
x_12 = x_89;
x_13 = x_86;
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
goto block_74;
}
}
else
{
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_del_object(x_77);
lean_dec_ref(x_1);
x_12 = x_89;
x_13 = x_86;
x_14 = x_2;
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
goto block_74;
}
}
}
}
block_83:
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_box(0);
if (x_78 == 0)
{
lean_ctor_set(x_77, 0, x_79);
x_80 = x_77;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_79);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
}
else
{
lean_object* x_447; lean_object* x_448; uint8_t x_449; uint8_t x_454; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_447 = lean_ctor_get(x_75, 0);
x_454 = !lean_is_exclusive(x_75);
if (x_454 == 0)
{
x_448 = x_75;
x_449 = x_454;
goto block_453;
}
else
{
lean_inc(x_447);
lean_dec(x_75);
x_448 = lean_box(0);
x_449 = x_454;
goto block_453;
}
block_453:
{
lean_object* x_450; 
if (x_449 == 0)
{
x_450 = x_448;
goto block_451;
}
else
{
lean_object* x_452; 
x_452 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_452, 0, x_447);
x_450 = x_452;
goto block_451;
}
block_451:
{
return x_450;
}
}
}
block_74:
{
lean_object* x_23; 
x_23 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_12, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_65; 
x_24 = lean_ctor_get(x_23, 0);
x_65 = !lean_is_exclusive(x_23);
if (x_65 == 0)
{
x_25 = x_23;
x_26 = x_65;
goto block_64;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = l_Lean_Expr_cleanupAnnotations(x_24);
x_28 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1));
x_29 = l_Lean_Expr_isConstOf(x_27, x_28);
lean_dec_ref(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_30 = lean_box(0);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_30);
x_31 = x_25;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
else
{
lean_object* x_34; 
lean_del_object(x_25);
x_34 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_55; 
x_35 = lean_ctor_get(x_34, 0);
x_55 = !lean_is_exclusive(x_34);
if (x_55 == 0)
{
x_36 = x_34;
x_37 = x_55;
goto block_54;
}
else
{
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = x_55;
goto block_54;
}
block_54:
{
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_38);
x_39 = x_36;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_53; 
x_42 = lean_ctor_get(x_35, 0);
x_53 = !lean_is_exclusive(x_35);
if (x_53 == 0)
{
x_43 = x_35;
x_44 = x_53;
goto block_52;
}
else
{
lean_inc(x_42);
lean_dec(x_35);
x_43 = lean_box(0);
x_44 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_nat_to_int(x_42);
if (x_44 == 0)
{
lean_ctor_set(x_43, 0, x_45);
x_46 = x_43;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_45);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_46);
x_47 = x_36;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_46);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
x_56 = lean_ctor_get(x_34, 0);
x_63 = !lean_is_exclusive(x_34);
if (x_63 == 0)
{
x_57 = x_34;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_34);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_73; 
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_13);
x_66 = lean_ctor_get(x_23, 0);
x_73 = !lean_is_exclusive(x_23);
if (x_73 == 0)
{
x_67 = x_23;
x_68 = x_73;
goto block_72;
}
else
{
lean_inc(x_66);
lean_dec(x_23);
x_67 = lean_box(0);
x_68 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_69; 
if (x_68 == 0)
{
x_69 = x_67;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_66);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_15; 
lean_inc_ref(x_1);
x_15 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_417; 
x_16 = lean_ctor_get(x_15, 0);
x_417 = !lean_is_exclusive(x_15);
if (x_417 == 0)
{
x_17 = x_15;
x_18 = x_417;
goto block_416;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_417;
goto block_416;
}
block_416:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_Expr_cleanupAnnotations(x_16);
x_20 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2));
x_21 = l_Lean_Expr_isConstOf(x_19, x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_del_object(x_17);
x_22 = l_Lean_Expr_isApp(x_19);
if (x_22 == 0)
{
lean_dec_ref(x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
goto block_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_23);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_25 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5));
x_26 = l_Lean_Expr_isConstOf(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7));
x_28 = l_Lean_Expr_isConstOf(x_24, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9));
x_30 = l_Lean_Expr_isConstOf(x_24, x_29);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = l_Lean_Expr_isApp(x_24);
if (x_31 == 0)
{
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
goto block_14;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_32);
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_34 = l_Lean_Expr_isApp(x_33);
if (x_34 == 0)
{
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
goto block_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc_ref(x_35);
x_36 = l_Lean_Expr_appFnCleanup___redArg(x_33);
x_37 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12));
x_38 = l_Lean_Expr_isConstOf(x_36, x_37);
if (x_38 == 0)
{
uint8_t x_39; 
lean_dec_ref(x_1);
x_39 = l_Lean_Expr_isApp(x_36);
if (x_39 == 0)
{
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
goto block_14;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Expr_appFnCleanup___redArg(x_36);
x_41 = l_Lean_Expr_isApp(x_40);
if (x_41 == 0)
{
lean_dec_ref(x_40);
lean_dec_ref(x_35);
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
goto block_14;
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Lean_Expr_appFnCleanup___redArg(x_40);
x_43 = l_Lean_Expr_isApp(x_42);
if (x_43 == 0)
{
lean_dec_ref(x_42);
lean_dec_ref(x_35);
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
goto block_14;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = l_Lean_Expr_appFnCleanup___redArg(x_42);
x_45 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15));
x_46 = l_Lean_Expr_isConstOf(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18));
x_48 = l_Lean_Expr_isConstOf(x_44, x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21));
x_50 = l_Lean_Expr_isConstOf(x_44, x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24));
x_52 = l_Lean_Expr_isConstOf(x_44, x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27));
x_54 = l_Lean_Expr_isConstOf(x_44, x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30));
x_56 = l_Lean_Expr_isConstOf(x_44, x_55);
lean_dec_ref(x_44);
if (x_56 == 0)
{
lean_dec_ref(x_35);
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
goto block_14;
}
else
{
lean_object* x_57; 
x_57 = l_Lean_Meta_Structural_isInstHAddNat___redArg(x_35, x_8);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_89; 
x_58 = lean_ctor_get(x_57, 0);
x_89 = !lean_is_exclusive(x_57);
if (x_89 == 0)
{
x_59 = x_57;
x_60 = x_89;
goto block_88;
}
else
{
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_box(0);
x_60 = x_89;
goto block_88;
}
block_88:
{
uint8_t x_61; 
x_61 = lean_unbox(x_58);
lean_dec(x_58);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_62 = lean_box(0);
if (x_60 == 0)
{
lean_ctor_set(x_59, 0, x_62);
x_63 = x_59;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_62);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
else
{
lean_object* x_66; 
lean_del_object(x_59);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_66 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_66;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec_ref(x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_dec(x_68);
return x_69;
}
else
{
lean_object* x_71; uint8_t x_72; uint8_t x_86; 
x_86 = !lean_is_exclusive(x_69);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_69, 0);
lean_dec(x_87);
x_71 = x_69;
x_72 = x_86;
goto block_85;
}
else
{
lean_dec(x_69);
x_71 = lean_box(0);
x_72 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_84; 
x_73 = lean_ctor_get(x_70, 0);
x_84 = !lean_is_exclusive(x_70);
if (x_84 == 0)
{
x_74 = x_70;
x_75 = x_84;
goto block_83;
}
else
{
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_box(0);
x_75 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_nat_add(x_68, x_73);
lean_dec(x_73);
lean_dec(x_68);
if (x_75 == 0)
{
lean_ctor_set(x_74, 0, x_76);
x_77 = x_74;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_76);
x_77 = x_82;
goto block_81;
}
block_81:
{
lean_object* x_78; 
if (x_72 == 0)
{
lean_ctor_set(x_71, 0, x_77);
x_78 = x_71;
goto block_79;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_77);
x_78 = x_80;
goto block_79;
}
block_79:
{
return x_78;
}
}
}
}
}
}
else
{
lean_dec(x_68);
return x_69;
}
}
}
else
{
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_66;
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_97; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_90 = lean_ctor_get(x_57, 0);
x_97 = !lean_is_exclusive(x_57);
if (x_97 == 0)
{
x_91 = x_57;
x_92 = x_97;
goto block_96;
}
else
{
lean_inc(x_90);
lean_dec(x_57);
x_91 = lean_box(0);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_92 == 0)
{
x_93 = x_91;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_90);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
}
}
else
{
lean_object* x_98; 
lean_dec_ref(x_44);
x_98 = l_Lean_Meta_Structural_isInstHMulNat___redArg(x_35, x_8);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_130; 
x_99 = lean_ctor_get(x_98, 0);
x_130 = !lean_is_exclusive(x_98);
if (x_130 == 0)
{
x_100 = x_98;
x_101 = x_130;
goto block_129;
}
else
{
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_box(0);
x_101 = x_130;
goto block_129;
}
block_129:
{
uint8_t x_102; 
x_102 = lean_unbox(x_99);
lean_dec(x_99);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_103 = lean_box(0);
if (x_101 == 0)
{
lean_ctor_set(x_100, 0, x_103);
x_104 = x_100;
goto block_105;
}
else
{
lean_object* x_106; 
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_103);
x_104 = x_106;
goto block_105;
}
block_105:
{
return x_104;
}
}
else
{
lean_object* x_107; 
lean_del_object(x_100);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_107 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_107;
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec_ref(x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
x_110 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
lean_dec(x_109);
return x_110;
}
else
{
lean_object* x_112; uint8_t x_113; uint8_t x_127; 
x_127 = !lean_is_exclusive(x_110);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_110, 0);
lean_dec(x_128);
x_112 = x_110;
x_113 = x_127;
goto block_126;
}
else
{
lean_dec(x_110);
x_112 = lean_box(0);
x_113 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_125; 
x_114 = lean_ctor_get(x_111, 0);
x_125 = !lean_is_exclusive(x_111);
if (x_125 == 0)
{
x_115 = x_111;
x_116 = x_125;
goto block_124;
}
else
{
lean_inc(x_114);
lean_dec(x_111);
x_115 = lean_box(0);
x_116 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_nat_mul(x_109, x_114);
lean_dec(x_114);
lean_dec(x_109);
if (x_116 == 0)
{
lean_ctor_set(x_115, 0, x_117);
x_118 = x_115;
goto block_122;
}
else
{
lean_object* x_123; 
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_117);
x_118 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_119; 
if (x_113 == 0)
{
lean_ctor_set(x_112, 0, x_118);
x_119 = x_112;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_118);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
}
}
}
}
}
else
{
lean_dec(x_109);
return x_110;
}
}
}
else
{
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_107;
}
}
}
}
else
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; uint8_t x_138; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_131 = lean_ctor_get(x_98, 0);
x_138 = !lean_is_exclusive(x_98);
if (x_138 == 0)
{
x_132 = x_98;
x_133 = x_138;
goto block_137;
}
else
{
lean_inc(x_131);
lean_dec(x_98);
x_132 = lean_box(0);
x_133 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_134; 
if (x_133 == 0)
{
x_134 = x_132;
goto block_135;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_131);
x_134 = x_136;
goto block_135;
}
block_135:
{
return x_134;
}
}
}
}
}
else
{
lean_object* x_139; 
lean_dec_ref(x_44);
x_139 = l_Lean_Meta_Structural_isInstHSubNat___redArg(x_35, x_8);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; uint8_t x_171; 
x_140 = lean_ctor_get(x_139, 0);
x_171 = !lean_is_exclusive(x_139);
if (x_171 == 0)
{
x_141 = x_139;
x_142 = x_171;
goto block_170;
}
else
{
lean_inc(x_140);
lean_dec(x_139);
x_141 = lean_box(0);
x_142 = x_171;
goto block_170;
}
block_170:
{
uint8_t x_143; 
x_143 = lean_unbox(x_140);
lean_dec(x_140);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_144 = lean_box(0);
if (x_142 == 0)
{
lean_ctor_set(x_141, 0, x_144);
x_145 = x_141;
goto block_146;
}
else
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_147, 0, x_144);
x_145 = x_147;
goto block_146;
}
block_146:
{
return x_145;
}
}
else
{
lean_object* x_148; 
lean_del_object(x_141);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_148 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_obj_tag(x_149) == 0)
{
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_148;
}
else
{
lean_object* x_150; lean_object* x_151; 
lean_dec_ref(x_148);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec_ref(x_149);
x_151 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
if (lean_obj_tag(x_152) == 0)
{
lean_dec(x_150);
return x_151;
}
else
{
lean_object* x_153; uint8_t x_154; uint8_t x_168; 
x_168 = !lean_is_exclusive(x_151);
if (x_168 == 0)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_151, 0);
lean_dec(x_169);
x_153 = x_151;
x_154 = x_168;
goto block_167;
}
else
{
lean_dec(x_151);
x_153 = lean_box(0);
x_154 = x_168;
goto block_167;
}
block_167:
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; uint8_t x_166; 
x_155 = lean_ctor_get(x_152, 0);
x_166 = !lean_is_exclusive(x_152);
if (x_166 == 0)
{
x_156 = x_152;
x_157 = x_166;
goto block_165;
}
else
{
lean_inc(x_155);
lean_dec(x_152);
x_156 = lean_box(0);
x_157 = x_166;
goto block_165;
}
block_165:
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_nat_sub(x_150, x_155);
lean_dec(x_155);
lean_dec(x_150);
if (x_157 == 0)
{
lean_ctor_set(x_156, 0, x_158);
x_159 = x_156;
goto block_163;
}
else
{
lean_object* x_164; 
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_158);
x_159 = x_164;
goto block_163;
}
block_163:
{
lean_object* x_160; 
if (x_154 == 0)
{
lean_ctor_set(x_153, 0, x_159);
x_160 = x_153;
goto block_161;
}
else
{
lean_object* x_162; 
x_162 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_162, 0, x_159);
x_160 = x_162;
goto block_161;
}
block_161:
{
return x_160;
}
}
}
}
}
}
else
{
lean_dec(x_150);
return x_151;
}
}
}
else
{
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_148;
}
}
}
}
else
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; uint8_t x_179; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_172 = lean_ctor_get(x_139, 0);
x_179 = !lean_is_exclusive(x_139);
if (x_179 == 0)
{
x_173 = x_139;
x_174 = x_179;
goto block_178;
}
else
{
lean_inc(x_172);
lean_dec(x_139);
x_173 = lean_box(0);
x_174 = x_179;
goto block_178;
}
block_178:
{
lean_object* x_175; 
if (x_174 == 0)
{
x_175 = x_173;
goto block_176;
}
else
{
lean_object* x_177; 
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_172);
x_175 = x_177;
goto block_176;
}
block_176:
{
return x_175;
}
}
}
}
}
else
{
lean_object* x_180; 
lean_dec_ref(x_44);
x_180 = l_Lean_Meta_Structural_isInstHDivNat___redArg(x_35, x_8);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; uint8_t x_212; 
x_181 = lean_ctor_get(x_180, 0);
x_212 = !lean_is_exclusive(x_180);
if (x_212 == 0)
{
x_182 = x_180;
x_183 = x_212;
goto block_211;
}
else
{
lean_inc(x_181);
lean_dec(x_180);
x_182 = lean_box(0);
x_183 = x_212;
goto block_211;
}
block_211:
{
uint8_t x_184; 
x_184 = lean_unbox(x_181);
lean_dec(x_181);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_185 = lean_box(0);
if (x_183 == 0)
{
lean_ctor_set(x_182, 0, x_185);
x_186 = x_182;
goto block_187;
}
else
{
lean_object* x_188; 
x_188 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_188, 0, x_185);
x_186 = x_188;
goto block_187;
}
block_187:
{
return x_186;
}
}
else
{
lean_object* x_189; 
lean_del_object(x_182);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_189 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
if (lean_obj_tag(x_190) == 0)
{
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_189;
}
else
{
lean_object* x_191; lean_object* x_192; 
lean_dec_ref(x_189);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec_ref(x_190);
x_192 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 0)
{
lean_dec(x_191);
return x_192;
}
else
{
lean_object* x_194; uint8_t x_195; uint8_t x_209; 
x_209 = !lean_is_exclusive(x_192);
if (x_209 == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_192, 0);
lean_dec(x_210);
x_194 = x_192;
x_195 = x_209;
goto block_208;
}
else
{
lean_dec(x_192);
x_194 = lean_box(0);
x_195 = x_209;
goto block_208;
}
block_208:
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; uint8_t x_207; 
x_196 = lean_ctor_get(x_193, 0);
x_207 = !lean_is_exclusive(x_193);
if (x_207 == 0)
{
x_197 = x_193;
x_198 = x_207;
goto block_206;
}
else
{
lean_inc(x_196);
lean_dec(x_193);
x_197 = lean_box(0);
x_198 = x_207;
goto block_206;
}
block_206:
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_nat_div(x_191, x_196);
lean_dec(x_196);
lean_dec(x_191);
if (x_198 == 0)
{
lean_ctor_set(x_197, 0, x_199);
x_200 = x_197;
goto block_204;
}
else
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_199);
x_200 = x_205;
goto block_204;
}
block_204:
{
lean_object* x_201; 
if (x_195 == 0)
{
lean_ctor_set(x_194, 0, x_200);
x_201 = x_194;
goto block_202;
}
else
{
lean_object* x_203; 
x_203 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_203, 0, x_200);
x_201 = x_203;
goto block_202;
}
block_202:
{
return x_201;
}
}
}
}
}
}
else
{
lean_dec(x_191);
return x_192;
}
}
}
else
{
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_189;
}
}
}
}
else
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; uint8_t x_220; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_213 = lean_ctor_get(x_180, 0);
x_220 = !lean_is_exclusive(x_180);
if (x_220 == 0)
{
x_214 = x_180;
x_215 = x_220;
goto block_219;
}
else
{
lean_inc(x_213);
lean_dec(x_180);
x_214 = lean_box(0);
x_215 = x_220;
goto block_219;
}
block_219:
{
lean_object* x_216; 
if (x_215 == 0)
{
x_216 = x_214;
goto block_217;
}
else
{
lean_object* x_218; 
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_213);
x_216 = x_218;
goto block_217;
}
block_217:
{
return x_216;
}
}
}
}
}
else
{
lean_object* x_221; 
lean_dec_ref(x_44);
x_221 = l_Lean_Meta_Structural_isInstHModNat___redArg(x_35, x_8);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; uint8_t x_253; 
x_222 = lean_ctor_get(x_221, 0);
x_253 = !lean_is_exclusive(x_221);
if (x_253 == 0)
{
x_223 = x_221;
x_224 = x_253;
goto block_252;
}
else
{
lean_inc(x_222);
lean_dec(x_221);
x_223 = lean_box(0);
x_224 = x_253;
goto block_252;
}
block_252:
{
uint8_t x_225; 
x_225 = lean_unbox(x_222);
lean_dec(x_222);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_226 = lean_box(0);
if (x_224 == 0)
{
lean_ctor_set(x_223, 0, x_226);
x_227 = x_223;
goto block_228;
}
else
{
lean_object* x_229; 
x_229 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_229, 0, x_226);
x_227 = x_229;
goto block_228;
}
block_228:
{
return x_227;
}
}
else
{
lean_object* x_230; 
lean_del_object(x_223);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_230 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
if (lean_obj_tag(x_231) == 0)
{
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_230;
}
else
{
lean_object* x_232; lean_object* x_233; 
lean_dec_ref(x_230);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
lean_dec_ref(x_231);
x_233 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
if (lean_obj_tag(x_234) == 0)
{
lean_dec(x_232);
return x_233;
}
else
{
lean_object* x_235; uint8_t x_236; uint8_t x_250; 
x_250 = !lean_is_exclusive(x_233);
if (x_250 == 0)
{
lean_object* x_251; 
x_251 = lean_ctor_get(x_233, 0);
lean_dec(x_251);
x_235 = x_233;
x_236 = x_250;
goto block_249;
}
else
{
lean_dec(x_233);
x_235 = lean_box(0);
x_236 = x_250;
goto block_249;
}
block_249:
{
lean_object* x_237; lean_object* x_238; uint8_t x_239; uint8_t x_248; 
x_237 = lean_ctor_get(x_234, 0);
x_248 = !lean_is_exclusive(x_234);
if (x_248 == 0)
{
x_238 = x_234;
x_239 = x_248;
goto block_247;
}
else
{
lean_inc(x_237);
lean_dec(x_234);
x_238 = lean_box(0);
x_239 = x_248;
goto block_247;
}
block_247:
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_nat_mod(x_232, x_237);
lean_dec(x_237);
lean_dec(x_232);
if (x_239 == 0)
{
lean_ctor_set(x_238, 0, x_240);
x_241 = x_238;
goto block_245;
}
else
{
lean_object* x_246; 
x_246 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_246, 0, x_240);
x_241 = x_246;
goto block_245;
}
block_245:
{
lean_object* x_242; 
if (x_236 == 0)
{
lean_ctor_set(x_235, 0, x_241);
x_242 = x_235;
goto block_243;
}
else
{
lean_object* x_244; 
x_244 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_244, 0, x_241);
x_242 = x_244;
goto block_243;
}
block_243:
{
return x_242;
}
}
}
}
}
}
else
{
lean_dec(x_232);
return x_233;
}
}
}
else
{
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_230;
}
}
}
}
else
{
lean_object* x_254; lean_object* x_255; uint8_t x_256; uint8_t x_261; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_254 = lean_ctor_get(x_221, 0);
x_261 = !lean_is_exclusive(x_221);
if (x_261 == 0)
{
x_255 = x_221;
x_256 = x_261;
goto block_260;
}
else
{
lean_inc(x_254);
lean_dec(x_221);
x_255 = lean_box(0);
x_256 = x_261;
goto block_260;
}
block_260:
{
lean_object* x_257; 
if (x_256 == 0)
{
x_257 = x_255;
goto block_258;
}
else
{
lean_object* x_259; 
x_259 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_259, 0, x_254);
x_257 = x_259;
goto block_258;
}
block_258:
{
return x_257;
}
}
}
}
}
else
{
lean_object* x_262; 
lean_dec_ref(x_44);
x_262 = l_Lean_Meta_Structural_isInstHPowNat___redArg(x_35, x_8);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; uint8_t x_312; 
x_263 = lean_ctor_get(x_262, 0);
x_312 = !lean_is_exclusive(x_262);
if (x_312 == 0)
{
x_264 = x_262;
x_265 = x_312;
goto block_311;
}
else
{
lean_inc(x_263);
lean_dec(x_262);
x_264 = lean_box(0);
x_265 = x_312;
goto block_311;
}
block_311:
{
uint8_t x_266; 
x_266 = lean_unbox(x_263);
lean_dec(x_263);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_267 = lean_box(0);
if (x_265 == 0)
{
lean_ctor_set(x_264, 0, x_267);
x_268 = x_264;
goto block_269;
}
else
{
lean_object* x_270; 
x_270 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_270, 0, x_267);
x_268 = x_270;
goto block_269;
}
block_269:
{
return x_268;
}
}
else
{
lean_object* x_271; 
lean_del_object(x_264);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_271 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
if (lean_obj_tag(x_272) == 0)
{
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_271;
}
else
{
lean_object* x_273; lean_object* x_274; 
lean_dec_ref(x_271);
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
lean_dec_ref(x_272);
lean_inc(x_273);
x_274 = l_Lean_Meta_Grind_Arith_checkExp(x_273, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; uint8_t x_277; uint8_t x_302; 
x_275 = lean_ctor_get(x_274, 0);
x_302 = !lean_is_exclusive(x_274);
if (x_302 == 0)
{
x_276 = x_274;
x_277 = x_302;
goto block_301;
}
else
{
lean_inc(x_275);
lean_dec(x_274);
x_276 = lean_box(0);
x_277 = x_302;
goto block_301;
}
block_301:
{
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_278; lean_object* x_279; 
lean_dec(x_273);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_278 = lean_box(0);
if (x_277 == 0)
{
lean_ctor_set(x_276, 0, x_278);
x_279 = x_276;
goto block_280;
}
else
{
lean_object* x_281; 
x_281 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_281, 0, x_278);
x_279 = x_281;
goto block_280;
}
block_280:
{
return x_279;
}
}
else
{
lean_object* x_282; 
lean_dec_ref(x_275);
lean_del_object(x_276);
x_282 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
if (lean_obj_tag(x_283) == 0)
{
lean_dec(x_273);
return x_282;
}
else
{
lean_object* x_284; uint8_t x_285; uint8_t x_299; 
x_299 = !lean_is_exclusive(x_282);
if (x_299 == 0)
{
lean_object* x_300; 
x_300 = lean_ctor_get(x_282, 0);
lean_dec(x_300);
x_284 = x_282;
x_285 = x_299;
goto block_298;
}
else
{
lean_dec(x_282);
x_284 = lean_box(0);
x_285 = x_299;
goto block_298;
}
block_298:
{
lean_object* x_286; lean_object* x_287; uint8_t x_288; uint8_t x_297; 
x_286 = lean_ctor_get(x_283, 0);
x_297 = !lean_is_exclusive(x_283);
if (x_297 == 0)
{
x_287 = x_283;
x_288 = x_297;
goto block_296;
}
else
{
lean_inc(x_286);
lean_dec(x_283);
x_287 = lean_box(0);
x_288 = x_297;
goto block_296;
}
block_296:
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_nat_pow(x_286, x_273);
lean_dec(x_273);
lean_dec(x_286);
if (x_288 == 0)
{
lean_ctor_set(x_287, 0, x_289);
x_290 = x_287;
goto block_294;
}
else
{
lean_object* x_295; 
x_295 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_295, 0, x_289);
x_290 = x_295;
goto block_294;
}
block_294:
{
lean_object* x_291; 
if (x_285 == 0)
{
lean_ctor_set(x_284, 0, x_290);
x_291 = x_284;
goto block_292;
}
else
{
lean_object* x_293; 
x_293 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_293, 0, x_290);
x_291 = x_293;
goto block_292;
}
block_292:
{
return x_291;
}
}
}
}
}
}
else
{
lean_dec(x_273);
return x_282;
}
}
}
}
else
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; uint8_t x_310; 
lean_dec(x_273);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_303 = lean_ctor_get(x_274, 0);
x_310 = !lean_is_exclusive(x_274);
if (x_310 == 0)
{
x_304 = x_274;
x_305 = x_310;
goto block_309;
}
else
{
lean_inc(x_303);
lean_dec(x_274);
x_304 = lean_box(0);
x_305 = x_310;
goto block_309;
}
block_309:
{
lean_object* x_306; 
if (x_305 == 0)
{
x_306 = x_304;
goto block_307;
}
else
{
lean_object* x_308; 
x_308 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_308, 0, x_303);
x_306 = x_308;
goto block_307;
}
block_307:
{
return x_306;
}
}
}
}
}
else
{
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_271;
}
}
}
}
else
{
lean_object* x_313; lean_object* x_314; uint8_t x_315; uint8_t x_320; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_313 = lean_ctor_get(x_262, 0);
x_320 = !lean_is_exclusive(x_262);
if (x_320 == 0)
{
x_314 = x_262;
x_315 = x_320;
goto block_319;
}
else
{
lean_inc(x_313);
lean_dec(x_262);
x_314 = lean_box(0);
x_315 = x_320;
goto block_319;
}
block_319:
{
lean_object* x_316; 
if (x_315 == 0)
{
x_316 = x_314;
goto block_317;
}
else
{
lean_object* x_318; 
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_313);
x_316 = x_318;
goto block_317;
}
block_317:
{
return x_316;
}
}
}
}
}
}
}
}
else
{
lean_object* x_321; 
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_32);
lean_dec_ref(x_23);
x_321 = l_Lean_Meta_getNatValue_x3f(x_1, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
if (lean_obj_tag(x_322) == 1)
{
lean_dec_ref(x_322);
return x_321;
}
else
{
lean_object* x_323; uint8_t x_324; uint8_t x_330; 
lean_dec(x_322);
x_330 = !lean_is_exclusive(x_321);
if (x_330 == 0)
{
lean_object* x_331; 
x_331 = lean_ctor_get(x_321, 0);
lean_dec(x_331);
x_323 = x_321;
x_324 = x_330;
goto block_329;
}
else
{
lean_dec(x_321);
x_323 = lean_box(0);
x_324 = x_330;
goto block_329;
}
block_329:
{
lean_object* x_325; lean_object* x_326; 
x_325 = lean_box(0);
if (x_324 == 0)
{
lean_ctor_set(x_323, 0, x_325);
x_326 = x_323;
goto block_327;
}
else
{
lean_object* x_328; 
x_328 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_328, 0, x_325);
x_326 = x_328;
goto block_327;
}
block_327:
{
return x_326;
}
}
}
}
else
{
return x_321;
}
}
}
}
}
else
{
lean_object* x_332; 
lean_dec_ref(x_24);
lean_dec_ref(x_1);
x_332 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
if (lean_obj_tag(x_333) == 0)
{
return x_332;
}
else
{
lean_object* x_334; uint8_t x_335; uint8_t x_350; 
x_350 = !lean_is_exclusive(x_332);
if (x_350 == 0)
{
lean_object* x_351; 
x_351 = lean_ctor_get(x_332, 0);
lean_dec(x_351);
x_334 = x_332;
x_335 = x_350;
goto block_349;
}
else
{
lean_dec(x_332);
x_334 = lean_box(0);
x_335 = x_350;
goto block_349;
}
block_349:
{
lean_object* x_336; lean_object* x_337; uint8_t x_338; uint8_t x_348; 
x_336 = lean_ctor_get(x_333, 0);
x_348 = !lean_is_exclusive(x_333);
if (x_348 == 0)
{
x_337 = x_333;
x_338 = x_348;
goto block_347;
}
else
{
lean_inc(x_336);
lean_dec(x_333);
x_337 = lean_box(0);
x_338 = x_348;
goto block_347;
}
block_347:
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_unsigned_to_nat(1u);
x_340 = lean_nat_add(x_336, x_339);
lean_dec(x_336);
if (x_338 == 0)
{
lean_ctor_set(x_337, 0, x_340);
x_341 = x_337;
goto block_345;
}
else
{
lean_object* x_346; 
x_346 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_346, 0, x_340);
x_341 = x_346;
goto block_345;
}
block_345:
{
lean_object* x_342; 
if (x_335 == 0)
{
lean_ctor_set(x_334, 0, x_341);
x_342 = x_334;
goto block_343;
}
else
{
lean_object* x_344; 
x_344 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_344, 0, x_341);
x_342 = x_344;
goto block_343;
}
block_343:
{
return x_342;
}
}
}
}
}
}
else
{
return x_332;
}
}
}
else
{
lean_object* x_352; 
lean_dec_ref(x_24);
lean_dec_ref(x_1);
x_352 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; uint8_t x_355; uint8_t x_373; 
x_353 = lean_ctor_get(x_352, 0);
x_373 = !lean_is_exclusive(x_352);
if (x_373 == 0)
{
x_354 = x_352;
x_355 = x_373;
goto block_372;
}
else
{
lean_inc(x_353);
lean_dec(x_352);
x_354 = lean_box(0);
x_355 = x_373;
goto block_372;
}
block_372:
{
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_box(0);
if (x_355 == 0)
{
lean_ctor_set(x_354, 0, x_356);
x_357 = x_354;
goto block_358;
}
else
{
lean_object* x_359; 
x_359 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_359, 0, x_356);
x_357 = x_359;
goto block_358;
}
block_358:
{
return x_357;
}
}
else
{
lean_object* x_360; lean_object* x_361; uint8_t x_362; uint8_t x_371; 
x_360 = lean_ctor_get(x_353, 0);
x_371 = !lean_is_exclusive(x_353);
if (x_371 == 0)
{
x_361 = x_353;
x_362 = x_371;
goto block_370;
}
else
{
lean_inc(x_360);
lean_dec(x_353);
x_361 = lean_box(0);
x_362 = x_371;
goto block_370;
}
block_370:
{
lean_object* x_363; lean_object* x_364; 
x_363 = l_Int_toNat(x_360);
lean_dec(x_360);
if (x_362 == 0)
{
lean_ctor_set(x_361, 0, x_363);
x_364 = x_361;
goto block_368;
}
else
{
lean_object* x_369; 
x_369 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_369, 0, x_363);
x_364 = x_369;
goto block_368;
}
block_368:
{
lean_object* x_365; 
if (x_355 == 0)
{
lean_ctor_set(x_354, 0, x_364);
x_365 = x_354;
goto block_366;
}
else
{
lean_object* x_367; 
x_367 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_367, 0, x_364);
x_365 = x_367;
goto block_366;
}
block_366:
{
return x_365;
}
}
}
}
}
}
else
{
lean_object* x_374; lean_object* x_375; uint8_t x_376; uint8_t x_381; 
x_374 = lean_ctor_get(x_352, 0);
x_381 = !lean_is_exclusive(x_352);
if (x_381 == 0)
{
x_375 = x_352;
x_376 = x_381;
goto block_380;
}
else
{
lean_inc(x_374);
lean_dec(x_352);
x_375 = lean_box(0);
x_376 = x_381;
goto block_380;
}
block_380:
{
lean_object* x_377; 
if (x_376 == 0)
{
x_377 = x_375;
goto block_378;
}
else
{
lean_object* x_379; 
x_379 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_379, 0, x_374);
x_377 = x_379;
goto block_378;
}
block_378:
{
return x_377;
}
}
}
}
}
else
{
lean_object* x_382; 
lean_dec_ref(x_24);
lean_dec_ref(x_1);
x_382 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; uint8_t x_385; uint8_t x_403; 
x_383 = lean_ctor_get(x_382, 0);
x_403 = !lean_is_exclusive(x_382);
if (x_403 == 0)
{
x_384 = x_382;
x_385 = x_403;
goto block_402;
}
else
{
lean_inc(x_383);
lean_dec(x_382);
x_384 = lean_box(0);
x_385 = x_403;
goto block_402;
}
block_402:
{
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_386; lean_object* x_387; 
x_386 = lean_box(0);
if (x_385 == 0)
{
lean_ctor_set(x_384, 0, x_386);
x_387 = x_384;
goto block_388;
}
else
{
lean_object* x_389; 
x_389 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_389, 0, x_386);
x_387 = x_389;
goto block_388;
}
block_388:
{
return x_387;
}
}
else
{
lean_object* x_390; lean_object* x_391; uint8_t x_392; uint8_t x_401; 
x_390 = lean_ctor_get(x_383, 0);
x_401 = !lean_is_exclusive(x_383);
if (x_401 == 0)
{
x_391 = x_383;
x_392 = x_401;
goto block_400;
}
else
{
lean_inc(x_390);
lean_dec(x_383);
x_391 = lean_box(0);
x_392 = x_401;
goto block_400;
}
block_400:
{
lean_object* x_393; lean_object* x_394; 
x_393 = lean_nat_abs(x_390);
lean_dec(x_390);
if (x_392 == 0)
{
lean_ctor_set(x_391, 0, x_393);
x_394 = x_391;
goto block_398;
}
else
{
lean_object* x_399; 
x_399 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_399, 0, x_393);
x_394 = x_399;
goto block_398;
}
block_398:
{
lean_object* x_395; 
if (x_385 == 0)
{
lean_ctor_set(x_384, 0, x_394);
x_395 = x_384;
goto block_396;
}
else
{
lean_object* x_397; 
x_397 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_397, 0, x_394);
x_395 = x_397;
goto block_396;
}
block_396:
{
return x_395;
}
}
}
}
}
}
else
{
lean_object* x_404; lean_object* x_405; uint8_t x_406; uint8_t x_411; 
x_404 = lean_ctor_get(x_382, 0);
x_411 = !lean_is_exclusive(x_382);
if (x_411 == 0)
{
x_405 = x_382;
x_406 = x_411;
goto block_410;
}
else
{
lean_inc(x_404);
lean_dec(x_382);
x_405 = lean_box(0);
x_406 = x_411;
goto block_410;
}
block_410:
{
lean_object* x_407; 
if (x_406 == 0)
{
x_407 = x_405;
goto block_408;
}
else
{
lean_object* x_409; 
x_409 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_409, 0, x_404);
x_407 = x_409;
goto block_408;
}
block_408:
{
return x_407;
}
}
}
}
}
}
else
{
lean_object* x_412; lean_object* x_413; 
lean_dec_ref(x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_412 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31));
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_412);
x_413 = x_17;
goto block_414;
}
else
{
lean_object* x_415; 
x_415 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_415, 0, x_412);
x_413 = x_415;
goto block_414;
}
block_414:
{
return x_413;
}
}
}
}
else
{
lean_object* x_418; lean_object* x_419; uint8_t x_420; uint8_t x_425; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_418 = lean_ctor_get(x_15, 0);
x_425 = !lean_is_exclusive(x_15);
if (x_425 == 0)
{
x_419 = x_15;
x_420 = x_425;
goto block_424;
}
else
{
lean_inc(x_418);
lean_dec(x_15);
x_419 = lean_box(0);
x_420 = x_425;
goto block_424;
}
block_424:
{
lean_object* x_421; 
if (x_420 == 0)
{
x_421 = x_419;
goto block_422;
}
else
{
lean_object* x_423; 
x_423 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_423, 0, x_418);
x_421 = x_423;
goto block_422;
}
block_422:
{
return x_421;
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalNat_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalNat_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_evalNat_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalInt_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalInt_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_evalInt_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_IntInstTesters(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatInstTesters(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IntInstTesters(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
}
#ifdef __cplusplus
}
#endif

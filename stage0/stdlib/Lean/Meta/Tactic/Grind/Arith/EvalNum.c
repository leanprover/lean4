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
static lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__2;
static const lean_string_object l_Lean_Meta_Grind_Arith_checkExp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = " exceeds threshold for exponentiation `(exp := "};
static const lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_checkExp___closed__3_value;
static lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__4;
static const lean_string_object l_Lean_Meta_Grind_Arith_checkExp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ")`"};
static const lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_checkExp___closed__5_value;
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_checkExp___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Arith_checkExp___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___closed__6() {
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
lean_object* x_12; lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Meta_Grind_Arith_checkExp___lam__0(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 7);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_nat_dec_lt(x_22, x_1);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_1);
x_24 = ((lean_object*)(l_Lean_Meta_Grind_Arith_checkExp___closed__0));
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
lean_object* x_25; 
lean_free_object(x_18);
x_25 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l_Lean_Meta_Grind_Arith_checkExp___lam__0(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*11 + 14);
lean_dec(x_31);
if (x_32 == 0)
{
lean_free_object(x_29);
lean_free_object(x_27);
lean_dec(x_1);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_33; 
x_33 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_ctor_get(x_34, 7);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Meta_Grind_Arith_checkExp___closed__2;
x_37 = l_Nat_reprFast(x_1);
lean_ctor_set_tag(x_29, 3);
lean_ctor_set(x_29, 0, x_37);
x_38 = l_Lean_MessageData_ofFormat(x_29);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Meta_Grind_Arith_checkExp___closed__4;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Nat_reprFast(x_35);
lean_ctor_set_tag(x_27, 3);
lean_ctor_set(x_27, 0, x_42);
x_43 = l_Lean_MessageData_ofFormat(x_27);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Meta_Grind_Arith_checkExp___closed__6;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Meta_Grind_reportIssue(x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_47) == 0)
{
lean_dec_ref(x_47);
x_12 = lean_box(0);
goto block_15;
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_free_object(x_29);
lean_free_object(x_27);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_33);
if (x_51 == 0)
{
return x_33;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_33, 0);
lean_inc(x_52);
lean_dec(x_33);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_29, 0);
lean_inc(x_54);
lean_dec(x_29);
x_55 = lean_ctor_get_uint8(x_54, sizeof(void*)*11 + 14);
lean_dec(x_54);
if (x_55 == 0)
{
lean_free_object(x_27);
lean_dec(x_1);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_56; 
x_56 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_ctor_get(x_57, 7);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_Lean_Meta_Grind_Arith_checkExp___closed__2;
x_60 = l_Nat_reprFast(x_1);
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l_Lean_MessageData_ofFormat(x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_Meta_Grind_Arith_checkExp___closed__4;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Nat_reprFast(x_58);
lean_ctor_set_tag(x_27, 3);
lean_ctor_set(x_27, 0, x_66);
x_67 = l_Lean_MessageData_ofFormat(x_27);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_Meta_Grind_Arith_checkExp___closed__6;
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Meta_Grind_reportIssue(x_70, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_71) == 0)
{
lean_dec_ref(x_71);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_free_object(x_27);
lean_dec(x_1);
x_75 = lean_ctor_get(x_56, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_76 = x_56;
} else {
 lean_dec_ref(x_56);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_78 = lean_ctor_get(x_27, 0);
lean_inc(x_78);
lean_dec(x_27);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get_uint8(x_79, sizeof(void*)*11 + 14);
lean_dec(x_79);
if (x_81 == 0)
{
lean_dec(x_80);
lean_dec(x_1);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_82; 
x_82 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = lean_ctor_get(x_83, 7);
lean_inc(x_84);
lean_dec(x_83);
x_85 = l_Lean_Meta_Grind_Arith_checkExp___closed__2;
x_86 = l_Nat_reprFast(x_1);
if (lean_is_scalar(x_80)) {
 x_87 = lean_alloc_ctor(3, 1, 0);
} else {
 x_87 = x_80;
 lean_ctor_set_tag(x_87, 3);
}
lean_ctor_set(x_87, 0, x_86);
x_88 = l_Lean_MessageData_ofFormat(x_87);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Meta_Grind_Arith_checkExp___closed__4;
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Nat_reprFast(x_84);
x_93 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = l_Lean_MessageData_ofFormat(x_93);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Meta_Grind_Arith_checkExp___closed__6;
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_Meta_Grind_reportIssue(x_97, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_98) == 0)
{
lean_dec_ref(x_98);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 1, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_99);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_80);
lean_dec(x_1);
x_102 = lean_ctor_get(x_82, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_103 = x_82;
} else {
 lean_dec_ref(x_82);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 1, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_102);
return x_104;
}
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_25);
if (x_105 == 0)
{
return x_25;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_25, 0);
lean_inc(x_106);
lean_dec(x_25);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_18, 0);
lean_inc(x_108);
lean_dec(x_18);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_ctor_get(x_109, 7);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_nat_dec_lt(x_110, x_1);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_1);
x_112 = ((lean_object*)(l_Lean_Meta_Grind_Arith_checkExp___closed__0));
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
else
{
lean_object* x_114; 
x_114 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec_ref(x_114);
x_116 = l_Lean_Meta_Grind_Arith_checkExp___lam__0(x_115, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_120 = x_117;
} else {
 lean_dec_ref(x_117);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get_uint8(x_119, sizeof(void*)*11 + 14);
lean_dec(x_119);
if (x_121 == 0)
{
lean_dec(x_120);
lean_dec(x_118);
lean_dec(x_1);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_122; 
x_122 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec_ref(x_122);
x_124 = lean_ctor_get(x_123, 7);
lean_inc(x_124);
lean_dec(x_123);
x_125 = l_Lean_Meta_Grind_Arith_checkExp___closed__2;
x_126 = l_Nat_reprFast(x_1);
if (lean_is_scalar(x_120)) {
 x_127 = lean_alloc_ctor(3, 1, 0);
} else {
 x_127 = x_120;
 lean_ctor_set_tag(x_127, 3);
}
lean_ctor_set(x_127, 0, x_126);
x_128 = l_Lean_MessageData_ofFormat(x_127);
x_129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_129, 0, x_125);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Lean_Meta_Grind_Arith_checkExp___closed__4;
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Nat_reprFast(x_124);
if (lean_is_scalar(x_118)) {
 x_133 = lean_alloc_ctor(3, 1, 0);
} else {
 x_133 = x_118;
 lean_ctor_set_tag(x_133, 3);
}
lean_ctor_set(x_133, 0, x_132);
x_134 = l_Lean_MessageData_ofFormat(x_133);
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_131);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lean_Meta_Grind_Arith_checkExp___closed__6;
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_Meta_Grind_reportIssue(x_137, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_138) == 0)
{
lean_dec_ref(x_138);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 x_140 = x_138;
} else {
 lean_dec_ref(x_138);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 1, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_139);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_120);
lean_dec(x_118);
lean_dec(x_1);
x_142 = lean_ctor_get(x_122, 0);
lean_inc(x_142);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_143 = x_122;
} else {
 lean_dec_ref(x_122);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 1, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_142);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_1);
x_145 = lean_ctor_get(x_114, 0);
lean_inc(x_145);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 x_146 = x_114;
} else {
 lean_dec_ref(x_114);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 1, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_145);
return x_147;
}
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_16);
if (x_148 == 0)
{
return x_16;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_16, 0);
lean_inc(x_149);
lean_dec(x_16);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
return x_150;
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
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
lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_55; 
lean_inc_ref(x_1);
x_55 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_8);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_61; uint8_t x_62; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_61 = l_Lean_Expr_cleanupAnnotations(x_56);
x_62 = l_Lean_Expr_isApp(x_61);
if (x_62 == 0)
{
lean_dec_ref(x_61);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
goto block_60;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc_ref(x_63);
x_64 = l_Lean_Expr_appFnCleanup___redArg(x_61);
x_65 = l_Lean_Expr_isApp(x_64);
if (x_65 == 0)
{
lean_dec_ref(x_64);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
goto block_60;
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_64, 1);
lean_inc_ref(x_66);
x_67 = l_Lean_Expr_appFnCleanup___redArg(x_64);
x_68 = l_Lean_Expr_isApp(x_67);
if (x_68 == 0)
{
lean_dec_ref(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
goto block_60;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_67, 1);
lean_inc_ref(x_69);
x_70 = l_Lean_Expr_appFnCleanup___redArg(x_67);
x_71 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3));
x_72 = l_Lean_Expr_isConstOf(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6));
x_74 = l_Lean_Expr_isConstOf(x_70, x_73);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12));
x_76 = l_Lean_Expr_isConstOf(x_70, x_75);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
lean_dec_ref(x_1);
x_77 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9));
x_78 = l_Lean_Expr_isConstOf(x_70, x_77);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_Expr_isApp(x_70);
if (x_79 == 0)
{
lean_dec_ref(x_70);
lean_dec_ref(x_69);
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
goto block_60;
}
else
{
lean_object* x_80; uint8_t x_81; 
x_80 = l_Lean_Expr_appFnCleanup___redArg(x_70);
x_81 = l_Lean_Expr_isApp(x_80);
if (x_81 == 0)
{
lean_dec_ref(x_80);
lean_dec_ref(x_69);
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
goto block_60;
}
else
{
lean_object* x_82; uint8_t x_83; 
x_82 = l_Lean_Expr_appFnCleanup___redArg(x_80);
x_83 = l_Lean_Expr_isApp(x_82);
if (x_83 == 0)
{
lean_dec_ref(x_82);
lean_dec_ref(x_69);
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
goto block_60;
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = l_Lean_Expr_appFnCleanup___redArg(x_82);
x_85 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15));
x_86 = l_Lean_Expr_isConstOf(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18));
x_88 = l_Lean_Expr_isConstOf(x_84, x_87);
if (x_88 == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21));
x_90 = l_Lean_Expr_isConstOf(x_84, x_89);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27));
x_92 = l_Lean_Expr_isConstOf(x_84, x_91);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24));
x_94 = l_Lean_Expr_isConstOf(x_84, x_93);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30));
x_96 = l_Lean_Expr_isConstOf(x_84, x_95);
lean_dec_ref(x_84);
if (x_96 == 0)
{
lean_dec_ref(x_69);
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
goto block_60;
}
else
{
lean_object* x_97; 
lean_dec(x_57);
x_97 = l_Lean_Meta_Structural_isInstHAddInt___redArg(x_69, x_8);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_unbox(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_101 = lean_box(0);
lean_ctor_set(x_97, 0, x_101);
return x_97;
}
else
{
lean_object* x_102; 
lean_free_object(x_97);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_102 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_102;
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec_ref(x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
lean_dec(x_104);
return x_105;
}
else
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_105);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_105, 0);
lean_dec(x_108);
x_109 = !lean_is_exclusive(x_106);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_106, 0);
x_111 = lean_int_add(x_104, x_110);
lean_dec(x_110);
lean_dec(x_104);
lean_ctor_set(x_106, 0, x_111);
return x_105;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_106, 0);
lean_inc(x_112);
lean_dec(x_106);
x_113 = lean_int_add(x_104, x_112);
lean_dec(x_112);
lean_dec(x_104);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_105, 0, x_114);
return x_105;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_105);
x_115 = lean_ctor_get(x_106, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 x_116 = x_106;
} else {
 lean_dec_ref(x_106);
 x_116 = lean_box(0);
}
x_117 = lean_int_add(x_104, x_115);
lean_dec(x_115);
lean_dec(x_104);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(1, 1, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
}
else
{
lean_dec(x_104);
return x_105;
}
}
}
else
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_102;
}
}
}
else
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_97, 0);
lean_inc(x_120);
lean_dec(x_97);
x_121 = lean_unbox(x_120);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
else
{
lean_object* x_124; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_124 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
if (lean_obj_tag(x_125) == 0)
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_124;
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec_ref(x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_127 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_dec(x_126);
return x_127;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 x_129 = x_127;
} else {
 lean_dec_ref(x_127);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
x_132 = lean_int_add(x_126, x_130);
lean_dec(x_130);
lean_dec(x_126);
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_131;
}
lean_ctor_set(x_133, 0, x_132);
if (lean_is_scalar(x_129)) {
 x_134 = lean_alloc_ctor(0, 1, 0);
} else {
 x_134 = x_129;
}
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
}
else
{
lean_dec(x_126);
return x_127;
}
}
}
else
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_124;
}
}
}
}
else
{
uint8_t x_135; 
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_135 = !lean_is_exclusive(x_97);
if (x_135 == 0)
{
return x_97;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_97, 0);
lean_inc(x_136);
lean_dec(x_97);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
}
}
else
{
lean_object* x_138; 
lean_dec_ref(x_84);
lean_dec(x_57);
x_138 = l_Lean_Meta_Structural_isInstHSubInt___redArg(x_69, x_8);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; 
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_142 = lean_box(0);
lean_ctor_set(x_138, 0, x_142);
return x_138;
}
else
{
lean_object* x_143; 
lean_free_object(x_138);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_143 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
if (lean_obj_tag(x_144) == 0)
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_143;
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec_ref(x_143);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
x_146 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_dec(x_145);
return x_146;
}
else
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_146);
if (x_148 == 0)
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_ctor_get(x_146, 0);
lean_dec(x_149);
x_150 = !lean_is_exclusive(x_147);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_147, 0);
x_152 = lean_int_sub(x_145, x_151);
lean_dec(x_151);
lean_dec(x_145);
lean_ctor_set(x_147, 0, x_152);
return x_146;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_147, 0);
lean_inc(x_153);
lean_dec(x_147);
x_154 = lean_int_sub(x_145, x_153);
lean_dec(x_153);
lean_dec(x_145);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_146, 0, x_155);
return x_146;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_146);
x_156 = lean_ctor_get(x_147, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_157 = x_147;
} else {
 lean_dec_ref(x_147);
 x_157 = lean_box(0);
}
x_158 = lean_int_sub(x_145, x_156);
lean_dec(x_156);
lean_dec(x_145);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_158);
x_160 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_160, 0, x_159);
return x_160;
}
}
}
else
{
lean_dec(x_145);
return x_146;
}
}
}
else
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_143;
}
}
}
else
{
lean_object* x_161; uint8_t x_162; 
x_161 = lean_ctor_get(x_138, 0);
lean_inc(x_161);
lean_dec(x_138);
x_162 = lean_unbox(x_161);
lean_dec(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_163 = lean_box(0);
x_164 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_164, 0, x_163);
return x_164;
}
else
{
lean_object* x_165; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_165 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 0)
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_165;
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec_ref(x_165);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_dec_ref(x_166);
x_168 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
if (lean_obj_tag(x_169) == 0)
{
lean_dec(x_167);
return x_168;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 x_170 = x_168;
} else {
 lean_dec_ref(x_168);
 x_170 = lean_box(0);
}
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_172 = x_169;
} else {
 lean_dec_ref(x_169);
 x_172 = lean_box(0);
}
x_173 = lean_int_sub(x_167, x_171);
lean_dec(x_171);
lean_dec(x_167);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(1, 1, 0);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_173);
if (lean_is_scalar(x_170)) {
 x_175 = lean_alloc_ctor(0, 1, 0);
} else {
 x_175 = x_170;
}
lean_ctor_set(x_175, 0, x_174);
return x_175;
}
}
else
{
lean_dec(x_167);
return x_168;
}
}
}
else
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_165;
}
}
}
}
else
{
uint8_t x_176; 
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_176 = !lean_is_exclusive(x_138);
if (x_176 == 0)
{
return x_138;
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_138, 0);
lean_inc(x_177);
lean_dec(x_138);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_177);
return x_178;
}
}
}
}
else
{
lean_object* x_179; 
lean_dec_ref(x_84);
lean_dec(x_57);
x_179 = l_Lean_Meta_Structural_isInstHMulInt___redArg(x_69, x_8);
if (lean_obj_tag(x_179) == 0)
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; uint8_t x_182; 
x_181 = lean_ctor_get(x_179, 0);
x_182 = lean_unbox(x_181);
lean_dec(x_181);
if (x_182 == 0)
{
lean_object* x_183; 
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_183 = lean_box(0);
lean_ctor_set(x_179, 0, x_183);
return x_179;
}
else
{
lean_object* x_184; 
lean_free_object(x_179);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_184 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 0)
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_184;
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec_ref(x_184);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
lean_dec_ref(x_185);
x_187 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
if (lean_obj_tag(x_188) == 0)
{
lean_dec(x_186);
return x_187;
}
else
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_187);
if (x_189 == 0)
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_ctor_get(x_187, 0);
lean_dec(x_190);
x_191 = !lean_is_exclusive(x_188);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_188, 0);
x_193 = lean_int_mul(x_186, x_192);
lean_dec(x_192);
lean_dec(x_186);
lean_ctor_set(x_188, 0, x_193);
return x_187;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_188, 0);
lean_inc(x_194);
lean_dec(x_188);
x_195 = lean_int_mul(x_186, x_194);
lean_dec(x_194);
lean_dec(x_186);
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_187, 0, x_196);
return x_187;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_187);
x_197 = lean_ctor_get(x_188, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 x_198 = x_188;
} else {
 lean_dec_ref(x_188);
 x_198 = lean_box(0);
}
x_199 = lean_int_mul(x_186, x_197);
lean_dec(x_197);
lean_dec(x_186);
if (lean_is_scalar(x_198)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_198;
}
lean_ctor_set(x_200, 0, x_199);
x_201 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
}
}
else
{
lean_dec(x_186);
return x_187;
}
}
}
else
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_184;
}
}
}
else
{
lean_object* x_202; uint8_t x_203; 
x_202 = lean_ctor_get(x_179, 0);
lean_inc(x_202);
lean_dec(x_179);
x_203 = lean_unbox(x_202);
lean_dec(x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_204 = lean_box(0);
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_204);
return x_205;
}
else
{
lean_object* x_206; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_206 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_206;
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec_ref(x_206);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec_ref(x_207);
x_209 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
if (lean_obj_tag(x_210) == 0)
{
lean_dec(x_208);
return x_209;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 x_211 = x_209;
} else {
 lean_dec_ref(x_209);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_210, 0);
lean_inc(x_212);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 x_213 = x_210;
} else {
 lean_dec_ref(x_210);
 x_213 = lean_box(0);
}
x_214 = lean_int_mul(x_208, x_212);
lean_dec(x_212);
lean_dec(x_208);
if (lean_is_scalar(x_213)) {
 x_215 = lean_alloc_ctor(1, 1, 0);
} else {
 x_215 = x_213;
}
lean_ctor_set(x_215, 0, x_214);
if (lean_is_scalar(x_211)) {
 x_216 = lean_alloc_ctor(0, 1, 0);
} else {
 x_216 = x_211;
}
lean_ctor_set(x_216, 0, x_215);
return x_216;
}
}
else
{
lean_dec(x_208);
return x_209;
}
}
}
else
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_206;
}
}
}
}
else
{
uint8_t x_217; 
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_217 = !lean_is_exclusive(x_179);
if (x_217 == 0)
{
return x_179;
}
else
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_179, 0);
lean_inc(x_218);
lean_dec(x_179);
x_219 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_219, 0, x_218);
return x_219;
}
}
}
}
else
{
lean_object* x_220; 
lean_dec_ref(x_84);
lean_dec(x_57);
x_220 = l_Lean_Meta_Structural_isInstHDivInt___redArg(x_69, x_8);
if (lean_obj_tag(x_220) == 0)
{
uint8_t x_221; 
x_221 = !lean_is_exclusive(x_220);
if (x_221 == 0)
{
lean_object* x_222; uint8_t x_223; 
x_222 = lean_ctor_get(x_220, 0);
x_223 = lean_unbox(x_222);
lean_dec(x_222);
if (x_223 == 0)
{
lean_object* x_224; 
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_224 = lean_box(0);
lean_ctor_set(x_220, 0, x_224);
return x_220;
}
else
{
lean_object* x_225; 
lean_free_object(x_220);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_225 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
if (lean_obj_tag(x_226) == 0)
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_225;
}
else
{
lean_object* x_227; lean_object* x_228; 
lean_dec_ref(x_225);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec_ref(x_226);
x_228 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
if (lean_obj_tag(x_229) == 0)
{
lean_dec(x_227);
return x_228;
}
else
{
uint8_t x_230; 
x_230 = !lean_is_exclusive(x_228);
if (x_230 == 0)
{
lean_object* x_231; uint8_t x_232; 
x_231 = lean_ctor_get(x_228, 0);
lean_dec(x_231);
x_232 = !lean_is_exclusive(x_229);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_229, 0);
x_234 = lean_int_ediv(x_227, x_233);
lean_dec(x_233);
lean_dec(x_227);
lean_ctor_set(x_229, 0, x_234);
return x_228;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_229, 0);
lean_inc(x_235);
lean_dec(x_229);
x_236 = lean_int_ediv(x_227, x_235);
lean_dec(x_235);
lean_dec(x_227);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_228, 0, x_237);
return x_228;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_228);
x_238 = lean_ctor_get(x_229, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 x_239 = x_229;
} else {
 lean_dec_ref(x_229);
 x_239 = lean_box(0);
}
x_240 = lean_int_ediv(x_227, x_238);
lean_dec(x_238);
lean_dec(x_227);
if (lean_is_scalar(x_239)) {
 x_241 = lean_alloc_ctor(1, 1, 0);
} else {
 x_241 = x_239;
}
lean_ctor_set(x_241, 0, x_240);
x_242 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_242, 0, x_241);
return x_242;
}
}
}
else
{
lean_dec(x_227);
return x_228;
}
}
}
else
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_225;
}
}
}
else
{
lean_object* x_243; uint8_t x_244; 
x_243 = lean_ctor_get(x_220, 0);
lean_inc(x_243);
lean_dec(x_220);
x_244 = lean_unbox(x_243);
lean_dec(x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; 
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_245 = lean_box(0);
x_246 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_246, 0, x_245);
return x_246;
}
else
{
lean_object* x_247; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_247 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 0)
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_247;
}
else
{
lean_object* x_249; lean_object* x_250; 
lean_dec_ref(x_247);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
lean_dec_ref(x_248);
x_250 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
if (lean_obj_tag(x_251) == 0)
{
lean_dec(x_249);
return x_250;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 x_252 = x_250;
} else {
 lean_dec_ref(x_250);
 x_252 = lean_box(0);
}
x_253 = lean_ctor_get(x_251, 0);
lean_inc(x_253);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 x_254 = x_251;
} else {
 lean_dec_ref(x_251);
 x_254 = lean_box(0);
}
x_255 = lean_int_ediv(x_249, x_253);
lean_dec(x_253);
lean_dec(x_249);
if (lean_is_scalar(x_254)) {
 x_256 = lean_alloc_ctor(1, 1, 0);
} else {
 x_256 = x_254;
}
lean_ctor_set(x_256, 0, x_255);
if (lean_is_scalar(x_252)) {
 x_257 = lean_alloc_ctor(0, 1, 0);
} else {
 x_257 = x_252;
}
lean_ctor_set(x_257, 0, x_256);
return x_257;
}
}
else
{
lean_dec(x_249);
return x_250;
}
}
}
else
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_247;
}
}
}
}
else
{
uint8_t x_258; 
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_258 = !lean_is_exclusive(x_220);
if (x_258 == 0)
{
return x_220;
}
else
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_220, 0);
lean_inc(x_259);
lean_dec(x_220);
x_260 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_260, 0, x_259);
return x_260;
}
}
}
}
else
{
lean_object* x_261; 
lean_dec_ref(x_84);
lean_dec(x_57);
x_261 = l_Lean_Meta_Structural_isInstHModInt___redArg(x_69, x_8);
if (lean_obj_tag(x_261) == 0)
{
uint8_t x_262; 
x_262 = !lean_is_exclusive(x_261);
if (x_262 == 0)
{
lean_object* x_263; uint8_t x_264; 
x_263 = lean_ctor_get(x_261, 0);
x_264 = lean_unbox(x_263);
lean_dec(x_263);
if (x_264 == 0)
{
lean_object* x_265; 
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_265 = lean_box(0);
lean_ctor_set(x_261, 0, x_265);
return x_261;
}
else
{
lean_object* x_266; 
lean_free_object(x_261);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_266 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
if (lean_obj_tag(x_267) == 0)
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_266;
}
else
{
lean_object* x_268; lean_object* x_269; 
lean_dec_ref(x_266);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
lean_dec_ref(x_267);
x_269 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
if (lean_obj_tag(x_270) == 0)
{
lean_dec(x_268);
return x_269;
}
else
{
uint8_t x_271; 
x_271 = !lean_is_exclusive(x_269);
if (x_271 == 0)
{
lean_object* x_272; uint8_t x_273; 
x_272 = lean_ctor_get(x_269, 0);
lean_dec(x_272);
x_273 = !lean_is_exclusive(x_270);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_270, 0);
x_275 = lean_int_emod(x_268, x_274);
lean_dec(x_274);
lean_dec(x_268);
lean_ctor_set(x_270, 0, x_275);
return x_269;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_270, 0);
lean_inc(x_276);
lean_dec(x_270);
x_277 = lean_int_emod(x_268, x_276);
lean_dec(x_276);
lean_dec(x_268);
x_278 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_269, 0, x_278);
return x_269;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_269);
x_279 = lean_ctor_get(x_270, 0);
lean_inc(x_279);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 x_280 = x_270;
} else {
 lean_dec_ref(x_270);
 x_280 = lean_box(0);
}
x_281 = lean_int_emod(x_268, x_279);
lean_dec(x_279);
lean_dec(x_268);
if (lean_is_scalar(x_280)) {
 x_282 = lean_alloc_ctor(1, 1, 0);
} else {
 x_282 = x_280;
}
lean_ctor_set(x_282, 0, x_281);
x_283 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_283, 0, x_282);
return x_283;
}
}
}
else
{
lean_dec(x_268);
return x_269;
}
}
}
else
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_266;
}
}
}
else
{
lean_object* x_284; uint8_t x_285; 
x_284 = lean_ctor_get(x_261, 0);
lean_inc(x_284);
lean_dec(x_261);
x_285 = lean_unbox(x_284);
lean_dec(x_284);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; 
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_286 = lean_box(0);
x_287 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_287, 0, x_286);
return x_287;
}
else
{
lean_object* x_288; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_288 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
if (lean_obj_tag(x_289) == 0)
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_288;
}
else
{
lean_object* x_290; lean_object* x_291; 
lean_dec_ref(x_288);
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
lean_dec_ref(x_289);
x_291 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
if (lean_obj_tag(x_292) == 0)
{
lean_dec(x_290);
return x_291;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 x_293 = x_291;
} else {
 lean_dec_ref(x_291);
 x_293 = lean_box(0);
}
x_294 = lean_ctor_get(x_292, 0);
lean_inc(x_294);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 x_295 = x_292;
} else {
 lean_dec_ref(x_292);
 x_295 = lean_box(0);
}
x_296 = lean_int_emod(x_290, x_294);
lean_dec(x_294);
lean_dec(x_290);
if (lean_is_scalar(x_295)) {
 x_297 = lean_alloc_ctor(1, 1, 0);
} else {
 x_297 = x_295;
}
lean_ctor_set(x_297, 0, x_296);
if (lean_is_scalar(x_293)) {
 x_298 = lean_alloc_ctor(0, 1, 0);
} else {
 x_298 = x_293;
}
lean_ctor_set(x_298, 0, x_297);
return x_298;
}
}
else
{
lean_dec(x_290);
return x_291;
}
}
}
else
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_288;
}
}
}
}
else
{
uint8_t x_299; 
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_299 = !lean_is_exclusive(x_261);
if (x_299 == 0)
{
return x_261;
}
else
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_261, 0);
lean_inc(x_300);
lean_dec(x_261);
x_301 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_301, 0, x_300);
return x_301;
}
}
}
}
else
{
lean_object* x_302; 
lean_dec_ref(x_84);
lean_dec(x_57);
x_302 = l_Lean_Meta_Structural_isInstHPowInt___redArg(x_69, x_8);
if (lean_obj_tag(x_302) == 0)
{
uint8_t x_303; 
x_303 = !lean_is_exclusive(x_302);
if (x_303 == 0)
{
lean_object* x_304; uint8_t x_305; 
x_304 = lean_ctor_get(x_302, 0);
x_305 = lean_unbox(x_304);
lean_dec(x_304);
if (x_305 == 0)
{
lean_object* x_306; 
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_306 = lean_box(0);
lean_ctor_set(x_302, 0, x_306);
return x_302;
}
else
{
lean_object* x_307; 
lean_free_object(x_302);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_307 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
if (lean_obj_tag(x_308) == 0)
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_307;
}
else
{
lean_object* x_309; lean_object* x_310; 
lean_dec_ref(x_307);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
lean_dec_ref(x_308);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_310 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_310) == 0)
{
uint8_t x_311; 
x_311 = !lean_is_exclusive(x_310);
if (x_311 == 0)
{
lean_object* x_312; 
x_312 = lean_ctor_get(x_310, 0);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; 
lean_dec(x_309);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_313 = lean_box(0);
lean_ctor_set(x_310, 0, x_313);
return x_310;
}
else
{
lean_object* x_314; lean_object* x_315; 
lean_free_object(x_310);
x_314 = lean_ctor_get(x_312, 0);
lean_inc(x_314);
lean_dec_ref(x_312);
lean_inc(x_314);
x_315 = l_Lean_Meta_Grind_Arith_checkExp(x_314, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
if (lean_obj_tag(x_315) == 0)
{
uint8_t x_316; 
x_316 = !lean_is_exclusive(x_315);
if (x_316 == 0)
{
lean_object* x_317; 
x_317 = lean_ctor_get(x_315, 0);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; 
lean_dec(x_314);
lean_dec(x_309);
x_318 = lean_box(0);
lean_ctor_set(x_315, 0, x_318);
return x_315;
}
else
{
uint8_t x_319; 
x_319 = !lean_is_exclusive(x_317);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; 
x_320 = lean_ctor_get(x_317, 0);
lean_dec(x_320);
x_321 = l_Int_pow(x_309, x_314);
lean_dec(x_314);
lean_dec(x_309);
lean_ctor_set(x_317, 0, x_321);
return x_315;
}
else
{
lean_object* x_322; lean_object* x_323; 
lean_dec(x_317);
x_322 = l_Int_pow(x_309, x_314);
lean_dec(x_314);
lean_dec(x_309);
x_323 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_315, 0, x_323);
return x_315;
}
}
}
else
{
lean_object* x_324; 
x_324 = lean_ctor_get(x_315, 0);
lean_inc(x_324);
lean_dec(x_315);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; 
lean_dec(x_314);
lean_dec(x_309);
x_325 = lean_box(0);
x_326 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_326, 0, x_325);
return x_326;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 x_327 = x_324;
} else {
 lean_dec_ref(x_324);
 x_327 = lean_box(0);
}
x_328 = l_Int_pow(x_309, x_314);
lean_dec(x_314);
lean_dec(x_309);
if (lean_is_scalar(x_327)) {
 x_329 = lean_alloc_ctor(1, 1, 0);
} else {
 x_329 = x_327;
}
lean_ctor_set(x_329, 0, x_328);
x_330 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_330, 0, x_329);
return x_330;
}
}
}
else
{
uint8_t x_331; 
lean_dec(x_314);
lean_dec(x_309);
x_331 = !lean_is_exclusive(x_315);
if (x_331 == 0)
{
return x_315;
}
else
{
lean_object* x_332; lean_object* x_333; 
x_332 = lean_ctor_get(x_315, 0);
lean_inc(x_332);
lean_dec(x_315);
x_333 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_333, 0, x_332);
return x_333;
}
}
}
}
else
{
lean_object* x_334; 
x_334 = lean_ctor_get(x_310, 0);
lean_inc(x_334);
lean_dec(x_310);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; 
lean_dec(x_309);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_335 = lean_box(0);
x_336 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_336, 0, x_335);
return x_336;
}
else
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_ctor_get(x_334, 0);
lean_inc(x_337);
lean_dec_ref(x_334);
lean_inc(x_337);
x_338 = l_Lean_Meta_Grind_Arith_checkExp(x_337, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 x_340 = x_338;
} else {
 lean_dec_ref(x_338);
 x_340 = lean_box(0);
}
if (lean_obj_tag(x_339) == 0)
{
lean_object* x_341; lean_object* x_342; 
lean_dec(x_337);
lean_dec(x_309);
x_341 = lean_box(0);
if (lean_is_scalar(x_340)) {
 x_342 = lean_alloc_ctor(0, 1, 0);
} else {
 x_342 = x_340;
}
lean_ctor_set(x_342, 0, x_341);
return x_342;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 x_343 = x_339;
} else {
 lean_dec_ref(x_339);
 x_343 = lean_box(0);
}
x_344 = l_Int_pow(x_309, x_337);
lean_dec(x_337);
lean_dec(x_309);
if (lean_is_scalar(x_343)) {
 x_345 = lean_alloc_ctor(1, 1, 0);
} else {
 x_345 = x_343;
}
lean_ctor_set(x_345, 0, x_344);
if (lean_is_scalar(x_340)) {
 x_346 = lean_alloc_ctor(0, 1, 0);
} else {
 x_346 = x_340;
}
lean_ctor_set(x_346, 0, x_345);
return x_346;
}
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_337);
lean_dec(x_309);
x_347 = lean_ctor_get(x_338, 0);
lean_inc(x_347);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 x_348 = x_338;
} else {
 lean_dec_ref(x_338);
 x_348 = lean_box(0);
}
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(1, 1, 0);
} else {
 x_349 = x_348;
}
lean_ctor_set(x_349, 0, x_347);
return x_349;
}
}
}
}
else
{
uint8_t x_350; 
lean_dec(x_309);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_350 = !lean_is_exclusive(x_310);
if (x_350 == 0)
{
return x_310;
}
else
{
lean_object* x_351; lean_object* x_352; 
x_351 = lean_ctor_get(x_310, 0);
lean_inc(x_351);
lean_dec(x_310);
x_352 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_352, 0, x_351);
return x_352;
}
}
}
}
else
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_307;
}
}
}
else
{
lean_object* x_353; uint8_t x_354; 
x_353 = lean_ctor_get(x_302, 0);
lean_inc(x_353);
lean_dec(x_302);
x_354 = lean_unbox(x_353);
lean_dec(x_353);
if (x_354 == 0)
{
lean_object* x_355; lean_object* x_356; 
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_355 = lean_box(0);
x_356 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_356, 0, x_355);
return x_356;
}
else
{
lean_object* x_357; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_357 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
if (lean_obj_tag(x_358) == 0)
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_357;
}
else
{
lean_object* x_359; lean_object* x_360; 
lean_dec_ref(x_357);
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
lean_dec_ref(x_358);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_360 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 x_362 = x_360;
} else {
 lean_dec_ref(x_360);
 x_362 = lean_box(0);
}
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_363; lean_object* x_364; 
lean_dec(x_359);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_363 = lean_box(0);
if (lean_is_scalar(x_362)) {
 x_364 = lean_alloc_ctor(0, 1, 0);
} else {
 x_364 = x_362;
}
lean_ctor_set(x_364, 0, x_363);
return x_364;
}
else
{
lean_object* x_365; lean_object* x_366; 
lean_dec(x_362);
x_365 = lean_ctor_get(x_361, 0);
lean_inc(x_365);
lean_dec_ref(x_361);
lean_inc(x_365);
x_366 = l_Lean_Meta_Grind_Arith_checkExp(x_365, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 x_368 = x_366;
} else {
 lean_dec_ref(x_366);
 x_368 = lean_box(0);
}
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_369; lean_object* x_370; 
lean_dec(x_365);
lean_dec(x_359);
x_369 = lean_box(0);
if (lean_is_scalar(x_368)) {
 x_370 = lean_alloc_ctor(0, 1, 0);
} else {
 x_370 = x_368;
}
lean_ctor_set(x_370, 0, x_369);
return x_370;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 x_371 = x_367;
} else {
 lean_dec_ref(x_367);
 x_371 = lean_box(0);
}
x_372 = l_Int_pow(x_359, x_365);
lean_dec(x_365);
lean_dec(x_359);
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 1, 0);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_372);
if (lean_is_scalar(x_368)) {
 x_374 = lean_alloc_ctor(0, 1, 0);
} else {
 x_374 = x_368;
}
lean_ctor_set(x_374, 0, x_373);
return x_374;
}
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_365);
lean_dec(x_359);
x_375 = lean_ctor_get(x_366, 0);
lean_inc(x_375);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 x_376 = x_366;
} else {
 lean_dec_ref(x_366);
 x_376 = lean_box(0);
}
if (lean_is_scalar(x_376)) {
 x_377 = lean_alloc_ctor(1, 1, 0);
} else {
 x_377 = x_376;
}
lean_ctor_set(x_377, 0, x_375);
return x_377;
}
}
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_359);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_378 = lean_ctor_get(x_360, 0);
lean_inc(x_378);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 x_379 = x_360;
} else {
 lean_dec_ref(x_360);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(1, 1, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_378);
return x_380;
}
}
}
else
{
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_357;
}
}
}
}
else
{
uint8_t x_381; 
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_381 = !lean_is_exclusive(x_302);
if (x_381 == 0)
{
return x_302;
}
else
{
lean_object* x_382; lean_object* x_383; 
x_382 = lean_ctor_get(x_302, 0);
lean_inc(x_382);
lean_dec(x_302);
x_383 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_383, 0, x_382);
return x_383;
}
}
}
}
}
}
}
else
{
lean_object* x_384; 
lean_dec_ref(x_70);
lean_dec_ref(x_69);
lean_dec(x_57);
x_384 = l_Lean_Meta_Structural_isInstNegInt___redArg(x_66, x_8);
if (lean_obj_tag(x_384) == 0)
{
uint8_t x_385; 
x_385 = !lean_is_exclusive(x_384);
if (x_385 == 0)
{
lean_object* x_386; uint8_t x_387; 
x_386 = lean_ctor_get(x_384, 0);
x_387 = lean_unbox(x_386);
lean_dec(x_386);
if (x_387 == 0)
{
lean_object* x_388; 
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_388 = lean_box(0);
lean_ctor_set(x_384, 0, x_388);
return x_384;
}
else
{
lean_object* x_389; 
lean_free_object(x_384);
x_389 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
if (lean_obj_tag(x_390) == 0)
{
return x_389;
}
else
{
uint8_t x_391; 
x_391 = !lean_is_exclusive(x_389);
if (x_391 == 0)
{
lean_object* x_392; uint8_t x_393; 
x_392 = lean_ctor_get(x_389, 0);
lean_dec(x_392);
x_393 = !lean_is_exclusive(x_390);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; 
x_394 = lean_ctor_get(x_390, 0);
x_395 = lean_int_neg(x_394);
lean_dec(x_394);
lean_ctor_set(x_390, 0, x_395);
return x_389;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_390, 0);
lean_inc(x_396);
lean_dec(x_390);
x_397 = lean_int_neg(x_396);
lean_dec(x_396);
x_398 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_389, 0, x_398);
return x_389;
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_389);
x_399 = lean_ctor_get(x_390, 0);
lean_inc(x_399);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 x_400 = x_390;
} else {
 lean_dec_ref(x_390);
 x_400 = lean_box(0);
}
x_401 = lean_int_neg(x_399);
lean_dec(x_399);
if (lean_is_scalar(x_400)) {
 x_402 = lean_alloc_ctor(1, 1, 0);
} else {
 x_402 = x_400;
}
lean_ctor_set(x_402, 0, x_401);
x_403 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_403, 0, x_402);
return x_403;
}
}
}
else
{
return x_389;
}
}
}
else
{
lean_object* x_404; uint8_t x_405; 
x_404 = lean_ctor_get(x_384, 0);
lean_inc(x_404);
lean_dec(x_384);
x_405 = lean_unbox(x_404);
lean_dec(x_404);
if (x_405 == 0)
{
lean_object* x_406; lean_object* x_407; 
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_406 = lean_box(0);
x_407 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_407, 0, x_406);
return x_407;
}
else
{
lean_object* x_408; 
x_408 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_63, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; 
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
if (lean_obj_tag(x_409) == 0)
{
return x_408;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 x_410 = x_408;
} else {
 lean_dec_ref(x_408);
 x_410 = lean_box(0);
}
x_411 = lean_ctor_get(x_409, 0);
lean_inc(x_411);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 x_412 = x_409;
} else {
 lean_dec_ref(x_409);
 x_412 = lean_box(0);
}
x_413 = lean_int_neg(x_411);
lean_dec(x_411);
if (lean_is_scalar(x_412)) {
 x_414 = lean_alloc_ctor(1, 1, 0);
} else {
 x_414 = x_412;
}
lean_ctor_set(x_414, 0, x_413);
if (lean_is_scalar(x_410)) {
 x_415 = lean_alloc_ctor(0, 1, 0);
} else {
 x_415 = x_410;
}
lean_ctor_set(x_415, 0, x_414);
return x_415;
}
}
else
{
return x_408;
}
}
}
}
else
{
uint8_t x_416; 
lean_dec_ref(x_63);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_416 = !lean_is_exclusive(x_384);
if (x_416 == 0)
{
return x_384;
}
else
{
lean_object* x_417; lean_object* x_418; 
x_417 = lean_ctor_get(x_384, 0);
lean_inc(x_417);
lean_dec(x_384);
x_418 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_418, 0, x_417);
return x_418;
}
}
}
}
else
{
lean_object* x_419; 
lean_dec_ref(x_70);
lean_dec_ref(x_69);
lean_dec_ref(x_66);
lean_dec_ref(x_63);
lean_dec(x_57);
x_419 = l_Lean_Meta_getIntValue_x3f(x_1, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
if (lean_obj_tag(x_420) == 1)
{
lean_dec_ref(x_420);
return x_419;
}
else
{
uint8_t x_421; 
lean_dec(x_420);
x_421 = !lean_is_exclusive(x_419);
if (x_421 == 0)
{
lean_object* x_422; lean_object* x_423; 
x_422 = lean_ctor_get(x_419, 0);
lean_dec(x_422);
x_423 = lean_box(0);
lean_ctor_set(x_419, 0, x_423);
return x_419;
}
else
{
lean_object* x_424; lean_object* x_425; 
lean_dec(x_419);
x_424 = lean_box(0);
x_425 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_425, 0, x_424);
return x_425;
}
}
}
else
{
return x_419;
}
}
}
else
{
lean_dec_ref(x_70);
lean_dec_ref(x_69);
lean_dec(x_57);
lean_dec_ref(x_1);
x_16 = x_66;
x_17 = x_63;
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
x_26 = x_10;
x_27 = lean_box(0);
goto block_54;
}
}
else
{
lean_dec_ref(x_70);
lean_dec_ref(x_69);
lean_dec(x_57);
lean_dec_ref(x_1);
x_16 = x_66;
x_17 = x_63;
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
x_26 = x_10;
x_27 = lean_box(0);
goto block_54;
}
}
}
}
block_60:
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_box(0);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 1, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
else
{
uint8_t x_426; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_426 = !lean_is_exclusive(x_55);
if (x_426 == 0)
{
return x_55;
}
else
{
lean_object* x_427; lean_object* x_428; 
x_427 = lean_ctor_get(x_55, 0);
lean_inc(x_427);
lean_dec(x_55);
x_428 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_428, 0, x_427);
return x_428;
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
block_54:
{
lean_object* x_28; 
x_28 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_16, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lean_Expr_cleanupAnnotations(x_29);
x_31 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1));
x_32 = l_Lean_Expr_isConstOf(x_30, x_31);
lean_dec_ref(x_30);
if (x_32 == 0)
{
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_17);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_33; 
x_33 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
if (lean_obj_tag(x_35) == 0)
{
lean_free_object(x_33);
x_12 = lean_box(0);
goto block_15;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_nat_to_int(x_37);
lean_ctor_set(x_35, 0, x_38);
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_nat_to_int(x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_33, 0, x_41);
return x_33;
}
}
}
else
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
lean_dec(x_33);
if (lean_obj_tag(x_42) == 0)
{
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = lean_nat_to_int(x_43);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(1, 1, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_33);
if (x_48 == 0)
{
return x_33;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_33, 0);
lean_inc(x_49);
lean_dec(x_33);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_17);
x_51 = !lean_is_exclusive(x_28);
if (x_51 == 0)
{
return x_28;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_28, 0);
lean_inc(x_52);
lean_dec(x_28);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_16; 
lean_inc_ref(x_1);
x_16 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l_Lean_Expr_cleanupAnnotations(x_18);
x_20 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2));
x_21 = l_Lean_Expr_isConstOf(x_19, x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_free_object(x_16);
x_22 = l_Lean_Expr_isApp(x_19);
if (x_22 == 0)
{
lean_dec_ref(x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_12 = lean_box(0);
goto block_15;
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
x_12 = lean_box(0);
goto block_15;
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
x_12 = lean_box(0);
goto block_15;
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
x_12 = lean_box(0);
goto block_15;
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
x_12 = lean_box(0);
goto block_15;
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
x_12 = lean_box(0);
goto block_15;
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
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_57; 
x_57 = l_Lean_Meta_Structural_isInstHAddNat___redArg(x_35, x_8);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_61 = lean_box(0);
lean_ctor_set(x_57, 0, x_61);
return x_57;
}
else
{
lean_object* x_62; 
lean_free_object(x_57);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_62 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_62;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec_ref(x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_dec(x_64);
return x_65;
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_65, 0);
lean_dec(x_68);
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_66, 0);
x_71 = lean_nat_add(x_64, x_70);
lean_dec(x_70);
lean_dec(x_64);
lean_ctor_set(x_66, 0, x_71);
return x_65;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_66, 0);
lean_inc(x_72);
lean_dec(x_66);
x_73 = lean_nat_add(x_64, x_72);
lean_dec(x_72);
lean_dec(x_64);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_65, 0, x_74);
return x_65;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_65);
x_75 = lean_ctor_get(x_66, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_76 = x_66;
} else {
 lean_dec_ref(x_66);
 x_76 = lean_box(0);
}
x_77 = lean_nat_add(x_64, x_75);
lean_dec(x_75);
lean_dec(x_64);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(1, 1, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
else
{
lean_dec(x_64);
return x_65;
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
return x_62;
}
}
}
else
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_57, 0);
lean_inc(x_80);
lean_dec(x_57);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
else
{
lean_object* x_84; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_84 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_84;
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec_ref(x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
lean_dec(x_86);
return x_87;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
x_92 = lean_nat_add(x_86, x_90);
lean_dec(x_90);
lean_dec(x_86);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(1, 1, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
if (lean_is_scalar(x_89)) {
 x_94 = lean_alloc_ctor(0, 1, 0);
} else {
 x_94 = x_89;
}
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
else
{
lean_dec(x_86);
return x_87;
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
return x_84;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_95 = !lean_is_exclusive(x_57);
if (x_95 == 0)
{
return x_57;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_57, 0);
lean_inc(x_96);
lean_dec(x_57);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
return x_97;
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
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_102 = lean_box(0);
lean_ctor_set(x_98, 0, x_102);
return x_98;
}
else
{
lean_object* x_103; 
lean_free_object(x_98);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_103 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_obj_tag(x_104) == 0)
{
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_103;
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec_ref(x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_106 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
lean_dec(x_105);
return x_106;
}
else
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_106);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_106, 0);
lean_dec(x_109);
x_110 = !lean_is_exclusive(x_107);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_107, 0);
x_112 = lean_nat_mul(x_105, x_111);
lean_dec(x_111);
lean_dec(x_105);
lean_ctor_set(x_107, 0, x_112);
return x_106;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_107, 0);
lean_inc(x_113);
lean_dec(x_107);
x_114 = lean_nat_mul(x_105, x_113);
lean_dec(x_113);
lean_dec(x_105);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_106, 0, x_115);
return x_106;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_106);
x_116 = lean_ctor_get(x_107, 0);
lean_inc(x_116);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_117 = x_107;
} else {
 lean_dec_ref(x_107);
 x_117 = lean_box(0);
}
x_118 = lean_nat_mul(x_105, x_116);
lean_dec(x_116);
lean_dec(x_105);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(1, 1, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
else
{
lean_dec(x_105);
return x_106;
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
return x_103;
}
}
}
else
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_98, 0);
lean_inc(x_121);
lean_dec(x_98);
x_122 = lean_unbox(x_121);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
else
{
lean_object* x_125; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_125 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
if (lean_obj_tag(x_126) == 0)
{
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_125;
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec_ref(x_125);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
if (lean_obj_tag(x_129) == 0)
{
lean_dec(x_127);
return x_128;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_130 = x_128;
} else {
 lean_dec_ref(x_128);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
x_133 = lean_nat_mul(x_127, x_131);
lean_dec(x_131);
lean_dec(x_127);
if (lean_is_scalar(x_132)) {
 x_134 = lean_alloc_ctor(1, 1, 0);
} else {
 x_134 = x_132;
}
lean_ctor_set(x_134, 0, x_133);
if (lean_is_scalar(x_130)) {
 x_135 = lean_alloc_ctor(0, 1, 0);
} else {
 x_135 = x_130;
}
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
else
{
lean_dec(x_127);
return x_128;
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
return x_125;
}
}
}
}
else
{
uint8_t x_136; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_136 = !lean_is_exclusive(x_98);
if (x_136 == 0)
{
return x_98;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_98, 0);
lean_inc(x_137);
lean_dec(x_98);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
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
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
lean_object* x_141; uint8_t x_142; 
x_141 = lean_ctor_get(x_139, 0);
x_142 = lean_unbox(x_141);
lean_dec(x_141);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_143 = lean_box(0);
lean_ctor_set(x_139, 0, x_143);
return x_139;
}
else
{
lean_object* x_144; 
lean_free_object(x_139);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_144 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
if (lean_obj_tag(x_145) == 0)
{
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_144;
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec_ref(x_144);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec_ref(x_145);
x_147 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
lean_dec(x_146);
return x_147;
}
else
{
uint8_t x_149; 
x_149 = !lean_is_exclusive(x_147);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_ctor_get(x_147, 0);
lean_dec(x_150);
x_151 = !lean_is_exclusive(x_148);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_148, 0);
x_153 = lean_nat_sub(x_146, x_152);
lean_dec(x_152);
lean_dec(x_146);
lean_ctor_set(x_148, 0, x_153);
return x_147;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_148, 0);
lean_inc(x_154);
lean_dec(x_148);
x_155 = lean_nat_sub(x_146, x_154);
lean_dec(x_154);
lean_dec(x_146);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_147, 0, x_156);
return x_147;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_147);
x_157 = lean_ctor_get(x_148, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 x_158 = x_148;
} else {
 lean_dec_ref(x_148);
 x_158 = lean_box(0);
}
x_159 = lean_nat_sub(x_146, x_157);
lean_dec(x_157);
lean_dec(x_146);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(1, 1, 0);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_159);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_160);
return x_161;
}
}
}
else
{
lean_dec(x_146);
return x_147;
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
return x_144;
}
}
}
else
{
lean_object* x_162; uint8_t x_163; 
x_162 = lean_ctor_get(x_139, 0);
lean_inc(x_162);
lean_dec(x_139);
x_163 = lean_unbox(x_162);
lean_dec(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_164 = lean_box(0);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
else
{
lean_object* x_166; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_166 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
if (lean_obj_tag(x_167) == 0)
{
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_166;
}
else
{
lean_object* x_168; lean_object* x_169; 
lean_dec_ref(x_166);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
lean_dec_ref(x_167);
x_169 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
if (lean_obj_tag(x_170) == 0)
{
lean_dec(x_168);
return x_169;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_171 = x_169;
} else {
 lean_dec_ref(x_169);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
x_174 = lean_nat_sub(x_168, x_172);
lean_dec(x_172);
lean_dec(x_168);
if (lean_is_scalar(x_173)) {
 x_175 = lean_alloc_ctor(1, 1, 0);
} else {
 x_175 = x_173;
}
lean_ctor_set(x_175, 0, x_174);
if (lean_is_scalar(x_171)) {
 x_176 = lean_alloc_ctor(0, 1, 0);
} else {
 x_176 = x_171;
}
lean_ctor_set(x_176, 0, x_175);
return x_176;
}
}
else
{
lean_dec(x_168);
return x_169;
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
return x_166;
}
}
}
}
else
{
uint8_t x_177; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_177 = !lean_is_exclusive(x_139);
if (x_177 == 0)
{
return x_139;
}
else
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_139, 0);
lean_inc(x_178);
lean_dec(x_139);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_178);
return x_179;
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
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_180);
if (x_181 == 0)
{
lean_object* x_182; uint8_t x_183; 
x_182 = lean_ctor_get(x_180, 0);
x_183 = lean_unbox(x_182);
lean_dec(x_182);
if (x_183 == 0)
{
lean_object* x_184; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_184 = lean_box(0);
lean_ctor_set(x_180, 0, x_184);
return x_180;
}
else
{
lean_object* x_185; 
lean_free_object(x_180);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_185 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 0)
{
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_185;
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec_ref(x_185);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
lean_dec_ref(x_186);
x_188 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
if (lean_obj_tag(x_189) == 0)
{
lean_dec(x_187);
return x_188;
}
else
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_188);
if (x_190 == 0)
{
lean_object* x_191; uint8_t x_192; 
x_191 = lean_ctor_get(x_188, 0);
lean_dec(x_191);
x_192 = !lean_is_exclusive(x_189);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_189, 0);
x_194 = lean_nat_div(x_187, x_193);
lean_dec(x_193);
lean_dec(x_187);
lean_ctor_set(x_189, 0, x_194);
return x_188;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_189, 0);
lean_inc(x_195);
lean_dec(x_189);
x_196 = lean_nat_div(x_187, x_195);
lean_dec(x_195);
lean_dec(x_187);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_188, 0, x_197);
return x_188;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_188);
x_198 = lean_ctor_get(x_189, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 x_199 = x_189;
} else {
 lean_dec_ref(x_189);
 x_199 = lean_box(0);
}
x_200 = lean_nat_div(x_187, x_198);
lean_dec(x_198);
lean_dec(x_187);
if (lean_is_scalar(x_199)) {
 x_201 = lean_alloc_ctor(1, 1, 0);
} else {
 x_201 = x_199;
}
lean_ctor_set(x_201, 0, x_200);
x_202 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_202, 0, x_201);
return x_202;
}
}
}
else
{
lean_dec(x_187);
return x_188;
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
return x_185;
}
}
}
else
{
lean_object* x_203; uint8_t x_204; 
x_203 = lean_ctor_get(x_180, 0);
lean_inc(x_203);
lean_dec(x_180);
x_204 = lean_unbox(x_203);
lean_dec(x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_205 = lean_box(0);
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_205);
return x_206;
}
else
{
lean_object* x_207; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_207 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_207;
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec_ref(x_207);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
lean_dec_ref(x_208);
x_210 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
if (lean_obj_tag(x_211) == 0)
{
lean_dec(x_209);
return x_210;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 x_212 = x_210;
} else {
 lean_dec_ref(x_210);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_211, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 x_214 = x_211;
} else {
 lean_dec_ref(x_211);
 x_214 = lean_box(0);
}
x_215 = lean_nat_div(x_209, x_213);
lean_dec(x_213);
lean_dec(x_209);
if (lean_is_scalar(x_214)) {
 x_216 = lean_alloc_ctor(1, 1, 0);
} else {
 x_216 = x_214;
}
lean_ctor_set(x_216, 0, x_215);
if (lean_is_scalar(x_212)) {
 x_217 = lean_alloc_ctor(0, 1, 0);
} else {
 x_217 = x_212;
}
lean_ctor_set(x_217, 0, x_216);
return x_217;
}
}
else
{
lean_dec(x_209);
return x_210;
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
return x_207;
}
}
}
}
else
{
uint8_t x_218; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_218 = !lean_is_exclusive(x_180);
if (x_218 == 0)
{
return x_180;
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_180, 0);
lean_inc(x_219);
lean_dec(x_180);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_219);
return x_220;
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
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
lean_object* x_223; uint8_t x_224; 
x_223 = lean_ctor_get(x_221, 0);
x_224 = lean_unbox(x_223);
lean_dec(x_223);
if (x_224 == 0)
{
lean_object* x_225; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_225 = lean_box(0);
lean_ctor_set(x_221, 0, x_225);
return x_221;
}
else
{
lean_object* x_226; 
lean_free_object(x_221);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_226 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; 
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
if (lean_obj_tag(x_227) == 0)
{
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_226;
}
else
{
lean_object* x_228; lean_object* x_229; 
lean_dec_ref(x_226);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
lean_dec_ref(x_227);
x_229 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
if (lean_obj_tag(x_230) == 0)
{
lean_dec(x_228);
return x_229;
}
else
{
uint8_t x_231; 
x_231 = !lean_is_exclusive(x_229);
if (x_231 == 0)
{
lean_object* x_232; uint8_t x_233; 
x_232 = lean_ctor_get(x_229, 0);
lean_dec(x_232);
x_233 = !lean_is_exclusive(x_230);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_230, 0);
x_235 = lean_nat_mod(x_228, x_234);
lean_dec(x_234);
lean_dec(x_228);
lean_ctor_set(x_230, 0, x_235);
return x_229;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_230, 0);
lean_inc(x_236);
lean_dec(x_230);
x_237 = lean_nat_mod(x_228, x_236);
lean_dec(x_236);
lean_dec(x_228);
x_238 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_229, 0, x_238);
return x_229;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_229);
x_239 = lean_ctor_get(x_230, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 x_240 = x_230;
} else {
 lean_dec_ref(x_230);
 x_240 = lean_box(0);
}
x_241 = lean_nat_mod(x_228, x_239);
lean_dec(x_239);
lean_dec(x_228);
if (lean_is_scalar(x_240)) {
 x_242 = lean_alloc_ctor(1, 1, 0);
} else {
 x_242 = x_240;
}
lean_ctor_set(x_242, 0, x_241);
x_243 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_243, 0, x_242);
return x_243;
}
}
}
else
{
lean_dec(x_228);
return x_229;
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
return x_226;
}
}
}
else
{
lean_object* x_244; uint8_t x_245; 
x_244 = lean_ctor_get(x_221, 0);
lean_inc(x_244);
lean_dec(x_221);
x_245 = lean_unbox(x_244);
lean_dec(x_244);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_246 = lean_box(0);
x_247 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_247, 0, x_246);
return x_247;
}
else
{
lean_object* x_248; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_248 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
if (lean_obj_tag(x_249) == 0)
{
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_248;
}
else
{
lean_object* x_250; lean_object* x_251; 
lean_dec_ref(x_248);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
lean_dec_ref(x_249);
x_251 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
if (lean_obj_tag(x_252) == 0)
{
lean_dec(x_250);
return x_251;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 x_253 = x_251;
} else {
 lean_dec_ref(x_251);
 x_253 = lean_box(0);
}
x_254 = lean_ctor_get(x_252, 0);
lean_inc(x_254);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 x_255 = x_252;
} else {
 lean_dec_ref(x_252);
 x_255 = lean_box(0);
}
x_256 = lean_nat_mod(x_250, x_254);
lean_dec(x_254);
lean_dec(x_250);
if (lean_is_scalar(x_255)) {
 x_257 = lean_alloc_ctor(1, 1, 0);
} else {
 x_257 = x_255;
}
lean_ctor_set(x_257, 0, x_256);
if (lean_is_scalar(x_253)) {
 x_258 = lean_alloc_ctor(0, 1, 0);
} else {
 x_258 = x_253;
}
lean_ctor_set(x_258, 0, x_257);
return x_258;
}
}
else
{
lean_dec(x_250);
return x_251;
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
return x_248;
}
}
}
}
else
{
uint8_t x_259; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_259 = !lean_is_exclusive(x_221);
if (x_259 == 0)
{
return x_221;
}
else
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_221, 0);
lean_inc(x_260);
lean_dec(x_221);
x_261 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_261, 0, x_260);
return x_261;
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
uint8_t x_263; 
x_263 = !lean_is_exclusive(x_262);
if (x_263 == 0)
{
lean_object* x_264; uint8_t x_265; 
x_264 = lean_ctor_get(x_262, 0);
x_265 = lean_unbox(x_264);
lean_dec(x_264);
if (x_265 == 0)
{
lean_object* x_266; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_266 = lean_box(0);
lean_ctor_set(x_262, 0, x_266);
return x_262;
}
else
{
lean_object* x_267; 
lean_free_object(x_262);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_267 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
if (lean_obj_tag(x_268) == 0)
{
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_267;
}
else
{
lean_object* x_269; lean_object* x_270; 
lean_dec_ref(x_267);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
lean_dec_ref(x_268);
lean_inc(x_269);
x_270 = l_Lean_Meta_Grind_Arith_checkExp(x_269, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_270) == 0)
{
uint8_t x_271; 
x_271 = !lean_is_exclusive(x_270);
if (x_271 == 0)
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_270, 0);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; 
lean_dec(x_269);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_273 = lean_box(0);
lean_ctor_set(x_270, 0, x_273);
return x_270;
}
else
{
lean_object* x_274; 
lean_free_object(x_270);
lean_dec_ref(x_272);
x_274 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
if (lean_obj_tag(x_275) == 0)
{
lean_dec(x_269);
return x_274;
}
else
{
uint8_t x_276; 
x_276 = !lean_is_exclusive(x_274);
if (x_276 == 0)
{
lean_object* x_277; uint8_t x_278; 
x_277 = lean_ctor_get(x_274, 0);
lean_dec(x_277);
x_278 = !lean_is_exclusive(x_275);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_275, 0);
x_280 = lean_nat_pow(x_279, x_269);
lean_dec(x_269);
lean_dec(x_279);
lean_ctor_set(x_275, 0, x_280);
return x_274;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_275, 0);
lean_inc(x_281);
lean_dec(x_275);
x_282 = lean_nat_pow(x_281, x_269);
lean_dec(x_269);
lean_dec(x_281);
x_283 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_274, 0, x_283);
return x_274;
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_274);
x_284 = lean_ctor_get(x_275, 0);
lean_inc(x_284);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 x_285 = x_275;
} else {
 lean_dec_ref(x_275);
 x_285 = lean_box(0);
}
x_286 = lean_nat_pow(x_284, x_269);
lean_dec(x_269);
lean_dec(x_284);
if (lean_is_scalar(x_285)) {
 x_287 = lean_alloc_ctor(1, 1, 0);
} else {
 x_287 = x_285;
}
lean_ctor_set(x_287, 0, x_286);
x_288 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_288, 0, x_287);
return x_288;
}
}
}
else
{
lean_dec(x_269);
return x_274;
}
}
}
else
{
lean_object* x_289; 
x_289 = lean_ctor_get(x_270, 0);
lean_inc(x_289);
lean_dec(x_270);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; 
lean_dec(x_269);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_290 = lean_box(0);
x_291 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_291, 0, x_290);
return x_291;
}
else
{
lean_object* x_292; 
lean_dec_ref(x_289);
x_292 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
if (lean_obj_tag(x_293) == 0)
{
lean_dec(x_269);
return x_292;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 x_294 = x_292;
} else {
 lean_dec_ref(x_292);
 x_294 = lean_box(0);
}
x_295 = lean_ctor_get(x_293, 0);
lean_inc(x_295);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 x_296 = x_293;
} else {
 lean_dec_ref(x_293);
 x_296 = lean_box(0);
}
x_297 = lean_nat_pow(x_295, x_269);
lean_dec(x_269);
lean_dec(x_295);
if (lean_is_scalar(x_296)) {
 x_298 = lean_alloc_ctor(1, 1, 0);
} else {
 x_298 = x_296;
}
lean_ctor_set(x_298, 0, x_297);
if (lean_is_scalar(x_294)) {
 x_299 = lean_alloc_ctor(0, 1, 0);
} else {
 x_299 = x_294;
}
lean_ctor_set(x_299, 0, x_298);
return x_299;
}
}
else
{
lean_dec(x_269);
return x_292;
}
}
}
}
else
{
uint8_t x_300; 
lean_dec(x_269);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_300 = !lean_is_exclusive(x_270);
if (x_300 == 0)
{
return x_270;
}
else
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_270, 0);
lean_inc(x_301);
lean_dec(x_270);
x_302 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_302, 0, x_301);
return x_302;
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
return x_267;
}
}
}
else
{
lean_object* x_303; uint8_t x_304; 
x_303 = lean_ctor_get(x_262, 0);
lean_inc(x_303);
lean_dec(x_262);
x_304 = lean_unbox(x_303);
lean_dec(x_303);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_305 = lean_box(0);
x_306 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_306, 0, x_305);
return x_306;
}
else
{
lean_object* x_307; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_307 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
if (lean_obj_tag(x_308) == 0)
{
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_307;
}
else
{
lean_object* x_309; lean_object* x_310; 
lean_dec_ref(x_307);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
lean_dec_ref(x_308);
lean_inc(x_309);
x_310 = l_Lean_Meta_Grind_Arith_checkExp(x_309, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 x_312 = x_310;
} else {
 lean_dec_ref(x_310);
 x_312 = lean_box(0);
}
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_313; lean_object* x_314; 
lean_dec(x_309);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_313 = lean_box(0);
if (lean_is_scalar(x_312)) {
 x_314 = lean_alloc_ctor(0, 1, 0);
} else {
 x_314 = x_312;
}
lean_ctor_set(x_314, 0, x_313);
return x_314;
}
else
{
lean_object* x_315; 
lean_dec(x_312);
lean_dec_ref(x_311);
x_315 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
if (lean_obj_tag(x_316) == 0)
{
lean_dec(x_309);
return x_315;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 x_317 = x_315;
} else {
 lean_dec_ref(x_315);
 x_317 = lean_box(0);
}
x_318 = lean_ctor_get(x_316, 0);
lean_inc(x_318);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 x_319 = x_316;
} else {
 lean_dec_ref(x_316);
 x_319 = lean_box(0);
}
x_320 = lean_nat_pow(x_318, x_309);
lean_dec(x_309);
lean_dec(x_318);
if (lean_is_scalar(x_319)) {
 x_321 = lean_alloc_ctor(1, 1, 0);
} else {
 x_321 = x_319;
}
lean_ctor_set(x_321, 0, x_320);
if (lean_is_scalar(x_317)) {
 x_322 = lean_alloc_ctor(0, 1, 0);
} else {
 x_322 = x_317;
}
lean_ctor_set(x_322, 0, x_321);
return x_322;
}
}
else
{
lean_dec(x_309);
return x_315;
}
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_309);
lean_dec_ref(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_323 = lean_ctor_get(x_310, 0);
lean_inc(x_323);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 x_324 = x_310;
} else {
 lean_dec_ref(x_310);
 x_324 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_325 = lean_alloc_ctor(1, 1, 0);
} else {
 x_325 = x_324;
}
lean_ctor_set(x_325, 0, x_323);
return x_325;
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
return x_307;
}
}
}
}
else
{
uint8_t x_326; 
lean_dec_ref(x_32);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_326 = !lean_is_exclusive(x_262);
if (x_326 == 0)
{
return x_262;
}
else
{
lean_object* x_327; lean_object* x_328; 
x_327 = lean_ctor_get(x_262, 0);
lean_inc(x_327);
lean_dec(x_262);
x_328 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_328, 0, x_327);
return x_328;
}
}
}
}
}
}
}
else
{
lean_object* x_329; 
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_32);
lean_dec_ref(x_23);
x_329 = l_Lean_Meta_getNatValue_x3f(x_1, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
if (lean_obj_tag(x_330) == 1)
{
lean_dec_ref(x_330);
return x_329;
}
else
{
uint8_t x_331; 
lean_dec(x_330);
x_331 = !lean_is_exclusive(x_329);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; 
x_332 = lean_ctor_get(x_329, 0);
lean_dec(x_332);
x_333 = lean_box(0);
lean_ctor_set(x_329, 0, x_333);
return x_329;
}
else
{
lean_object* x_334; lean_object* x_335; 
lean_dec(x_329);
x_334 = lean_box(0);
x_335 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_335, 0, x_334);
return x_335;
}
}
}
else
{
return x_329;
}
}
}
}
}
else
{
lean_object* x_336; 
lean_dec_ref(x_24);
lean_dec_ref(x_1);
x_336 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
if (lean_obj_tag(x_337) == 0)
{
return x_336;
}
else
{
uint8_t x_338; 
x_338 = !lean_is_exclusive(x_336);
if (x_338 == 0)
{
lean_object* x_339; uint8_t x_340; 
x_339 = lean_ctor_get(x_336, 0);
lean_dec(x_339);
x_340 = !lean_is_exclusive(x_337);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_337, 0);
x_342 = lean_unsigned_to_nat(1u);
x_343 = lean_nat_add(x_341, x_342);
lean_dec(x_341);
lean_ctor_set(x_337, 0, x_343);
return x_336;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_344 = lean_ctor_get(x_337, 0);
lean_inc(x_344);
lean_dec(x_337);
x_345 = lean_unsigned_to_nat(1u);
x_346 = lean_nat_add(x_344, x_345);
lean_dec(x_344);
x_347 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_336, 0, x_347);
return x_336;
}
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_336);
x_348 = lean_ctor_get(x_337, 0);
lean_inc(x_348);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 x_349 = x_337;
} else {
 lean_dec_ref(x_337);
 x_349 = lean_box(0);
}
x_350 = lean_unsigned_to_nat(1u);
x_351 = lean_nat_add(x_348, x_350);
lean_dec(x_348);
if (lean_is_scalar(x_349)) {
 x_352 = lean_alloc_ctor(1, 1, 0);
} else {
 x_352 = x_349;
}
lean_ctor_set(x_352, 0, x_351);
x_353 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_353, 0, x_352);
return x_353;
}
}
}
else
{
return x_336;
}
}
}
else
{
lean_object* x_354; 
lean_dec_ref(x_24);
lean_dec_ref(x_1);
x_354 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_354) == 0)
{
uint8_t x_355; 
x_355 = !lean_is_exclusive(x_354);
if (x_355 == 0)
{
lean_object* x_356; 
x_356 = lean_ctor_get(x_354, 0);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; 
x_357 = lean_box(0);
lean_ctor_set(x_354, 0, x_357);
return x_354;
}
else
{
uint8_t x_358; 
x_358 = !lean_is_exclusive(x_356);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; 
x_359 = lean_ctor_get(x_356, 0);
x_360 = l_Int_toNat(x_359);
lean_dec(x_359);
lean_ctor_set(x_356, 0, x_360);
return x_354;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = lean_ctor_get(x_356, 0);
lean_inc(x_361);
lean_dec(x_356);
x_362 = l_Int_toNat(x_361);
lean_dec(x_361);
x_363 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_363, 0, x_362);
lean_ctor_set(x_354, 0, x_363);
return x_354;
}
}
}
else
{
lean_object* x_364; 
x_364 = lean_ctor_get(x_354, 0);
lean_inc(x_364);
lean_dec(x_354);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; 
x_365 = lean_box(0);
x_366 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_366, 0, x_365);
return x_366;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_367 = lean_ctor_get(x_364, 0);
lean_inc(x_367);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 x_368 = x_364;
} else {
 lean_dec_ref(x_364);
 x_368 = lean_box(0);
}
x_369 = l_Int_toNat(x_367);
lean_dec(x_367);
if (lean_is_scalar(x_368)) {
 x_370 = lean_alloc_ctor(1, 1, 0);
} else {
 x_370 = x_368;
}
lean_ctor_set(x_370, 0, x_369);
x_371 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_371, 0, x_370);
return x_371;
}
}
}
else
{
uint8_t x_372; 
x_372 = !lean_is_exclusive(x_354);
if (x_372 == 0)
{
return x_354;
}
else
{
lean_object* x_373; lean_object* x_374; 
x_373 = lean_ctor_get(x_354, 0);
lean_inc(x_373);
lean_dec(x_354);
x_374 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_374, 0, x_373);
return x_374;
}
}
}
}
else
{
lean_object* x_375; 
lean_dec_ref(x_24);
lean_dec_ref(x_1);
x_375 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_375) == 0)
{
uint8_t x_376; 
x_376 = !lean_is_exclusive(x_375);
if (x_376 == 0)
{
lean_object* x_377; 
x_377 = lean_ctor_get(x_375, 0);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; 
x_378 = lean_box(0);
lean_ctor_set(x_375, 0, x_378);
return x_375;
}
else
{
uint8_t x_379; 
x_379 = !lean_is_exclusive(x_377);
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; 
x_380 = lean_ctor_get(x_377, 0);
x_381 = lean_nat_abs(x_380);
lean_dec(x_380);
lean_ctor_set(x_377, 0, x_381);
return x_375;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_377, 0);
lean_inc(x_382);
lean_dec(x_377);
x_383 = lean_nat_abs(x_382);
lean_dec(x_382);
x_384 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_375, 0, x_384);
return x_375;
}
}
}
else
{
lean_object* x_385; 
x_385 = lean_ctor_get(x_375, 0);
lean_inc(x_385);
lean_dec(x_375);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; 
x_386 = lean_box(0);
x_387 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_387, 0, x_386);
return x_387;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_388 = lean_ctor_get(x_385, 0);
lean_inc(x_388);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 x_389 = x_385;
} else {
 lean_dec_ref(x_385);
 x_389 = lean_box(0);
}
x_390 = lean_nat_abs(x_388);
lean_dec(x_388);
if (lean_is_scalar(x_389)) {
 x_391 = lean_alloc_ctor(1, 1, 0);
} else {
 x_391 = x_389;
}
lean_ctor_set(x_391, 0, x_390);
x_392 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_392, 0, x_391);
return x_392;
}
}
}
else
{
uint8_t x_393; 
x_393 = !lean_is_exclusive(x_375);
if (x_393 == 0)
{
return x_375;
}
else
{
lean_object* x_394; lean_object* x_395; 
x_394 = lean_ctor_get(x_375, 0);
lean_inc(x_394);
lean_dec(x_375);
x_395 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_395, 0, x_394);
return x_395;
}
}
}
}
}
else
{
lean_object* x_396; 
lean_dec_ref(x_19);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_396 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31));
lean_ctor_set(x_16, 0, x_396);
return x_16;
}
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; 
x_397 = lean_ctor_get(x_16, 0);
lean_inc(x_397);
lean_dec(x_16);
x_398 = l_Lean_Expr_cleanupAnnotations(x_397);
x_399 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2));
x_400 = l_Lean_Expr_isConstOf(x_398, x_399);
if (x_400 == 0)
{
uint8_t x_401; 
x_401 = l_Lean_Expr_isApp(x_398);
if (x_401 == 0)
{
lean_dec_ref(x_398);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; 
x_402 = lean_ctor_get(x_398, 1);
lean_inc_ref(x_402);
x_403 = l_Lean_Expr_appFnCleanup___redArg(x_398);
x_404 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5));
x_405 = l_Lean_Expr_isConstOf(x_403, x_404);
if (x_405 == 0)
{
lean_object* x_406; uint8_t x_407; 
x_406 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7));
x_407 = l_Lean_Expr_isConstOf(x_403, x_406);
if (x_407 == 0)
{
lean_object* x_408; uint8_t x_409; 
x_408 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9));
x_409 = l_Lean_Expr_isConstOf(x_403, x_408);
if (x_409 == 0)
{
uint8_t x_410; 
x_410 = l_Lean_Expr_isApp(x_403);
if (x_410 == 0)
{
lean_dec_ref(x_403);
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_411; lean_object* x_412; uint8_t x_413; 
x_411 = lean_ctor_get(x_403, 1);
lean_inc_ref(x_411);
x_412 = l_Lean_Expr_appFnCleanup___redArg(x_403);
x_413 = l_Lean_Expr_isApp(x_412);
if (x_413 == 0)
{
lean_dec_ref(x_412);
lean_dec_ref(x_411);
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; 
x_414 = lean_ctor_get(x_412, 1);
lean_inc_ref(x_414);
x_415 = l_Lean_Expr_appFnCleanup___redArg(x_412);
x_416 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12));
x_417 = l_Lean_Expr_isConstOf(x_415, x_416);
if (x_417 == 0)
{
uint8_t x_418; 
lean_dec_ref(x_1);
x_418 = l_Lean_Expr_isApp(x_415);
if (x_418 == 0)
{
lean_dec_ref(x_415);
lean_dec_ref(x_414);
lean_dec_ref(x_411);
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_419; uint8_t x_420; 
x_419 = l_Lean_Expr_appFnCleanup___redArg(x_415);
x_420 = l_Lean_Expr_isApp(x_419);
if (x_420 == 0)
{
lean_dec_ref(x_419);
lean_dec_ref(x_414);
lean_dec_ref(x_411);
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_421; uint8_t x_422; 
x_421 = l_Lean_Expr_appFnCleanup___redArg(x_419);
x_422 = l_Lean_Expr_isApp(x_421);
if (x_422 == 0)
{
lean_dec_ref(x_421);
lean_dec_ref(x_414);
lean_dec_ref(x_411);
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_423; lean_object* x_424; uint8_t x_425; 
x_423 = l_Lean_Expr_appFnCleanup___redArg(x_421);
x_424 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15));
x_425 = l_Lean_Expr_isConstOf(x_423, x_424);
if (x_425 == 0)
{
lean_object* x_426; uint8_t x_427; 
x_426 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18));
x_427 = l_Lean_Expr_isConstOf(x_423, x_426);
if (x_427 == 0)
{
lean_object* x_428; uint8_t x_429; 
x_428 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21));
x_429 = l_Lean_Expr_isConstOf(x_423, x_428);
if (x_429 == 0)
{
lean_object* x_430; uint8_t x_431; 
x_430 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24));
x_431 = l_Lean_Expr_isConstOf(x_423, x_430);
if (x_431 == 0)
{
lean_object* x_432; uint8_t x_433; 
x_432 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27));
x_433 = l_Lean_Expr_isConstOf(x_423, x_432);
if (x_433 == 0)
{
lean_object* x_434; uint8_t x_435; 
x_434 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30));
x_435 = l_Lean_Expr_isConstOf(x_423, x_434);
lean_dec_ref(x_423);
if (x_435 == 0)
{
lean_dec_ref(x_414);
lean_dec_ref(x_411);
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_436; 
x_436 = l_Lean_Meta_Structural_isInstHAddNat___redArg(x_414, x_8);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; uint8_t x_439; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 x_438 = x_436;
} else {
 lean_dec_ref(x_436);
 x_438 = lean_box(0);
}
x_439 = lean_unbox(x_437);
lean_dec(x_437);
if (x_439 == 0)
{
lean_object* x_440; lean_object* x_441; 
lean_dec_ref(x_411);
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_440 = lean_box(0);
if (lean_is_scalar(x_438)) {
 x_441 = lean_alloc_ctor(0, 1, 0);
} else {
 x_441 = x_438;
}
lean_ctor_set(x_441, 0, x_440);
return x_441;
}
else
{
lean_object* x_442; 
lean_dec(x_438);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_442 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_411, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
if (lean_obj_tag(x_443) == 0)
{
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_442;
}
else
{
lean_object* x_444; lean_object* x_445; 
lean_dec_ref(x_442);
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
lean_dec_ref(x_443);
x_445 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_402, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
if (lean_obj_tag(x_446) == 0)
{
lean_dec(x_444);
return x_445;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 x_447 = x_445;
} else {
 lean_dec_ref(x_445);
 x_447 = lean_box(0);
}
x_448 = lean_ctor_get(x_446, 0);
lean_inc(x_448);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 x_449 = x_446;
} else {
 lean_dec_ref(x_446);
 x_449 = lean_box(0);
}
x_450 = lean_nat_add(x_444, x_448);
lean_dec(x_448);
lean_dec(x_444);
if (lean_is_scalar(x_449)) {
 x_451 = lean_alloc_ctor(1, 1, 0);
} else {
 x_451 = x_449;
}
lean_ctor_set(x_451, 0, x_450);
if (lean_is_scalar(x_447)) {
 x_452 = lean_alloc_ctor(0, 1, 0);
} else {
 x_452 = x_447;
}
lean_ctor_set(x_452, 0, x_451);
return x_452;
}
}
else
{
lean_dec(x_444);
return x_445;
}
}
}
else
{
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_442;
}
}
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
lean_dec_ref(x_411);
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_453 = lean_ctor_get(x_436, 0);
lean_inc(x_453);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 x_454 = x_436;
} else {
 lean_dec_ref(x_436);
 x_454 = lean_box(0);
}
if (lean_is_scalar(x_454)) {
 x_455 = lean_alloc_ctor(1, 1, 0);
} else {
 x_455 = x_454;
}
lean_ctor_set(x_455, 0, x_453);
return x_455;
}
}
}
else
{
lean_object* x_456; 
lean_dec_ref(x_423);
x_456 = l_Lean_Meta_Structural_isInstHMulNat___redArg(x_414, x_8);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; uint8_t x_459; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 x_458 = x_456;
} else {
 lean_dec_ref(x_456);
 x_458 = lean_box(0);
}
x_459 = lean_unbox(x_457);
lean_dec(x_457);
if (x_459 == 0)
{
lean_object* x_460; lean_object* x_461; 
lean_dec_ref(x_411);
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_460 = lean_box(0);
if (lean_is_scalar(x_458)) {
 x_461 = lean_alloc_ctor(0, 1, 0);
} else {
 x_461 = x_458;
}
lean_ctor_set(x_461, 0, x_460);
return x_461;
}
else
{
lean_object* x_462; 
lean_dec(x_458);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_462 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_411, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
if (lean_obj_tag(x_463) == 0)
{
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_462;
}
else
{
lean_object* x_464; lean_object* x_465; 
lean_dec_ref(x_462);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
lean_dec_ref(x_463);
x_465 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_402, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
if (lean_obj_tag(x_466) == 0)
{
lean_dec(x_464);
return x_465;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 x_467 = x_465;
} else {
 lean_dec_ref(x_465);
 x_467 = lean_box(0);
}
x_468 = lean_ctor_get(x_466, 0);
lean_inc(x_468);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 x_469 = x_466;
} else {
 lean_dec_ref(x_466);
 x_469 = lean_box(0);
}
x_470 = lean_nat_mul(x_464, x_468);
lean_dec(x_468);
lean_dec(x_464);
if (lean_is_scalar(x_469)) {
 x_471 = lean_alloc_ctor(1, 1, 0);
} else {
 x_471 = x_469;
}
lean_ctor_set(x_471, 0, x_470);
if (lean_is_scalar(x_467)) {
 x_472 = lean_alloc_ctor(0, 1, 0);
} else {
 x_472 = x_467;
}
lean_ctor_set(x_472, 0, x_471);
return x_472;
}
}
else
{
lean_dec(x_464);
return x_465;
}
}
}
else
{
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_462;
}
}
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; 
lean_dec_ref(x_411);
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_473 = lean_ctor_get(x_456, 0);
lean_inc(x_473);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 x_474 = x_456;
} else {
 lean_dec_ref(x_456);
 x_474 = lean_box(0);
}
if (lean_is_scalar(x_474)) {
 x_475 = lean_alloc_ctor(1, 1, 0);
} else {
 x_475 = x_474;
}
lean_ctor_set(x_475, 0, x_473);
return x_475;
}
}
}
else
{
lean_object* x_476; 
lean_dec_ref(x_423);
x_476 = l_Lean_Meta_Structural_isInstHSubNat___redArg(x_414, x_8);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; uint8_t x_479; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 x_478 = x_476;
} else {
 lean_dec_ref(x_476);
 x_478 = lean_box(0);
}
x_479 = lean_unbox(x_477);
lean_dec(x_477);
if (x_479 == 0)
{
lean_object* x_480; lean_object* x_481; 
lean_dec_ref(x_411);
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_480 = lean_box(0);
if (lean_is_scalar(x_478)) {
 x_481 = lean_alloc_ctor(0, 1, 0);
} else {
 x_481 = x_478;
}
lean_ctor_set(x_481, 0, x_480);
return x_481;
}
else
{
lean_object* x_482; 
lean_dec(x_478);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_482 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_411, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; 
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
if (lean_obj_tag(x_483) == 0)
{
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_482;
}
else
{
lean_object* x_484; lean_object* x_485; 
lean_dec_ref(x_482);
x_484 = lean_ctor_get(x_483, 0);
lean_inc(x_484);
lean_dec_ref(x_483);
x_485 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_402, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
if (lean_obj_tag(x_486) == 0)
{
lean_dec(x_484);
return x_485;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 x_487 = x_485;
} else {
 lean_dec_ref(x_485);
 x_487 = lean_box(0);
}
x_488 = lean_ctor_get(x_486, 0);
lean_inc(x_488);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 x_489 = x_486;
} else {
 lean_dec_ref(x_486);
 x_489 = lean_box(0);
}
x_490 = lean_nat_sub(x_484, x_488);
lean_dec(x_488);
lean_dec(x_484);
if (lean_is_scalar(x_489)) {
 x_491 = lean_alloc_ctor(1, 1, 0);
} else {
 x_491 = x_489;
}
lean_ctor_set(x_491, 0, x_490);
if (lean_is_scalar(x_487)) {
 x_492 = lean_alloc_ctor(0, 1, 0);
} else {
 x_492 = x_487;
}
lean_ctor_set(x_492, 0, x_491);
return x_492;
}
}
else
{
lean_dec(x_484);
return x_485;
}
}
}
else
{
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_482;
}
}
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_dec_ref(x_411);
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_493 = lean_ctor_get(x_476, 0);
lean_inc(x_493);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 x_494 = x_476;
} else {
 lean_dec_ref(x_476);
 x_494 = lean_box(0);
}
if (lean_is_scalar(x_494)) {
 x_495 = lean_alloc_ctor(1, 1, 0);
} else {
 x_495 = x_494;
}
lean_ctor_set(x_495, 0, x_493);
return x_495;
}
}
}
else
{
lean_object* x_496; 
lean_dec_ref(x_423);
x_496 = l_Lean_Meta_Structural_isInstHDivNat___redArg(x_414, x_8);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; uint8_t x_499; 
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 x_498 = x_496;
} else {
 lean_dec_ref(x_496);
 x_498 = lean_box(0);
}
x_499 = lean_unbox(x_497);
lean_dec(x_497);
if (x_499 == 0)
{
lean_object* x_500; lean_object* x_501; 
lean_dec_ref(x_411);
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_500 = lean_box(0);
if (lean_is_scalar(x_498)) {
 x_501 = lean_alloc_ctor(0, 1, 0);
} else {
 x_501 = x_498;
}
lean_ctor_set(x_501, 0, x_500);
return x_501;
}
else
{
lean_object* x_502; 
lean_dec(x_498);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_502 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_411, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; 
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
if (lean_obj_tag(x_503) == 0)
{
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_502;
}
else
{
lean_object* x_504; lean_object* x_505; 
lean_dec_ref(x_502);
x_504 = lean_ctor_get(x_503, 0);
lean_inc(x_504);
lean_dec_ref(x_503);
x_505 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_402, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
if (lean_obj_tag(x_506) == 0)
{
lean_dec(x_504);
return x_505;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 x_507 = x_505;
} else {
 lean_dec_ref(x_505);
 x_507 = lean_box(0);
}
x_508 = lean_ctor_get(x_506, 0);
lean_inc(x_508);
if (lean_is_exclusive(x_506)) {
 lean_ctor_release(x_506, 0);
 x_509 = x_506;
} else {
 lean_dec_ref(x_506);
 x_509 = lean_box(0);
}
x_510 = lean_nat_div(x_504, x_508);
lean_dec(x_508);
lean_dec(x_504);
if (lean_is_scalar(x_509)) {
 x_511 = lean_alloc_ctor(1, 1, 0);
} else {
 x_511 = x_509;
}
lean_ctor_set(x_511, 0, x_510);
if (lean_is_scalar(x_507)) {
 x_512 = lean_alloc_ctor(0, 1, 0);
} else {
 x_512 = x_507;
}
lean_ctor_set(x_512, 0, x_511);
return x_512;
}
}
else
{
lean_dec(x_504);
return x_505;
}
}
}
else
{
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_502;
}
}
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec_ref(x_411);
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_513 = lean_ctor_get(x_496, 0);
lean_inc(x_513);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 x_514 = x_496;
} else {
 lean_dec_ref(x_496);
 x_514 = lean_box(0);
}
if (lean_is_scalar(x_514)) {
 x_515 = lean_alloc_ctor(1, 1, 0);
} else {
 x_515 = x_514;
}
lean_ctor_set(x_515, 0, x_513);
return x_515;
}
}
}
else
{
lean_object* x_516; 
lean_dec_ref(x_423);
x_516 = l_Lean_Meta_Structural_isInstHModNat___redArg(x_414, x_8);
if (lean_obj_tag(x_516) == 0)
{
lean_object* x_517; lean_object* x_518; uint8_t x_519; 
x_517 = lean_ctor_get(x_516, 0);
lean_inc(x_517);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 x_518 = x_516;
} else {
 lean_dec_ref(x_516);
 x_518 = lean_box(0);
}
x_519 = lean_unbox(x_517);
lean_dec(x_517);
if (x_519 == 0)
{
lean_object* x_520; lean_object* x_521; 
lean_dec_ref(x_411);
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_520 = lean_box(0);
if (lean_is_scalar(x_518)) {
 x_521 = lean_alloc_ctor(0, 1, 0);
} else {
 x_521 = x_518;
}
lean_ctor_set(x_521, 0, x_520);
return x_521;
}
else
{
lean_object* x_522; 
lean_dec(x_518);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_522 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_411, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; 
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
if (lean_obj_tag(x_523) == 0)
{
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_522;
}
else
{
lean_object* x_524; lean_object* x_525; 
lean_dec_ref(x_522);
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
lean_dec_ref(x_523);
x_525 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_402, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_525) == 0)
{
lean_object* x_526; 
x_526 = lean_ctor_get(x_525, 0);
lean_inc(x_526);
if (lean_obj_tag(x_526) == 0)
{
lean_dec(x_524);
return x_525;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
if (lean_is_exclusive(x_525)) {
 lean_ctor_release(x_525, 0);
 x_527 = x_525;
} else {
 lean_dec_ref(x_525);
 x_527 = lean_box(0);
}
x_528 = lean_ctor_get(x_526, 0);
lean_inc(x_528);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 x_529 = x_526;
} else {
 lean_dec_ref(x_526);
 x_529 = lean_box(0);
}
x_530 = lean_nat_mod(x_524, x_528);
lean_dec(x_528);
lean_dec(x_524);
if (lean_is_scalar(x_529)) {
 x_531 = lean_alloc_ctor(1, 1, 0);
} else {
 x_531 = x_529;
}
lean_ctor_set(x_531, 0, x_530);
if (lean_is_scalar(x_527)) {
 x_532 = lean_alloc_ctor(0, 1, 0);
} else {
 x_532 = x_527;
}
lean_ctor_set(x_532, 0, x_531);
return x_532;
}
}
else
{
lean_dec(x_524);
return x_525;
}
}
}
else
{
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_522;
}
}
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec_ref(x_411);
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_533 = lean_ctor_get(x_516, 0);
lean_inc(x_533);
if (lean_is_exclusive(x_516)) {
 lean_ctor_release(x_516, 0);
 x_534 = x_516;
} else {
 lean_dec_ref(x_516);
 x_534 = lean_box(0);
}
if (lean_is_scalar(x_534)) {
 x_535 = lean_alloc_ctor(1, 1, 0);
} else {
 x_535 = x_534;
}
lean_ctor_set(x_535, 0, x_533);
return x_535;
}
}
}
else
{
lean_object* x_536; 
lean_dec_ref(x_423);
x_536 = l_Lean_Meta_Structural_isInstHPowNat___redArg(x_414, x_8);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; lean_object* x_538; uint8_t x_539; 
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
if (lean_is_exclusive(x_536)) {
 lean_ctor_release(x_536, 0);
 x_538 = x_536;
} else {
 lean_dec_ref(x_536);
 x_538 = lean_box(0);
}
x_539 = lean_unbox(x_537);
lean_dec(x_537);
if (x_539 == 0)
{
lean_object* x_540; lean_object* x_541; 
lean_dec_ref(x_411);
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_540 = lean_box(0);
if (lean_is_scalar(x_538)) {
 x_541 = lean_alloc_ctor(0, 1, 0);
} else {
 x_541 = x_538;
}
lean_ctor_set(x_541, 0, x_540);
return x_541;
}
else
{
lean_object* x_542; 
lean_dec(x_538);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_542 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_402, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; 
x_543 = lean_ctor_get(x_542, 0);
lean_inc(x_543);
if (lean_obj_tag(x_543) == 0)
{
lean_dec_ref(x_411);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_542;
}
else
{
lean_object* x_544; lean_object* x_545; 
lean_dec_ref(x_542);
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
lean_dec_ref(x_543);
lean_inc(x_544);
x_545 = l_Lean_Meta_Grind_Arith_checkExp(x_544, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_546; lean_object* x_547; 
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 x_547 = x_545;
} else {
 lean_dec_ref(x_545);
 x_547 = lean_box(0);
}
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_548; lean_object* x_549; 
lean_dec(x_544);
lean_dec_ref(x_411);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_548 = lean_box(0);
if (lean_is_scalar(x_547)) {
 x_549 = lean_alloc_ctor(0, 1, 0);
} else {
 x_549 = x_547;
}
lean_ctor_set(x_549, 0, x_548);
return x_549;
}
else
{
lean_object* x_550; 
lean_dec(x_547);
lean_dec_ref(x_546);
x_550 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_411, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_550) == 0)
{
lean_object* x_551; 
x_551 = lean_ctor_get(x_550, 0);
lean_inc(x_551);
if (lean_obj_tag(x_551) == 0)
{
lean_dec(x_544);
return x_550;
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
if (lean_is_exclusive(x_550)) {
 lean_ctor_release(x_550, 0);
 x_552 = x_550;
} else {
 lean_dec_ref(x_550);
 x_552 = lean_box(0);
}
x_553 = lean_ctor_get(x_551, 0);
lean_inc(x_553);
if (lean_is_exclusive(x_551)) {
 lean_ctor_release(x_551, 0);
 x_554 = x_551;
} else {
 lean_dec_ref(x_551);
 x_554 = lean_box(0);
}
x_555 = lean_nat_pow(x_553, x_544);
lean_dec(x_544);
lean_dec(x_553);
if (lean_is_scalar(x_554)) {
 x_556 = lean_alloc_ctor(1, 1, 0);
} else {
 x_556 = x_554;
}
lean_ctor_set(x_556, 0, x_555);
if (lean_is_scalar(x_552)) {
 x_557 = lean_alloc_ctor(0, 1, 0);
} else {
 x_557 = x_552;
}
lean_ctor_set(x_557, 0, x_556);
return x_557;
}
}
else
{
lean_dec(x_544);
return x_550;
}
}
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; 
lean_dec(x_544);
lean_dec_ref(x_411);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_558 = lean_ctor_get(x_545, 0);
lean_inc(x_558);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 x_559 = x_545;
} else {
 lean_dec_ref(x_545);
 x_559 = lean_box(0);
}
if (lean_is_scalar(x_559)) {
 x_560 = lean_alloc_ctor(1, 1, 0);
} else {
 x_560 = x_559;
}
lean_ctor_set(x_560, 0, x_558);
return x_560;
}
}
}
else
{
lean_dec_ref(x_411);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_542;
}
}
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
lean_dec_ref(x_411);
lean_dec_ref(x_402);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_561 = lean_ctor_get(x_536, 0);
lean_inc(x_561);
if (lean_is_exclusive(x_536)) {
 lean_ctor_release(x_536, 0);
 x_562 = x_536;
} else {
 lean_dec_ref(x_536);
 x_562 = lean_box(0);
}
if (lean_is_scalar(x_562)) {
 x_563 = lean_alloc_ctor(1, 1, 0);
} else {
 x_563 = x_562;
}
lean_ctor_set(x_563, 0, x_561);
return x_563;
}
}
}
}
}
}
else
{
lean_object* x_564; 
lean_dec_ref(x_415);
lean_dec_ref(x_414);
lean_dec_ref(x_411);
lean_dec_ref(x_402);
x_564 = l_Lean_Meta_getNatValue_x3f(x_1, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; 
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
if (lean_obj_tag(x_565) == 1)
{
lean_dec_ref(x_565);
return x_564;
}
else
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; 
lean_dec(x_565);
if (lean_is_exclusive(x_564)) {
 lean_ctor_release(x_564, 0);
 x_566 = x_564;
} else {
 lean_dec_ref(x_564);
 x_566 = lean_box(0);
}
x_567 = lean_box(0);
if (lean_is_scalar(x_566)) {
 x_568 = lean_alloc_ctor(0, 1, 0);
} else {
 x_568 = x_566;
}
lean_ctor_set(x_568, 0, x_567);
return x_568;
}
}
else
{
return x_564;
}
}
}
}
}
else
{
lean_object* x_569; 
lean_dec_ref(x_403);
lean_dec_ref(x_1);
x_569 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_402, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; 
x_570 = lean_ctor_get(x_569, 0);
lean_inc(x_570);
if (lean_obj_tag(x_570) == 0)
{
return x_569;
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 x_571 = x_569;
} else {
 lean_dec_ref(x_569);
 x_571 = lean_box(0);
}
x_572 = lean_ctor_get(x_570, 0);
lean_inc(x_572);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 x_573 = x_570;
} else {
 lean_dec_ref(x_570);
 x_573 = lean_box(0);
}
x_574 = lean_unsigned_to_nat(1u);
x_575 = lean_nat_add(x_572, x_574);
lean_dec(x_572);
if (lean_is_scalar(x_573)) {
 x_576 = lean_alloc_ctor(1, 1, 0);
} else {
 x_576 = x_573;
}
lean_ctor_set(x_576, 0, x_575);
if (lean_is_scalar(x_571)) {
 x_577 = lean_alloc_ctor(0, 1, 0);
} else {
 x_577 = x_571;
}
lean_ctor_set(x_577, 0, x_576);
return x_577;
}
}
else
{
return x_569;
}
}
}
else
{
lean_object* x_578; 
lean_dec_ref(x_403);
lean_dec_ref(x_1);
x_578 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_402, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_578) == 0)
{
lean_object* x_579; lean_object* x_580; 
x_579 = lean_ctor_get(x_578, 0);
lean_inc(x_579);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 x_580 = x_578;
} else {
 lean_dec_ref(x_578);
 x_580 = lean_box(0);
}
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_581; lean_object* x_582; 
x_581 = lean_box(0);
if (lean_is_scalar(x_580)) {
 x_582 = lean_alloc_ctor(0, 1, 0);
} else {
 x_582 = x_580;
}
lean_ctor_set(x_582, 0, x_581);
return x_582;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_583 = lean_ctor_get(x_579, 0);
lean_inc(x_583);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 x_584 = x_579;
} else {
 lean_dec_ref(x_579);
 x_584 = lean_box(0);
}
x_585 = l_Int_toNat(x_583);
lean_dec(x_583);
if (lean_is_scalar(x_584)) {
 x_586 = lean_alloc_ctor(1, 1, 0);
} else {
 x_586 = x_584;
}
lean_ctor_set(x_586, 0, x_585);
if (lean_is_scalar(x_580)) {
 x_587 = lean_alloc_ctor(0, 1, 0);
} else {
 x_587 = x_580;
}
lean_ctor_set(x_587, 0, x_586);
return x_587;
}
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_588 = lean_ctor_get(x_578, 0);
lean_inc(x_588);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 x_589 = x_578;
} else {
 lean_dec_ref(x_578);
 x_589 = lean_box(0);
}
if (lean_is_scalar(x_589)) {
 x_590 = lean_alloc_ctor(1, 1, 0);
} else {
 x_590 = x_589;
}
lean_ctor_set(x_590, 0, x_588);
return x_590;
}
}
}
else
{
lean_object* x_591; 
lean_dec_ref(x_403);
lean_dec_ref(x_1);
x_591 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_402, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_591) == 0)
{
lean_object* x_592; lean_object* x_593; 
x_592 = lean_ctor_get(x_591, 0);
lean_inc(x_592);
if (lean_is_exclusive(x_591)) {
 lean_ctor_release(x_591, 0);
 x_593 = x_591;
} else {
 lean_dec_ref(x_591);
 x_593 = lean_box(0);
}
if (lean_obj_tag(x_592) == 0)
{
lean_object* x_594; lean_object* x_595; 
x_594 = lean_box(0);
if (lean_is_scalar(x_593)) {
 x_595 = lean_alloc_ctor(0, 1, 0);
} else {
 x_595 = x_593;
}
lean_ctor_set(x_595, 0, x_594);
return x_595;
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_596 = lean_ctor_get(x_592, 0);
lean_inc(x_596);
if (lean_is_exclusive(x_592)) {
 lean_ctor_release(x_592, 0);
 x_597 = x_592;
} else {
 lean_dec_ref(x_592);
 x_597 = lean_box(0);
}
x_598 = lean_nat_abs(x_596);
lean_dec(x_596);
if (lean_is_scalar(x_597)) {
 x_599 = lean_alloc_ctor(1, 1, 0);
} else {
 x_599 = x_597;
}
lean_ctor_set(x_599, 0, x_598);
if (lean_is_scalar(x_593)) {
 x_600 = lean_alloc_ctor(0, 1, 0);
} else {
 x_600 = x_593;
}
lean_ctor_set(x_600, 0, x_599);
return x_600;
}
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_601 = lean_ctor_get(x_591, 0);
lean_inc(x_601);
if (lean_is_exclusive(x_591)) {
 lean_ctor_release(x_591, 0);
 x_602 = x_591;
} else {
 lean_dec_ref(x_591);
 x_602 = lean_box(0);
}
if (lean_is_scalar(x_602)) {
 x_603 = lean_alloc_ctor(1, 1, 0);
} else {
 x_603 = x_602;
}
lean_ctor_set(x_603, 0, x_601);
return x_603;
}
}
}
}
else
{
lean_object* x_604; lean_object* x_605; 
lean_dec_ref(x_398);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_604 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31));
x_605 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_605, 0, x_604);
return x_605;
}
}
}
else
{
uint8_t x_606; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_606 = !lean_is_exclusive(x_16);
if (x_606 == 0)
{
return x_16;
}
else
{
lean_object* x_607; lean_object* x_608; 
x_607 = lean_ctor_get(x_16, 0);
lean_inc(x_607);
lean_dec(x_16);
x_608 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_608, 0, x_607);
return x_608;
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_checkExp___closed__2 = _init_l_Lean_Meta_Grind_Arith_checkExp___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_checkExp___closed__2);
l_Lean_Meta_Grind_Arith_checkExp___closed__4 = _init_l_Lean_Meta_Grind_Arith_checkExp___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_checkExp___closed__4);
l_Lean_Meta_Grind_Arith_checkExp___closed__6 = _init_l_Lean_Meta_Grind_Arith_checkExp___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_checkExp___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

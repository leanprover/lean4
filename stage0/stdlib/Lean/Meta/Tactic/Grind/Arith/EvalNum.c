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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
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
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg(lean_object*, lean_object*);
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
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_checkExp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_checkExp___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_checkExp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "exponent "};
static const lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_checkExp___closed__1_value;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalNat_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalNat_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalInt_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalInt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___lam__0(lean_object* v_____do__lift_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_12_, 0, v_____do__lift_1_);
v___x_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_13_, 0, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___lam__0___boxed(lean_object* v_____do__lift_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Meta_Grind_Arith_checkExp___lam__0(v_____do__lift_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
lean_dec(v___y_15_);
return v_res_25_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___closed__2(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_checkExp___closed__1));
v___x_30_ = l_Lean_stringToMessageData(v___x_29_);
return v___x_30_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___closed__4(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_checkExp___closed__3));
v___x_33_ = l_Lean_stringToMessageData(v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___closed__6(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_checkExp___closed__5));
v___x_36_ = l_Lean_stringToMessageData(v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp(lean_object* v_k_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_39_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_53_; lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_124_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_a_52_);
lean_dec_ref(v___x_51_);
v___x_53_ = l_Lean_Meta_Grind_Arith_checkExp___lam__0(v_a_52_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_);
v_a_54_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_124_ == 0)
{
v___x_56_ = v___x_53_;
v_isShared_57_ = v_isSharedCheck_124_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_53_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_124_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v_val_58_; lean_object* v_exp_59_; uint8_t v___x_60_; 
v_val_58_ = lean_ctor_get(v_a_54_, 0);
lean_inc(v_val_58_);
lean_dec(v_a_54_);
v_exp_59_ = lean_ctor_get(v_val_58_, 7);
lean_inc(v_exp_59_);
lean_dec(v_val_58_);
v___x_60_ = lean_nat_dec_lt(v_exp_59_, v_k_37_);
lean_dec(v_exp_59_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v___x_63_; 
lean_dec(v_k_37_);
v___x_61_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_checkExp___closed__0));
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 0, v___x_61_);
v___x_63_ = v___x_56_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v___x_61_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
else
{
lean_object* v___x_65_; 
lean_del_object(v___x_56_);
v___x_65_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_39_);
if (lean_obj_tag(v___x_65_) == 0)
{
lean_object* v_a_66_; lean_object* v___x_67_; lean_object* v_a_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_115_; 
v_a_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc(v_a_66_);
lean_dec_ref(v___x_65_);
v___x_67_ = l_Lean_Meta_Grind_Arith_checkExp___lam__0(v_a_66_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_);
v_a_68_ = lean_ctor_get(v___x_67_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_67_);
if (v_isSharedCheck_115_ == 0)
{
v___x_70_ = v___x_67_;
v_isShared_71_ = v_isSharedCheck_115_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_a_68_);
lean_dec(v___x_67_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_115_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v_val_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_114_; 
v_val_72_ = lean_ctor_get(v_a_68_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v_a_68_);
if (v_isSharedCheck_114_ == 0)
{
v___x_74_ = v_a_68_;
v_isShared_75_ = v_isSharedCheck_114_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_val_72_);
lean_dec(v_a_68_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_114_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
uint8_t v_verbose_76_; 
v_verbose_76_ = lean_ctor_get_uint8(v_val_72_, sizeof(void*)*11 + 15);
lean_dec(v_val_72_);
if (v_verbose_76_ == 0)
{
lean_del_object(v___x_74_);
lean_del_object(v___x_70_);
lean_dec(v_k_37_);
goto v___jp_48_;
}
else
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_39_);
if (lean_obj_tag(v___x_77_) == 0)
{
lean_object* v_a_78_; lean_object* v_exp_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_83_; 
v_a_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v_a_78_);
lean_dec_ref(v___x_77_);
v_exp_79_ = lean_ctor_get(v_a_78_, 7);
lean_inc(v_exp_79_);
lean_dec(v_a_78_);
v___x_80_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_checkExp___closed__2, &l_Lean_Meta_Grind_Arith_checkExp___closed__2_once, _init_l_Lean_Meta_Grind_Arith_checkExp___closed__2);
v___x_81_ = l_Nat_reprFast(v_k_37_);
if (v_isShared_75_ == 0)
{
lean_ctor_set_tag(v___x_74_, 3);
lean_ctor_set(v___x_74_, 0, v___x_81_);
v___x_83_ = v___x_74_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_81_);
v___x_83_ = v_reuseFailAlloc_105_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_90_; 
v___x_84_ = l_Lean_MessageData_ofFormat(v___x_83_);
v___x_85_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_80_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_checkExp___closed__4, &l_Lean_Meta_Grind_Arith_checkExp___closed__4_once, _init_l_Lean_Meta_Grind_Arith_checkExp___closed__4);
v___x_87_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = l_Nat_reprFast(v_exp_79_);
if (v_isShared_71_ == 0)
{
lean_ctor_set_tag(v___x_70_, 3);
lean_ctor_set(v___x_70_, 0, v___x_88_);
v___x_90_ = v___x_70_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_88_);
v___x_90_ = v_reuseFailAlloc_104_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_91_ = l_Lean_MessageData_ofFormat(v___x_90_);
v___x_92_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_87_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v___x_93_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_checkExp___closed__6, &l_Lean_Meta_Grind_Arith_checkExp___closed__6_once, _init_l_Lean_Meta_Grind_Arith_checkExp___closed__6);
v___x_94_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_92_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = l_Lean_Meta_Grind_reportIssue(v___x_94_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_dec_ref(v___x_95_);
goto v___jp_48_;
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_95_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_95_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_a_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
}
}
else
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
lean_del_object(v___x_74_);
lean_del_object(v___x_70_);
lean_dec(v_k_37_);
v_a_106_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___x_77_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_77_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
lean_dec(v_k_37_);
v_a_116_ = lean_ctor_get(v___x_65_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___x_65_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_65_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
}
}
else
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
lean_dec(v_k_37_);
v_a_125_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_51_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_51_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
v___jp_48_:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_box(0);
v___x_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___boxed(lean_object* v_k_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Meta_Grind_Arith_checkExp(v_k_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
lean_dec(v_a_138_);
lean_dec_ref(v_a_137_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(lean_object* v_e_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_i_229_; lean_object* v_a_230_; lean_object* v___y_231_; lean_object* v___y_232_; lean_object* v___y_233_; lean_object* v___y_234_; lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___y_237_; lean_object* v___y_238_; lean_object* v___y_239_; lean_object* v___x_291_; 
lean_inc_ref(v_e_217_);
v___x_291_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_217_, v_a_224_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_662_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_662_ == 0)
{
v___x_294_ = v___x_291_;
v_isShared_295_ = v_isSharedCheck_662_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_662_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = l_Lean_Expr_cleanupAnnotations(v_a_292_);
v___x_302_ = l_Lean_Expr_isApp(v___x_301_);
if (v___x_302_ == 0)
{
lean_dec_ref(v___x_301_);
lean_dec_ref(v_e_217_);
goto v___jp_296_;
}
else
{
lean_object* v_arg_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v_arg_303_ = lean_ctor_get(v___x_301_, 1);
lean_inc_ref(v_arg_303_);
v___x_304_ = l_Lean_Expr_appFnCleanup___redArg(v___x_301_);
v___x_305_ = l_Lean_Expr_isApp(v___x_304_);
if (v___x_305_ == 0)
{
lean_dec_ref(v___x_304_);
lean_dec_ref(v_arg_303_);
lean_dec_ref(v_e_217_);
goto v___jp_296_;
}
else
{
lean_object* v_arg_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_arg_306_ = lean_ctor_get(v___x_304_, 1);
lean_inc_ref(v_arg_306_);
v___x_307_ = l_Lean_Expr_appFnCleanup___redArg(v___x_304_);
v___x_308_ = l_Lean_Expr_isApp(v___x_307_);
if (v___x_308_ == 0)
{
lean_dec_ref(v___x_307_);
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
lean_dec_ref(v_e_217_);
goto v___jp_296_;
}
else
{
lean_object* v_arg_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v_arg_309_ = lean_ctor_get(v___x_307_, 1);
lean_inc_ref(v_arg_309_);
v___x_310_ = l_Lean_Expr_appFnCleanup___redArg(v___x_307_);
v___x_311_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3));
v___x_312_ = l_Lean_Expr_isConstOf(v___x_310_, v___x_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_313_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6));
v___x_314_ = l_Lean_Expr_isConstOf(v___x_310_, v___x_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12));
v___x_316_ = l_Lean_Expr_isConstOf(v___x_310_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; uint8_t v___x_318_; 
lean_dec_ref(v_e_217_);
v___x_317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9));
v___x_318_ = l_Lean_Expr_isConstOf(v___x_310_, v___x_317_);
if (v___x_318_ == 0)
{
uint8_t v___x_319_; 
v___x_319_ = l_Lean_Expr_isApp(v___x_310_);
if (v___x_319_ == 0)
{
lean_dec_ref(v___x_310_);
lean_dec_ref(v_arg_309_);
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
goto v___jp_296_;
}
else
{
lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_320_ = l_Lean_Expr_appFnCleanup___redArg(v___x_310_);
v___x_321_ = l_Lean_Expr_isApp(v___x_320_);
if (v___x_321_ == 0)
{
lean_dec_ref(v___x_320_);
lean_dec_ref(v_arg_309_);
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
goto v___jp_296_;
}
else
{
lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_322_ = l_Lean_Expr_appFnCleanup___redArg(v___x_320_);
v___x_323_ = l_Lean_Expr_isApp(v___x_322_);
if (v___x_323_ == 0)
{
lean_dec_ref(v___x_322_);
lean_dec_ref(v_arg_309_);
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
goto v___jp_296_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_324_ = l_Lean_Expr_appFnCleanup___redArg(v___x_322_);
v___x_325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15));
v___x_326_ = l_Lean_Expr_isConstOf(v___x_324_, v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18));
v___x_328_ = l_Lean_Expr_isConstOf(v___x_324_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21));
v___x_330_ = l_Lean_Expr_isConstOf(v___x_324_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27));
v___x_332_ = l_Lean_Expr_isConstOf(v___x_324_, v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24));
v___x_334_ = l_Lean_Expr_isConstOf(v___x_324_, v___x_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30));
v___x_336_ = l_Lean_Expr_isConstOf(v___x_324_, v___x_335_);
lean_dec_ref(v___x_324_);
if (v___x_336_ == 0)
{
lean_dec_ref(v_arg_309_);
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
goto v___jp_296_;
}
else
{
lean_object* v___x_337_; 
lean_del_object(v___x_294_);
v___x_337_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_309_, v_a_224_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_369_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_369_ == 0)
{
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_369_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_369_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
uint8_t v___x_342_; 
v___x_342_ = lean_unbox(v_a_338_);
lean_dec(v_a_338_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_345_; 
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
v___x_343_ = lean_box(0);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_343_);
v___x_345_ = v___x_340_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
else
{
lean_object* v___x_347_; 
lean_del_object(v___x_340_);
v___x_347_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_306_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
if (lean_obj_tag(v_a_348_) == 0)
{
lean_dec_ref(v_arg_303_);
return v___x_347_;
}
else
{
lean_object* v_val_349_; lean_object* v___x_350_; 
lean_dec_ref(v___x_347_);
v_val_349_ = lean_ctor_get(v_a_348_, 0);
lean_inc(v_val_349_);
lean_dec_ref(v_a_348_);
v___x_350_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_303_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_a_351_);
if (lean_obj_tag(v_a_351_) == 0)
{
lean_dec(v_val_349_);
return v___x_350_;
}
else
{
lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_367_; 
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_367_ == 0)
{
lean_object* v_unused_368_; 
v_unused_368_ = lean_ctor_get(v___x_350_, 0);
lean_dec(v_unused_368_);
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_367_;
goto v_resetjp_352_;
}
else
{
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_367_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v_val_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_366_; 
v_val_355_ = lean_ctor_get(v_a_351_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v_a_351_);
if (v_isSharedCheck_366_ == 0)
{
v___x_357_ = v_a_351_;
v_isShared_358_ = v_isSharedCheck_366_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_val_355_);
lean_dec(v_a_351_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_366_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_359_ = lean_int_add(v_val_349_, v_val_355_);
lean_dec(v_val_355_);
lean_dec(v_val_349_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_359_);
v___x_361_ = v___x_357_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_365_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_363_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_361_);
v___x_363_ = v___x_353_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
}
else
{
lean_dec(v_val_349_);
return v___x_350_;
}
}
}
else
{
lean_dec_ref(v_arg_303_);
return v___x_347_;
}
}
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
v_a_370_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_337_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_337_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
else
{
lean_object* v___x_378_; 
lean_dec_ref(v___x_324_);
lean_del_object(v___x_294_);
v___x_378_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_arg_309_, v_a_224_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_410_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_410_ == 0)
{
v___x_381_ = v___x_378_;
v_isShared_382_ = v_isSharedCheck_410_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_378_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_410_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
uint8_t v___x_383_; 
v___x_383_ = lean_unbox(v_a_379_);
lean_dec(v_a_379_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; lean_object* v___x_386_; 
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
v___x_384_ = lean_box(0);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_384_);
v___x_386_ = v___x_381_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
else
{
lean_object* v___x_388_; 
lean_del_object(v___x_381_);
v___x_388_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_306_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
if (lean_obj_tag(v_a_389_) == 0)
{
lean_dec_ref(v_arg_303_);
return v___x_388_;
}
else
{
lean_object* v_val_390_; lean_object* v___x_391_; 
lean_dec_ref(v___x_388_);
v_val_390_ = lean_ctor_get(v_a_389_, 0);
lean_inc(v_val_390_);
lean_dec_ref(v_a_389_);
v___x_391_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_303_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_a_392_);
if (lean_obj_tag(v_a_392_) == 0)
{
lean_dec(v_val_390_);
return v___x_391_;
}
else
{
lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_408_; 
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; 
v_unused_409_ = lean_ctor_get(v___x_391_, 0);
lean_dec(v_unused_409_);
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_408_;
goto v_resetjp_393_;
}
else
{
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_408_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v_val_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_407_; 
v_val_396_ = lean_ctor_get(v_a_392_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v_a_392_);
if (v_isSharedCheck_407_ == 0)
{
v___x_398_ = v_a_392_;
v_isShared_399_ = v_isSharedCheck_407_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_val_396_);
lean_dec(v_a_392_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_407_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_400_ = lean_int_sub(v_val_390_, v_val_396_);
lean_dec(v_val_396_);
lean_dec(v_val_390_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_400_);
v___x_402_ = v___x_398_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_406_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_404_; 
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_402_);
v___x_404_ = v___x_394_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
}
else
{
lean_dec(v_val_390_);
return v___x_391_;
}
}
}
else
{
lean_dec_ref(v_arg_303_);
return v___x_388_;
}
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
v_a_411_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_378_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_378_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
else
{
lean_object* v___x_419_; 
lean_dec_ref(v___x_324_);
lean_del_object(v___x_294_);
v___x_419_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_309_, v_a_224_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_451_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_451_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_451_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_451_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
uint8_t v___x_424_; 
v___x_424_ = lean_unbox(v_a_420_);
lean_dec(v_a_420_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_427_; 
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
v___x_425_ = lean_box(0);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_425_);
v___x_427_ = v___x_422_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
else
{
lean_object* v___x_429_; 
lean_del_object(v___x_422_);
v___x_429_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_306_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
if (lean_obj_tag(v_a_430_) == 0)
{
lean_dec_ref(v_arg_303_);
return v___x_429_;
}
else
{
lean_object* v_val_431_; lean_object* v___x_432_; 
lean_dec_ref(v___x_429_);
v_val_431_ = lean_ctor_get(v_a_430_, 0);
lean_inc(v_val_431_);
lean_dec_ref(v_a_430_);
v___x_432_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_303_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
if (lean_obj_tag(v_a_433_) == 0)
{
lean_dec(v_val_431_);
return v___x_432_;
}
else
{
lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_449_; 
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; 
v_unused_450_ = lean_ctor_get(v___x_432_, 0);
lean_dec(v_unused_450_);
v___x_435_ = v___x_432_;
v_isShared_436_ = v_isSharedCheck_449_;
goto v_resetjp_434_;
}
else
{
lean_dec(v___x_432_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_449_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v_val_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_448_; 
v_val_437_ = lean_ctor_get(v_a_433_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v_a_433_);
if (v_isSharedCheck_448_ == 0)
{
v___x_439_ = v_a_433_;
v_isShared_440_ = v_isSharedCheck_448_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_val_437_);
lean_dec(v_a_433_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_448_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_441_ = lean_int_mul(v_val_431_, v_val_437_);
lean_dec(v_val_437_);
lean_dec(v_val_431_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_441_);
v___x_443_ = v___x_439_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_447_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_445_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_443_);
v___x_445_ = v___x_435_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
}
}
}
else
{
lean_dec(v_val_431_);
return v___x_432_;
}
}
}
else
{
lean_dec_ref(v_arg_303_);
return v___x_429_;
}
}
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
v_a_452_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_419_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_419_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
}
else
{
lean_object* v___x_460_; 
lean_dec_ref(v___x_324_);
lean_del_object(v___x_294_);
v___x_460_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_arg_309_, v_a_224_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_492_; 
v_a_461_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_492_ == 0)
{
v___x_463_ = v___x_460_;
v_isShared_464_ = v_isSharedCheck_492_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_460_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_492_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
uint8_t v___x_465_; 
v___x_465_ = lean_unbox(v_a_461_);
lean_dec(v_a_461_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_468_; 
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
v___x_466_ = lean_box(0);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 0, v___x_466_);
v___x_468_ = v___x_463_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
else
{
lean_object* v___x_470_; 
lean_del_object(v___x_463_);
v___x_470_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_306_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
if (lean_obj_tag(v_a_471_) == 0)
{
lean_dec_ref(v_arg_303_);
return v___x_470_;
}
else
{
lean_object* v_val_472_; lean_object* v___x_473_; 
lean_dec_ref(v___x_470_);
v_val_472_ = lean_ctor_get(v_a_471_, 0);
lean_inc(v_val_472_);
lean_dec_ref(v_a_471_);
v___x_473_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_303_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_a_474_);
if (lean_obj_tag(v_a_474_) == 0)
{
lean_dec(v_val_472_);
return v___x_473_;
}
else
{
lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_490_; 
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_490_ == 0)
{
lean_object* v_unused_491_; 
v_unused_491_ = lean_ctor_get(v___x_473_, 0);
lean_dec(v_unused_491_);
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_490_;
goto v_resetjp_475_;
}
else
{
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_490_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v_val_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_489_; 
v_val_478_ = lean_ctor_get(v_a_474_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v_a_474_);
if (v_isSharedCheck_489_ == 0)
{
v___x_480_ = v_a_474_;
v_isShared_481_ = v_isSharedCheck_489_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_val_478_);
lean_dec(v_a_474_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_489_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_482_ = lean_int_ediv(v_val_472_, v_val_478_);
lean_dec(v_val_478_);
lean_dec(v_val_472_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_482_);
v___x_484_ = v___x_480_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_482_);
v___x_484_ = v_reuseFailAlloc_488_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_486_; 
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_484_);
v___x_486_ = v___x_476_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
}
else
{
lean_dec(v_val_472_);
return v___x_473_;
}
}
}
else
{
lean_dec_ref(v_arg_303_);
return v___x_470_;
}
}
}
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
v_a_493_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_460_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_460_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
}
else
{
lean_object* v___x_501_; 
lean_dec_ref(v___x_324_);
lean_del_object(v___x_294_);
v___x_501_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_arg_309_, v_a_224_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_533_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_533_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_533_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_533_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
uint8_t v___x_506_; 
v___x_506_ = lean_unbox(v_a_502_);
lean_dec(v_a_502_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_509_; 
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
v___x_507_ = lean_box(0);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_507_);
v___x_509_ = v___x_504_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
else
{
lean_object* v___x_511_; 
lean_del_object(v___x_504_);
v___x_511_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_306_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
if (lean_obj_tag(v_a_512_) == 0)
{
lean_dec_ref(v_arg_303_);
return v___x_511_;
}
else
{
lean_object* v_val_513_; lean_object* v___x_514_; 
lean_dec_ref(v___x_511_);
v_val_513_ = lean_ctor_get(v_a_512_, 0);
lean_inc(v_val_513_);
lean_dec_ref(v_a_512_);
v___x_514_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_303_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
if (lean_obj_tag(v_a_515_) == 0)
{
lean_dec(v_val_513_);
return v___x_514_;
}
else
{
lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_531_; 
v_isSharedCheck_531_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_531_ == 0)
{
lean_object* v_unused_532_; 
v_unused_532_ = lean_ctor_get(v___x_514_, 0);
lean_dec(v_unused_532_);
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_531_;
goto v_resetjp_516_;
}
else
{
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_531_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v_val_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_530_; 
v_val_519_ = lean_ctor_get(v_a_515_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v_a_515_);
if (v_isSharedCheck_530_ == 0)
{
v___x_521_ = v_a_515_;
v_isShared_522_ = v_isSharedCheck_530_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_val_519_);
lean_dec(v_a_515_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_530_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_523_ = lean_int_emod(v_val_513_, v_val_519_);
lean_dec(v_val_519_);
lean_dec(v_val_513_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_523_);
v___x_525_ = v___x_521_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_529_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_527_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_525_);
v___x_527_ = v___x_517_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
}
else
{
lean_dec(v_val_513_);
return v___x_514_;
}
}
}
else
{
lean_dec_ref(v_arg_303_);
return v___x_511_;
}
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
v_a_534_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_501_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_501_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
else
{
lean_object* v___x_542_; 
lean_dec_ref(v___x_324_);
lean_del_object(v___x_294_);
v___x_542_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_arg_309_, v_a_224_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_604_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_604_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_604_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_604_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
uint8_t v___x_547_; 
v___x_547_ = lean_unbox(v_a_543_);
lean_dec(v_a_543_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_550_; 
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
v___x_548_ = lean_box(0);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_548_);
v___x_550_ = v___x_545_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
else
{
lean_object* v___x_552_; 
lean_del_object(v___x_545_);
v___x_552_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_306_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
if (lean_obj_tag(v_a_553_) == 0)
{
lean_dec_ref(v_arg_303_);
return v___x_552_;
}
else
{
lean_object* v_val_554_; lean_object* v___x_555_; 
lean_dec_ref(v___x_552_);
v_val_554_ = lean_ctor_get(v_a_553_, 0);
lean_inc(v_val_554_);
lean_dec_ref(v_a_553_);
v___x_555_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_303_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_595_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_595_ == 0)
{
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_595_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_595_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
if (lean_obj_tag(v_a_556_) == 0)
{
lean_object* v___x_560_; lean_object* v___x_562_; 
lean_dec(v_val_554_);
v___x_560_ = lean_box(0);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_560_);
v___x_562_ = v___x_558_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
else
{
lean_object* v_val_564_; lean_object* v___x_565_; 
lean_del_object(v___x_558_);
v_val_564_ = lean_ctor_get(v_a_556_, 0);
lean_inc(v_val_564_);
lean_dec_ref(v_a_556_);
lean_inc(v_val_564_);
v___x_565_ = l_Lean_Meta_Grind_Arith_checkExp(v_val_564_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_586_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_586_ == 0)
{
v___x_568_ = v___x_565_;
v_isShared_569_ = v_isSharedCheck_586_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_565_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_586_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
if (lean_obj_tag(v_a_566_) == 0)
{
lean_object* v___x_570_; lean_object* v___x_572_; 
lean_dec(v_val_564_);
lean_dec(v_val_554_);
v___x_570_ = lean_box(0);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v___x_570_);
v___x_572_ = v___x_568_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
else
{
lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_584_; 
v_isSharedCheck_584_ = !lean_is_exclusive(v_a_566_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; 
v_unused_585_ = lean_ctor_get(v_a_566_, 0);
lean_dec(v_unused_585_);
v___x_575_ = v_a_566_;
v_isShared_576_ = v_isSharedCheck_584_;
goto v_resetjp_574_;
}
else
{
lean_dec(v_a_566_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_584_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; lean_object* v___x_579_; 
v___x_577_ = l_Int_pow(v_val_554_, v_val_564_);
lean_dec(v_val_564_);
lean_dec(v_val_554_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_577_);
v___x_579_ = v___x_575_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_583_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_581_; 
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v___x_579_);
v___x_581_ = v___x_568_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_dec(v_val_564_);
lean_dec(v_val_554_);
v_a_587_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_565_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_565_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec(v_val_554_);
v_a_596_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_555_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_555_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_303_);
return v___x_552_;
}
}
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
v_a_605_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_542_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_542_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
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
lean_object* v___x_613_; 
lean_dec_ref(v___x_310_);
lean_dec_ref(v_arg_309_);
lean_del_object(v___x_294_);
v___x_613_ = l_Lean_Meta_Structural_isInstNegInt___redArg(v_arg_306_, v_a_224_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_642_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_642_ == 0)
{
v___x_616_ = v___x_613_;
v_isShared_617_ = v_isSharedCheck_642_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_613_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_642_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
uint8_t v___x_618_; 
v___x_618_ = lean_unbox(v_a_614_);
lean_dec(v_a_614_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; lean_object* v___x_621_; 
lean_dec_ref(v_arg_303_);
v___x_619_ = lean_box(0);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_619_);
v___x_621_ = v___x_616_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
else
{
lean_object* v___x_623_; 
lean_del_object(v___x_616_);
v___x_623_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_303_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_624_);
if (lean_obj_tag(v_a_624_) == 0)
{
return v___x_623_;
}
else
{
lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_640_; 
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; 
v_unused_641_ = lean_ctor_get(v___x_623_, 0);
lean_dec(v_unused_641_);
v___x_626_ = v___x_623_;
v_isShared_627_ = v_isSharedCheck_640_;
goto v_resetjp_625_;
}
else
{
lean_dec(v___x_623_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_640_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v_val_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_639_; 
v_val_628_ = lean_ctor_get(v_a_624_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v_a_624_);
if (v_isSharedCheck_639_ == 0)
{
v___x_630_ = v_a_624_;
v_isShared_631_ = v_isSharedCheck_639_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_val_628_);
lean_dec(v_a_624_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_639_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_632_ = lean_int_neg(v_val_628_);
lean_dec(v_val_628_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_632_);
v___x_634_ = v___x_630_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_632_);
v___x_634_ = v_reuseFailAlloc_638_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_636_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_634_);
v___x_636_ = v___x_626_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
}
}
else
{
return v___x_623_;
}
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec_ref(v_arg_303_);
v_a_643_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_613_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_613_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
else
{
lean_object* v___x_651_; 
lean_dec_ref(v___x_310_);
lean_dec_ref(v_arg_309_);
lean_dec_ref(v_arg_306_);
lean_dec_ref(v_arg_303_);
lean_del_object(v___x_294_);
v___x_651_ = l_Lean_Meta_getIntValue_x3f(v_e_217_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
if (lean_obj_tag(v_a_652_) == 1)
{
lean_dec_ref(v_a_652_);
return v___x_651_;
}
else
{
lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_660_; 
lean_dec(v_a_652_);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_660_ == 0)
{
lean_object* v_unused_661_; 
v_unused_661_ = lean_ctor_get(v___x_651_, 0);
lean_dec(v_unused_661_);
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
else
{
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_656_ = lean_box(0);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_656_);
v___x_658_ = v___x_654_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
else
{
return v___x_651_;
}
}
}
else
{
lean_dec_ref(v___x_310_);
lean_dec_ref(v_arg_309_);
lean_del_object(v___x_294_);
lean_dec_ref(v_e_217_);
v_i_229_ = v_arg_306_;
v_a_230_ = v_arg_303_;
v___y_231_ = v_a_218_;
v___y_232_ = v_a_219_;
v___y_233_ = v_a_220_;
v___y_234_ = v_a_221_;
v___y_235_ = v_a_222_;
v___y_236_ = v_a_223_;
v___y_237_ = v_a_224_;
v___y_238_ = v_a_225_;
v___y_239_ = v_a_226_;
goto v___jp_228_;
}
}
else
{
lean_dec_ref(v___x_310_);
lean_dec_ref(v_arg_309_);
lean_del_object(v___x_294_);
lean_dec_ref(v_e_217_);
v_i_229_ = v_arg_306_;
v_a_230_ = v_arg_303_;
v___y_231_ = v_a_218_;
v___y_232_ = v_a_219_;
v___y_233_ = v_a_220_;
v___y_234_ = v_a_221_;
v___y_235_ = v_a_222_;
v___y_236_ = v_a_223_;
v___y_237_ = v_a_224_;
v___y_238_ = v_a_225_;
v___y_239_ = v_a_226_;
goto v___jp_228_;
}
}
}
}
v___jp_296_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_box(0);
if (v_isShared_295_ == 0)
{
lean_ctor_set(v___x_294_, 0, v___x_297_);
v___x_299_ = v___x_294_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec_ref(v_e_217_);
v_a_663_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_291_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_291_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
v___jp_228_:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_i_229_, v___y_237_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_282_; 
v_a_241_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_282_ == 0)
{
v___x_243_ = v___x_240_;
v_isShared_244_ = v_isSharedCheck_282_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_240_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_282_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_245_ = l_Lean_Expr_cleanupAnnotations(v_a_241_);
v___x_246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1));
v___x_247_ = l_Lean_Expr_isConstOf(v___x_245_, v___x_246_);
lean_dec_ref(v___x_245_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; lean_object* v___x_250_; 
lean_dec_ref(v_a_230_);
v___x_248_ = lean_box(0);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_248_);
v___x_250_ = v___x_243_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
else
{
lean_object* v___x_252_; 
lean_del_object(v___x_243_);
v___x_252_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_a_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_273_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_273_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_273_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_273_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
if (lean_obj_tag(v_a_253_) == 0)
{
lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_257_ = lean_box(0);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v___x_257_);
v___x_259_ = v___x_255_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
else
{
lean_object* v_val_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_272_; 
v_val_261_ = lean_ctor_get(v_a_253_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v_a_253_);
if (v_isSharedCheck_272_ == 0)
{
v___x_263_ = v_a_253_;
v_isShared_264_ = v_isSharedCheck_272_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_val_261_);
lean_dec(v_a_253_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_272_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_265_ = lean_nat_to_int(v_val_261_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v___x_265_);
v___x_267_ = v___x_263_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_265_);
v___x_267_ = v_reuseFailAlloc_271_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_269_; 
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 0, v___x_267_);
v___x_269_ = v___x_255_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
v_a_274_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_252_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_252_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_dec_ref(v_a_230_);
v_a_283_ = lean_ctor_get(v___x_240_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_240_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_240_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_240_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(lean_object* v_e_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v___x_685_; 
lean_inc_ref(v_e_671_);
v___x_685_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_671_, v_a_678_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_1087_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_1087_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_1087_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_690_ = l_Lean_Expr_cleanupAnnotations(v_a_686_);
v___x_691_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2));
v___x_692_ = l_Lean_Expr_isConstOf(v___x_690_, v___x_691_);
if (v___x_692_ == 0)
{
uint8_t v___x_693_; 
lean_del_object(v___x_688_);
v___x_693_ = l_Lean_Expr_isApp(v___x_690_);
if (v___x_693_ == 0)
{
lean_dec_ref(v___x_690_);
lean_dec_ref(v_e_671_);
goto v___jp_682_;
}
else
{
lean_object* v_arg_694_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v_arg_694_ = lean_ctor_get(v___x_690_, 1);
lean_inc_ref(v_arg_694_);
v___x_695_ = l_Lean_Expr_appFnCleanup___redArg(v___x_690_);
v___x_696_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5));
v___x_697_ = l_Lean_Expr_isConstOf(v___x_695_, v___x_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_698_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7));
v___x_699_ = l_Lean_Expr_isConstOf(v___x_695_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9));
v___x_701_ = l_Lean_Expr_isConstOf(v___x_695_, v___x_700_);
if (v___x_701_ == 0)
{
uint8_t v___x_702_; 
v___x_702_ = l_Lean_Expr_isApp(v___x_695_);
if (v___x_702_ == 0)
{
lean_dec_ref(v___x_695_);
lean_dec_ref(v_arg_694_);
lean_dec_ref(v_e_671_);
goto v___jp_682_;
}
else
{
lean_object* v_arg_703_; lean_object* v___x_704_; uint8_t v___x_705_; 
v_arg_703_ = lean_ctor_get(v___x_695_, 1);
lean_inc_ref(v_arg_703_);
v___x_704_ = l_Lean_Expr_appFnCleanup___redArg(v___x_695_);
v___x_705_ = l_Lean_Expr_isApp(v___x_704_);
if (v___x_705_ == 0)
{
lean_dec_ref(v___x_704_);
lean_dec_ref(v_arg_703_);
lean_dec_ref(v_arg_694_);
lean_dec_ref(v_e_671_);
goto v___jp_682_;
}
else
{
lean_object* v_arg_706_; lean_object* v___x_707_; lean_object* v___x_708_; uint8_t v___x_709_; 
v_arg_706_ = lean_ctor_get(v___x_704_, 1);
lean_inc_ref(v_arg_706_);
v___x_707_ = l_Lean_Expr_appFnCleanup___redArg(v___x_704_);
v___x_708_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12));
v___x_709_ = l_Lean_Expr_isConstOf(v___x_707_, v___x_708_);
if (v___x_709_ == 0)
{
uint8_t v___x_710_; 
lean_dec_ref(v_e_671_);
v___x_710_ = l_Lean_Expr_isApp(v___x_707_);
if (v___x_710_ == 0)
{
lean_dec_ref(v___x_707_);
lean_dec_ref(v_arg_706_);
lean_dec_ref(v_arg_703_);
lean_dec_ref(v_arg_694_);
goto v___jp_682_;
}
else
{
lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_711_ = l_Lean_Expr_appFnCleanup___redArg(v___x_707_);
v___x_712_ = l_Lean_Expr_isApp(v___x_711_);
if (v___x_712_ == 0)
{
lean_dec_ref(v___x_711_);
lean_dec_ref(v_arg_706_);
lean_dec_ref(v_arg_703_);
lean_dec_ref(v_arg_694_);
goto v___jp_682_;
}
else
{
lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_713_ = l_Lean_Expr_appFnCleanup___redArg(v___x_711_);
v___x_714_ = l_Lean_Expr_isApp(v___x_713_);
if (v___x_714_ == 0)
{
lean_dec_ref(v___x_713_);
lean_dec_ref(v_arg_706_);
lean_dec_ref(v_arg_703_);
lean_dec_ref(v_arg_694_);
goto v___jp_682_;
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_715_ = l_Lean_Expr_appFnCleanup___redArg(v___x_713_);
v___x_716_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15));
v___x_717_ = l_Lean_Expr_isConstOf(v___x_715_, v___x_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18));
v___x_719_ = l_Lean_Expr_isConstOf(v___x_715_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_720_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21));
v___x_721_ = l_Lean_Expr_isConstOf(v___x_715_, v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; uint8_t v___x_723_; 
v___x_722_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24));
v___x_723_ = l_Lean_Expr_isConstOf(v___x_715_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_724_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27));
v___x_725_ = l_Lean_Expr_isConstOf(v___x_715_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30));
v___x_727_ = l_Lean_Expr_isConstOf(v___x_715_, v___x_726_);
lean_dec_ref(v___x_715_);
if (v___x_727_ == 0)
{
lean_dec_ref(v_arg_706_);
lean_dec_ref(v_arg_703_);
lean_dec_ref(v_arg_694_);
goto v___jp_682_;
}
else
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_706_, v_a_678_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_760_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_760_ == 0)
{
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_760_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_760_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
uint8_t v___x_733_; 
v___x_733_ = lean_unbox(v_a_729_);
lean_dec(v_a_729_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_736_; 
lean_dec_ref(v_arg_703_);
lean_dec_ref(v_arg_694_);
v___x_734_ = lean_box(0);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_734_);
v___x_736_ = v___x_731_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
else
{
lean_object* v___x_738_; 
lean_del_object(v___x_731_);
v___x_738_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_703_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
if (lean_obj_tag(v_a_739_) == 0)
{
lean_dec_ref(v_arg_694_);
return v___x_738_;
}
else
{
lean_object* v_val_740_; lean_object* v___x_741_; 
lean_dec_ref(v___x_738_);
v_val_740_ = lean_ctor_get(v_a_739_, 0);
lean_inc(v_val_740_);
lean_dec_ref(v_a_739_);
v___x_741_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_694_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
if (lean_obj_tag(v_a_742_) == 0)
{
lean_dec(v_val_740_);
return v___x_741_;
}
else
{
lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_758_; 
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; 
v_unused_759_ = lean_ctor_get(v___x_741_, 0);
lean_dec(v_unused_759_);
v___x_744_ = v___x_741_;
v_isShared_745_ = v_isSharedCheck_758_;
goto v_resetjp_743_;
}
else
{
lean_dec(v___x_741_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_758_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v_val_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_757_; 
v_val_746_ = lean_ctor_get(v_a_742_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v_a_742_);
if (v_isSharedCheck_757_ == 0)
{
v___x_748_ = v_a_742_;
v_isShared_749_ = v_isSharedCheck_757_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_val_746_);
lean_dec(v_a_742_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_757_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = lean_nat_add(v_val_740_, v_val_746_);
lean_dec(v_val_746_);
lean_dec(v_val_740_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 0, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_750_);
v___x_752_ = v_reuseFailAlloc_756_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_754_; 
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_752_);
v___x_754_ = v___x_744_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
}
else
{
lean_dec(v_val_740_);
return v___x_741_;
}
}
}
else
{
lean_dec_ref(v_arg_694_);
return v___x_738_;
}
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec_ref(v_arg_703_);
lean_dec_ref(v_arg_694_);
v_a_761_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_728_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_728_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
else
{
lean_object* v___x_769_; 
lean_dec_ref(v___x_715_);
v___x_769_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_arg_706_, v_a_678_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_801_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_801_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_801_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_801_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
uint8_t v___x_774_; 
v___x_774_ = lean_unbox(v_a_770_);
lean_dec(v_a_770_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; lean_object* v___x_777_; 
lean_dec_ref(v_arg_703_);
lean_dec_ref(v_arg_694_);
v___x_775_ = lean_box(0);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_775_);
v___x_777_ = v___x_772_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
else
{
lean_object* v___x_779_; 
lean_del_object(v___x_772_);
v___x_779_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_703_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
if (lean_obj_tag(v_a_780_) == 0)
{
lean_dec_ref(v_arg_694_);
return v___x_779_;
}
else
{
lean_object* v_val_781_; lean_object* v___x_782_; 
lean_dec_ref(v___x_779_);
v_val_781_ = lean_ctor_get(v_a_780_, 0);
lean_inc(v_val_781_);
lean_dec_ref(v_a_780_);
v___x_782_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_694_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
if (lean_obj_tag(v_a_783_) == 0)
{
lean_dec(v_val_781_);
return v___x_782_;
}
else
{
lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_799_; 
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_799_ == 0)
{
lean_object* v_unused_800_; 
v_unused_800_ = lean_ctor_get(v___x_782_, 0);
lean_dec(v_unused_800_);
v___x_785_ = v___x_782_;
v_isShared_786_ = v_isSharedCheck_799_;
goto v_resetjp_784_;
}
else
{
lean_dec(v___x_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_799_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v_val_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_798_; 
v_val_787_ = lean_ctor_get(v_a_783_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v_a_783_);
if (v_isSharedCheck_798_ == 0)
{
v___x_789_ = v_a_783_;
v_isShared_790_ = v_isSharedCheck_798_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_val_787_);
lean_dec(v_a_783_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_798_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_791_ = lean_nat_mul(v_val_781_, v_val_787_);
lean_dec(v_val_787_);
lean_dec(v_val_781_);
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_791_);
v___x_793_ = v___x_789_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_797_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_795_; 
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_793_);
v___x_795_ = v___x_785_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
}
else
{
lean_dec(v_val_781_);
return v___x_782_;
}
}
}
else
{
lean_dec_ref(v_arg_694_);
return v___x_779_;
}
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_dec_ref(v_arg_703_);
lean_dec_ref(v_arg_694_);
v_a_802_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_769_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_769_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
else
{
lean_object* v___x_810_; 
lean_dec_ref(v___x_715_);
v___x_810_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_arg_706_, v_a_678_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_842_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_842_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_842_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_842_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
uint8_t v___x_815_; 
v___x_815_ = lean_unbox(v_a_811_);
lean_dec(v_a_811_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; lean_object* v___x_818_; 
lean_dec_ref(v_arg_703_);
lean_dec_ref(v_arg_694_);
v___x_816_ = lean_box(0);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 0, v___x_816_);
v___x_818_ = v___x_813_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
else
{
lean_object* v___x_820_; 
lean_del_object(v___x_813_);
v___x_820_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_703_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
if (lean_obj_tag(v_a_821_) == 0)
{
lean_dec_ref(v_arg_694_);
return v___x_820_;
}
else
{
lean_object* v_val_822_; lean_object* v___x_823_; 
lean_dec_ref(v___x_820_);
v_val_822_ = lean_ctor_get(v_a_821_, 0);
lean_inc(v_val_822_);
lean_dec_ref(v_a_821_);
v___x_823_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_694_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
if (lean_obj_tag(v_a_824_) == 0)
{
lean_dec(v_val_822_);
return v___x_823_;
}
else
{
lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_840_; 
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_840_ == 0)
{
lean_object* v_unused_841_; 
v_unused_841_ = lean_ctor_get(v___x_823_, 0);
lean_dec(v_unused_841_);
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_840_;
goto v_resetjp_825_;
}
else
{
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_840_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v_val_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_839_; 
v_val_828_ = lean_ctor_get(v_a_824_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v_a_824_);
if (v_isSharedCheck_839_ == 0)
{
v___x_830_ = v_a_824_;
v_isShared_831_ = v_isSharedCheck_839_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_val_828_);
lean_dec(v_a_824_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_839_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_832_ = lean_nat_sub(v_val_822_, v_val_828_);
lean_dec(v_val_828_);
lean_dec(v_val_822_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_832_);
v___x_834_ = v___x_830_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_838_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
lean_object* v___x_836_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_834_);
v___x_836_ = v___x_826_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
}
else
{
lean_dec(v_val_822_);
return v___x_823_;
}
}
}
else
{
lean_dec_ref(v_arg_694_);
return v___x_820_;
}
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec_ref(v_arg_703_);
lean_dec_ref(v_arg_694_);
v_a_843_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_810_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_810_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
else
{
lean_object* v___x_851_; 
lean_dec_ref(v___x_715_);
v___x_851_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_arg_706_, v_a_678_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_883_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_883_ == 0)
{
v___x_854_ = v___x_851_;
v_isShared_855_ = v_isSharedCheck_883_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_851_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_883_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
uint8_t v___x_856_; 
v___x_856_ = lean_unbox(v_a_852_);
lean_dec(v_a_852_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_859_; 
lean_dec_ref(v_arg_703_);
lean_dec_ref(v_arg_694_);
v___x_857_ = lean_box(0);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_857_);
v___x_859_ = v___x_854_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
else
{
lean_object* v___x_861_; 
lean_del_object(v___x_854_);
v___x_861_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_703_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
if (lean_obj_tag(v_a_862_) == 0)
{
lean_dec_ref(v_arg_694_);
return v___x_861_;
}
else
{
lean_object* v_val_863_; lean_object* v___x_864_; 
lean_dec_ref(v___x_861_);
v_val_863_ = lean_ctor_get(v_a_862_, 0);
lean_inc(v_val_863_);
lean_dec_ref(v_a_862_);
v___x_864_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_694_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
if (lean_obj_tag(v_a_865_) == 0)
{
lean_dec(v_val_863_);
return v___x_864_;
}
else
{
lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_881_; 
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_881_ == 0)
{
lean_object* v_unused_882_; 
v_unused_882_ = lean_ctor_get(v___x_864_, 0);
lean_dec(v_unused_882_);
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_881_;
goto v_resetjp_866_;
}
else
{
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_881_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v_val_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_880_; 
v_val_869_ = lean_ctor_get(v_a_865_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v_a_865_);
if (v_isSharedCheck_880_ == 0)
{
v___x_871_ = v_a_865_;
v_isShared_872_ = v_isSharedCheck_880_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_val_869_);
lean_dec(v_a_865_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_880_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_873_ = lean_nat_div(v_val_863_, v_val_869_);
lean_dec(v_val_869_);
lean_dec(v_val_863_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_873_);
v___x_875_ = v___x_871_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_873_);
v___x_875_ = v_reuseFailAlloc_879_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
lean_object* v___x_877_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_875_);
v___x_877_ = v___x_867_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
}
else
{
lean_dec(v_val_863_);
return v___x_864_;
}
}
}
else
{
lean_dec_ref(v_arg_694_);
return v___x_861_;
}
}
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec_ref(v_arg_703_);
lean_dec_ref(v_arg_694_);
v_a_884_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_851_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_851_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
else
{
lean_object* v___x_892_; 
lean_dec_ref(v___x_715_);
v___x_892_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_arg_706_, v_a_678_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_924_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_924_ == 0)
{
v___x_895_ = v___x_892_;
v_isShared_896_ = v_isSharedCheck_924_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_924_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
uint8_t v___x_897_; 
v___x_897_ = lean_unbox(v_a_893_);
lean_dec(v_a_893_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___x_900_; 
lean_dec_ref(v_arg_703_);
lean_dec_ref(v_arg_694_);
v___x_898_ = lean_box(0);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 0, v___x_898_);
v___x_900_ = v___x_895_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
else
{
lean_object* v___x_902_; 
lean_del_object(v___x_895_);
v___x_902_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_703_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
if (lean_obj_tag(v_a_903_) == 0)
{
lean_dec_ref(v_arg_694_);
return v___x_902_;
}
else
{
lean_object* v_val_904_; lean_object* v___x_905_; 
lean_dec_ref(v___x_902_);
v_val_904_ = lean_ctor_get(v_a_903_, 0);
lean_inc(v_val_904_);
lean_dec_ref(v_a_903_);
v___x_905_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_694_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_906_);
if (lean_obj_tag(v_a_906_) == 0)
{
lean_dec(v_val_904_);
return v___x_905_;
}
else
{
lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_922_; 
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; 
v_unused_923_ = lean_ctor_get(v___x_905_, 0);
lean_dec(v_unused_923_);
v___x_908_ = v___x_905_;
v_isShared_909_ = v_isSharedCheck_922_;
goto v_resetjp_907_;
}
else
{
lean_dec(v___x_905_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_922_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v_val_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_921_; 
v_val_910_ = lean_ctor_get(v_a_906_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v_a_906_);
if (v_isSharedCheck_921_ == 0)
{
v___x_912_ = v_a_906_;
v_isShared_913_ = v_isSharedCheck_921_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_val_910_);
lean_dec(v_a_906_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_921_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_914_ = lean_nat_mod(v_val_904_, v_val_910_);
lean_dec(v_val_910_);
lean_dec(v_val_904_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_914_);
v___x_916_ = v___x_912_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_920_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_918_; 
if (v_isShared_909_ == 0)
{
lean_ctor_set(v___x_908_, 0, v___x_916_);
v___x_918_ = v___x_908_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
}
else
{
lean_dec(v_val_904_);
return v___x_905_;
}
}
}
else
{
lean_dec_ref(v_arg_694_);
return v___x_902_;
}
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v_arg_703_);
lean_dec_ref(v_arg_694_);
v_a_925_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_892_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_892_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
else
{
lean_object* v___x_933_; 
lean_dec_ref(v___x_715_);
v___x_933_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_arg_706_, v_a_678_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_983_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_983_ == 0)
{
v___x_936_ = v___x_933_;
v_isShared_937_ = v_isSharedCheck_983_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_933_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_983_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
uint8_t v___x_938_; 
v___x_938_ = lean_unbox(v_a_934_);
lean_dec(v_a_934_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; lean_object* v___x_941_; 
lean_dec_ref(v_arg_703_);
lean_dec_ref(v_arg_694_);
v___x_939_ = lean_box(0);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_939_);
v___x_941_ = v___x_936_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
else
{
lean_object* v___x_943_; 
lean_del_object(v___x_936_);
v___x_943_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_694_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_a_944_);
if (lean_obj_tag(v_a_944_) == 0)
{
lean_dec_ref(v_arg_703_);
return v___x_943_;
}
else
{
lean_object* v_val_945_; lean_object* v___x_946_; 
lean_dec_ref(v___x_943_);
v_val_945_ = lean_ctor_get(v_a_944_, 0);
lean_inc(v_val_945_);
lean_dec_ref(v_a_944_);
lean_inc(v_val_945_);
v___x_946_ = l_Lean_Meta_Grind_Arith_checkExp(v_val_945_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_974_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_974_ == 0)
{
v___x_949_ = v___x_946_;
v_isShared_950_ = v_isSharedCheck_974_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_946_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_974_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
if (lean_obj_tag(v_a_947_) == 0)
{
lean_object* v___x_951_; lean_object* v___x_953_; 
lean_dec(v_val_945_);
lean_dec_ref(v_arg_703_);
v___x_951_ = lean_box(0);
if (v_isShared_950_ == 0)
{
lean_ctor_set(v___x_949_, 0, v___x_951_);
v___x_953_ = v___x_949_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
else
{
lean_object* v___x_955_; 
lean_dec_ref(v_a_947_);
lean_del_object(v___x_949_);
v___x_955_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_703_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
if (lean_obj_tag(v_a_956_) == 0)
{
lean_dec(v_val_945_);
return v___x_955_;
}
else
{
lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_972_; 
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_972_ == 0)
{
lean_object* v_unused_973_; 
v_unused_973_ = lean_ctor_get(v___x_955_, 0);
lean_dec(v_unused_973_);
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_972_;
goto v_resetjp_957_;
}
else
{
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_972_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v_val_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_971_; 
v_val_960_ = lean_ctor_get(v_a_956_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v_a_956_);
if (v_isSharedCheck_971_ == 0)
{
v___x_962_ = v_a_956_;
v_isShared_963_ = v_isSharedCheck_971_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_val_960_);
lean_dec(v_a_956_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_971_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_964_ = lean_nat_pow(v_val_960_, v_val_945_);
lean_dec(v_val_945_);
lean_dec(v_val_960_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 0, v___x_964_);
v___x_966_ = v___x_962_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_964_);
v___x_966_ = v_reuseFailAlloc_970_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_968_; 
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v___x_966_);
v___x_968_ = v___x_958_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
}
else
{
lean_dec(v_val_945_);
return v___x_955_;
}
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v_val_945_);
lean_dec_ref(v_arg_703_);
v_a_975_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_946_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_946_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_703_);
return v___x_943_;
}
}
}
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec_ref(v_arg_703_);
lean_dec_ref(v_arg_694_);
v_a_984_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_933_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_933_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
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
lean_object* v___x_992_; 
lean_dec_ref(v___x_707_);
lean_dec_ref(v_arg_706_);
lean_dec_ref(v_arg_703_);
lean_dec_ref(v_arg_694_);
v___x_992_ = l_Lean_Meta_getNatValue_x3f(v_e_671_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
lean_dec_ref(v_e_671_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
if (lean_obj_tag(v_a_993_) == 1)
{
lean_dec_ref(v_a_993_);
return v___x_992_;
}
else
{
lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1001_; 
lean_dec(v_a_993_);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1001_ == 0)
{
lean_object* v_unused_1002_; 
v_unused_1002_ = lean_ctor_get(v___x_992_, 0);
lean_dec(v_unused_1002_);
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1001_;
goto v_resetjp_994_;
}
else
{
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1001_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_997_ = lean_box(0);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_997_);
v___x_999_ = v___x_995_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_997_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
else
{
return v___x_992_;
}
}
}
}
}
else
{
lean_object* v___x_1003_; 
lean_dec_ref(v___x_695_);
lean_dec_ref(v_e_671_);
v___x_1003_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_694_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
if (lean_obj_tag(v_a_1004_) == 0)
{
return v___x_1003_;
}
else
{
lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1021_; 
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; 
v_unused_1022_ = lean_ctor_get(v___x_1003_, 0);
lean_dec(v_unused_1022_);
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1021_;
goto v_resetjp_1005_;
}
else
{
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1021_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_val_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1020_; 
v_val_1008_ = lean_ctor_get(v_a_1004_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_a_1004_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1010_ = v_a_1004_;
v_isShared_1011_ = v_isSharedCheck_1020_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_val_1008_);
lean_dec(v_a_1004_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1020_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1012_ = lean_unsigned_to_nat(1u);
v___x_1013_ = lean_nat_add(v_val_1008_, v___x_1012_);
lean_dec(v_val_1008_);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 0, v___x_1013_);
v___x_1015_ = v___x_1010_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
lean_object* v___x_1017_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1015_);
v___x_1017_ = v___x_1006_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
}
else
{
return v___x_1003_;
}
}
}
else
{
lean_object* v___x_1023_; 
lean_dec_ref(v___x_695_);
lean_dec_ref(v_e_671_);
v___x_1023_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_694_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1044_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1044_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1044_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
if (lean_obj_tag(v_a_1024_) == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1030_; 
v___x_1028_ = lean_box(0);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1028_);
v___x_1030_ = v___x_1026_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
else
{
lean_object* v_val_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1043_; 
v_val_1032_ = lean_ctor_get(v_a_1024_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_a_1024_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1034_ = v_a_1024_;
v_isShared_1035_ = v_isSharedCheck_1043_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_val_1032_);
lean_dec(v_a_1024_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1043_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
v___x_1036_ = l_Int_toNat(v_val_1032_);
lean_dec(v_val_1032_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v___x_1036_);
v___x_1038_ = v___x_1034_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1040_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1038_);
v___x_1040_ = v___x_1026_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
v_a_1045_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1023_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1023_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
else
{
lean_object* v___x_1053_; 
lean_dec_ref(v___x_695_);
lean_dec_ref(v_e_671_);
v___x_1053_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_694_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1074_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1074_ == 0)
{
v___x_1056_ = v___x_1053_;
v_isShared_1057_ = v_isSharedCheck_1074_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1074_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
if (lean_obj_tag(v_a_1054_) == 0)
{
lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1058_ = lean_box(0);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1058_);
v___x_1060_ = v___x_1056_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v___x_1058_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
else
{
lean_object* v_val_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1073_; 
v_val_1062_ = lean_ctor_get(v_a_1054_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_a_1054_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1064_ = v_a_1054_;
v_isShared_1065_ = v_isSharedCheck_1073_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_val_1062_);
lean_dec(v_a_1054_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1073_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1066_ = lean_nat_abs(v_val_1062_);
lean_dec(v_val_1062_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 0, v___x_1066_);
v___x_1068_ = v___x_1064_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1070_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1068_);
v___x_1070_ = v___x_1056_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
}
else
{
lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1082_; 
v_a_1075_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1077_ = v___x_1053_;
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1053_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1082_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1080_; 
if (v_isShared_1078_ == 0)
{
v___x_1080_ = v___x_1077_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_a_1075_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
lean_dec_ref(v___x_690_);
lean_dec_ref(v_e_671_);
v___x_1083_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31));
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_1083_);
v___x_1085_ = v___x_688_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec_ref(v_e_671_);
v_a_1088_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_685_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_685_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
v___jp_682_:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_box(0);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___boxed(lean_object* v_e_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_e_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
lean_dec(v_a_1105_);
lean_dec_ref(v_a_1104_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___boxed(lean_object* v_e_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_e_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
lean_dec(v_a_1109_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore_spec__1(lean_object* v_a_1120_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_nat_to_int(v_a_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalNat_x3f(lean_object* v_e_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_e_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalNat_x3f___boxed(lean_object* v_e_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_Meta_Grind_Arith_evalNat_x3f(v_e_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
lean_dec(v_a_1143_);
lean_dec_ref(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec_ref(v_a_1140_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalInt_x3f(lean_object* v_e_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_e_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalInt_x3f___boxed(lean_object* v_e_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_Meta_Grind_Arith_evalInt_x3f(v_e_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec_ref(v_a_1162_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
return v_res_1169_;
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
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
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(builtin);
}
#ifdef __cplusplus
}
#endif

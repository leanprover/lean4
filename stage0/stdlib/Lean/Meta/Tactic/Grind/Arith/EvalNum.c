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
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "exponent "};
static const lean_object* l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__2;
static const lean_string_object l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = " exceeds threshold for exponentiation `(exp := "};
static const lean_object* l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__4;
static const lean_string_object l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ")`"};
static const lean_object* l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__1));
v___x_5_ = l_Lean_stringToMessageData(v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__4(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__3));
v___x_8_ = l_Lean_stringToMessageData(v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__6(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__5));
v___x_11_ = l_Lean_stringToMessageData(v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___redArg(lean_object* v_k_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_13_);
if (lean_obj_tag(v___x_24_) == 0)
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_79_; 
v_a_25_ = lean_ctor_get(v___x_24_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_79_ == 0)
{
v___x_27_ = v___x_24_;
v_isShared_28_ = v_isSharedCheck_79_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_24_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_79_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v_exp_29_; uint8_t v___x_30_; 
v_exp_29_ = lean_ctor_get(v_a_25_, 8);
lean_inc(v_exp_29_);
lean_dec(v_a_25_);
v___x_30_ = lean_nat_dec_lt(v_exp_29_, v_k_12_);
lean_dec(v_exp_29_);
if (v___x_30_ == 0)
{
lean_object* v___x_31_; lean_object* v___x_33_; 
lean_dec(v_k_12_);
v___x_31_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__0));
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 0, v___x_31_);
v___x_33_ = v___x_27_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___x_31_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
else
{
lean_object* v___x_35_; 
lean_del_object(v___x_27_);
v___x_35_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_13_);
if (lean_obj_tag(v___x_35_) == 0)
{
lean_object* v_a_36_; lean_object* v___x_37_; 
v_a_36_ = lean_ctor_get(v___x_35_, 0);
lean_inc(v_a_36_);
lean_dec_ref(v___x_35_);
v___x_37_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_14_);
if (lean_obj_tag(v___x_37_) == 0)
{
lean_object* v_a_38_; uint8_t v___x_39_; 
v_a_38_ = lean_ctor_get(v___x_37_, 0);
lean_inc(v_a_38_);
lean_dec_ref(v___x_37_);
v___x_39_ = lean_unbox(v_a_38_);
lean_dec(v_a_38_);
if (v___x_39_ == 0)
{
lean_dec(v_a_36_);
lean_dec(v_k_12_);
goto v___jp_21_;
}
else
{
lean_object* v_exp_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v_exp_40_ = lean_ctor_get(v_a_36_, 8);
lean_inc(v_exp_40_);
lean_dec(v_a_36_);
v___x_41_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__2, &l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__2_once, _init_l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__2);
v___x_42_ = l_Nat_reprFast(v_k_12_);
v___x_43_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
v___x_44_ = l_Lean_MessageData_ofFormat(v___x_43_);
v___x_45_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_41_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
v___x_46_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__4, &l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__4_once, _init_l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__4);
v___x_47_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_45_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
v___x_48_ = l_Nat_reprFast(v_exp_40_);
v___x_49_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
v___x_50_ = l_Lean_MessageData_ofFormat(v___x_49_);
v___x_51_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_47_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
v___x_52_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__6, &l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__6_once, _init_l_Lean_Meta_Grind_Arith_checkExp___redArg___closed__6);
v___x_53_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_51_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
v___x_54_ = l_Lean_Meta_Sym_reportIssue(v___x_53_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_, v_a_19_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_dec_ref(v___x_54_);
goto v___jp_21_;
}
else
{
lean_object* v_a_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_62_; 
v_a_55_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_62_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_62_ == 0)
{
v___x_57_ = v___x_54_;
v_isShared_58_ = v_isSharedCheck_62_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_a_55_);
lean_dec(v___x_54_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_62_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_60_; 
if (v_isShared_58_ == 0)
{
v___x_60_ = v___x_57_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_a_55_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
}
}
}
else
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_70_; 
lean_dec(v_a_36_);
lean_dec(v_k_12_);
v_a_63_ = lean_ctor_get(v___x_37_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_37_);
if (v_isSharedCheck_70_ == 0)
{
v___x_65_ = v___x_37_;
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_37_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
if (v_isShared_66_ == 0)
{
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_a_63_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
else
{
lean_object* v_a_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_78_; 
lean_dec(v_k_12_);
v_a_71_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_78_ == 0)
{
v___x_73_ = v___x_35_;
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_a_71_);
lean_dec(v___x_35_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_76_; 
if (v_isShared_74_ == 0)
{
v___x_76_ = v___x_73_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_a_71_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
}
}
}
else
{
lean_object* v_a_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_87_; 
lean_dec(v_k_12_);
v_a_80_ = lean_ctor_get(v___x_24_, 0);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_87_ == 0)
{
v___x_82_ = v___x_24_;
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_a_80_);
lean_dec(v___x_24_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_87_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_85_; 
if (v_isShared_83_ == 0)
{
v___x_85_ = v___x_82_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_a_80_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
v___jp_21_:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_box(0);
v___x_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___redArg___boxed(lean_object* v_k_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Meta_Grind_Arith_checkExp___redArg(v_k_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
lean_dec_ref(v_a_89_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp(lean_object* v_k_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_Meta_Grind_Arith_checkExp___redArg(v_k_98_, v_a_100_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___boxed(lean_object* v_k_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_Meta_Grind_Arith_checkExp(v_k_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_);
lean_dec(v_a_119_);
lean_dec_ref(v_a_118_);
lean_dec(v_a_117_);
lean_dec_ref(v_a_116_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(lean_object* v_e_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_i_206_; lean_object* v_a_207_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___x_268_; 
lean_inc_ref(v_e_194_);
v___x_268_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_194_, v_a_201_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_639_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_639_ == 0)
{
v___x_271_ = v___x_268_;
v_isShared_272_ = v_isSharedCheck_639_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_268_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_639_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = l_Lean_Expr_cleanupAnnotations(v_a_269_);
v___x_279_ = l_Lean_Expr_isApp(v___x_278_);
if (v___x_279_ == 0)
{
lean_dec_ref(v___x_278_);
lean_dec_ref(v_e_194_);
goto v___jp_273_;
}
else
{
lean_object* v_arg_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v_arg_280_ = lean_ctor_get(v___x_278_, 1);
lean_inc_ref(v_arg_280_);
v___x_281_ = l_Lean_Expr_appFnCleanup___redArg(v___x_278_);
v___x_282_ = l_Lean_Expr_isApp(v___x_281_);
if (v___x_282_ == 0)
{
lean_dec_ref(v___x_281_);
lean_dec_ref(v_arg_280_);
lean_dec_ref(v_e_194_);
goto v___jp_273_;
}
else
{
lean_object* v_arg_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_arg_283_ = lean_ctor_get(v___x_281_, 1);
lean_inc_ref(v_arg_283_);
v___x_284_ = l_Lean_Expr_appFnCleanup___redArg(v___x_281_);
v___x_285_ = l_Lean_Expr_isApp(v___x_284_);
if (v___x_285_ == 0)
{
lean_dec_ref(v___x_284_);
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_arg_280_);
lean_dec_ref(v_e_194_);
goto v___jp_273_;
}
else
{
lean_object* v_arg_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v_arg_286_ = lean_ctor_get(v___x_284_, 1);
lean_inc_ref(v_arg_286_);
v___x_287_ = l_Lean_Expr_appFnCleanup___redArg(v___x_284_);
v___x_288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3));
v___x_289_ = l_Lean_Expr_isConstOf(v___x_287_, v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6));
v___x_291_ = l_Lean_Expr_isConstOf(v___x_287_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12));
v___x_293_ = l_Lean_Expr_isConstOf(v___x_287_, v___x_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; uint8_t v___x_295_; 
lean_dec_ref(v_e_194_);
v___x_294_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9));
v___x_295_ = l_Lean_Expr_isConstOf(v___x_287_, v___x_294_);
if (v___x_295_ == 0)
{
uint8_t v___x_296_; 
v___x_296_ = l_Lean_Expr_isApp(v___x_287_);
if (v___x_296_ == 0)
{
lean_dec_ref(v___x_287_);
lean_dec_ref(v_arg_286_);
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_arg_280_);
goto v___jp_273_;
}
else
{
lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = l_Lean_Expr_appFnCleanup___redArg(v___x_287_);
v___x_298_ = l_Lean_Expr_isApp(v___x_297_);
if (v___x_298_ == 0)
{
lean_dec_ref(v___x_297_);
lean_dec_ref(v_arg_286_);
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_arg_280_);
goto v___jp_273_;
}
else
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = l_Lean_Expr_appFnCleanup___redArg(v___x_297_);
v___x_300_ = l_Lean_Expr_isApp(v___x_299_);
if (v___x_300_ == 0)
{
lean_dec_ref(v___x_299_);
lean_dec_ref(v_arg_286_);
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_arg_280_);
goto v___jp_273_;
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_301_ = l_Lean_Expr_appFnCleanup___redArg(v___x_299_);
v___x_302_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15));
v___x_303_ = l_Lean_Expr_isConstOf(v___x_301_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18));
v___x_305_ = l_Lean_Expr_isConstOf(v___x_301_, v___x_304_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21));
v___x_307_ = l_Lean_Expr_isConstOf(v___x_301_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27));
v___x_309_ = l_Lean_Expr_isConstOf(v___x_301_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24));
v___x_311_ = l_Lean_Expr_isConstOf(v___x_301_, v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30));
v___x_313_ = l_Lean_Expr_isConstOf(v___x_301_, v___x_312_);
lean_dec_ref(v___x_301_);
if (v___x_313_ == 0)
{
lean_dec_ref(v_arg_286_);
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_arg_280_);
goto v___jp_273_;
}
else
{
lean_object* v___x_314_; 
lean_del_object(v___x_271_);
v___x_314_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_286_, v_a_201_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_346_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_346_ == 0)
{
v___x_317_ = v___x_314_;
v_isShared_318_ = v_isSharedCheck_346_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_346_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
uint8_t v___x_319_; 
v___x_319_ = lean_unbox(v_a_315_);
lean_dec(v_a_315_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; lean_object* v___x_322_; 
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_arg_280_);
v___x_320_ = lean_box(0);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_320_);
v___x_322_ = v___x_317_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
else
{
lean_object* v___x_324_; 
lean_del_object(v___x_317_);
v___x_324_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_283_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
if (lean_obj_tag(v_a_325_) == 0)
{
lean_dec_ref(v_arg_280_);
return v___x_324_;
}
else
{
lean_object* v_val_326_; lean_object* v___x_327_; 
lean_dec_ref(v___x_324_);
v_val_326_ = lean_ctor_get(v_a_325_, 0);
lean_inc(v_val_326_);
lean_dec_ref(v_a_325_);
v___x_327_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_280_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_328_);
if (lean_obj_tag(v_a_328_) == 0)
{
lean_dec(v_val_326_);
return v___x_327_;
}
else
{
lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_344_; 
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_344_ == 0)
{
lean_object* v_unused_345_; 
v_unused_345_ = lean_ctor_get(v___x_327_, 0);
lean_dec(v_unused_345_);
v___x_330_ = v___x_327_;
v_isShared_331_ = v_isSharedCheck_344_;
goto v_resetjp_329_;
}
else
{
lean_dec(v___x_327_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_344_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v_val_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_343_; 
v_val_332_ = lean_ctor_get(v_a_328_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v_a_328_);
if (v_isSharedCheck_343_ == 0)
{
v___x_334_ = v_a_328_;
v_isShared_335_ = v_isSharedCheck_343_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_val_332_);
lean_dec(v_a_328_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_343_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_336_ = lean_int_add(v_val_326_, v_val_332_);
lean_dec(v_val_332_);
lean_dec(v_val_326_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_336_);
v___x_338_ = v___x_334_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_342_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_340_; 
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_338_);
v___x_340_ = v___x_330_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
}
else
{
lean_dec(v_val_326_);
return v___x_327_;
}
}
}
else
{
lean_dec_ref(v_arg_280_);
return v___x_324_;
}
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_arg_280_);
v_a_347_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_314_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_314_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
else
{
lean_object* v___x_355_; 
lean_dec_ref(v___x_301_);
lean_del_object(v___x_271_);
v___x_355_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_arg_286_, v_a_201_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_387_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_387_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_387_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_387_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
uint8_t v___x_360_; 
v___x_360_ = lean_unbox(v_a_356_);
lean_dec(v_a_356_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; lean_object* v___x_363_; 
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_arg_280_);
v___x_361_ = lean_box(0);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_361_);
v___x_363_ = v___x_358_;
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
else
{
lean_object* v___x_365_; 
lean_del_object(v___x_358_);
v___x_365_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_283_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_a_366_);
if (lean_obj_tag(v_a_366_) == 0)
{
lean_dec_ref(v_arg_280_);
return v___x_365_;
}
else
{
lean_object* v_val_367_; lean_object* v___x_368_; 
lean_dec_ref(v___x_365_);
v_val_367_ = lean_ctor_get(v_a_366_, 0);
lean_inc(v_val_367_);
lean_dec_ref(v_a_366_);
v___x_368_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_280_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_a_369_; 
v_a_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_a_369_);
if (lean_obj_tag(v_a_369_) == 0)
{
lean_dec(v_val_367_);
return v___x_368_;
}
else
{
lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_385_; 
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_385_ == 0)
{
lean_object* v_unused_386_; 
v_unused_386_ = lean_ctor_get(v___x_368_, 0);
lean_dec(v_unused_386_);
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_385_;
goto v_resetjp_370_;
}
else
{
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_385_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v_val_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_384_; 
v_val_373_ = lean_ctor_get(v_a_369_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v_a_369_);
if (v_isSharedCheck_384_ == 0)
{
v___x_375_ = v_a_369_;
v_isShared_376_ = v_isSharedCheck_384_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_val_373_);
lean_dec(v_a_369_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_384_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_377_ = lean_int_sub(v_val_367_, v_val_373_);
lean_dec(v_val_373_);
lean_dec(v_val_367_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_377_);
v___x_379_ = v___x_375_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_383_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_381_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_379_);
v___x_381_ = v___x_371_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
}
else
{
lean_dec(v_val_367_);
return v___x_368_;
}
}
}
else
{
lean_dec_ref(v_arg_280_);
return v___x_365_;
}
}
}
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_arg_280_);
v_a_388_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_355_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_355_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
else
{
lean_object* v___x_396_; 
lean_dec_ref(v___x_301_);
lean_del_object(v___x_271_);
v___x_396_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_286_, v_a_201_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_428_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_428_ == 0)
{
v___x_399_ = v___x_396_;
v_isShared_400_ = v_isSharedCheck_428_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_428_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
uint8_t v___x_401_; 
v___x_401_ = lean_unbox(v_a_397_);
lean_dec(v_a_397_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_404_; 
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_arg_280_);
v___x_402_ = lean_box(0);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_402_);
v___x_404_ = v___x_399_;
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
else
{
lean_object* v___x_406_; 
lean_del_object(v___x_399_);
v___x_406_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_283_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
if (lean_obj_tag(v_a_407_) == 0)
{
lean_dec_ref(v_arg_280_);
return v___x_406_;
}
else
{
lean_object* v_val_408_; lean_object* v___x_409_; 
lean_dec_ref(v___x_406_);
v_val_408_ = lean_ctor_get(v_a_407_, 0);
lean_inc(v_val_408_);
lean_dec_ref(v_a_407_);
v___x_409_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_280_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
if (lean_obj_tag(v_a_410_) == 0)
{
lean_dec(v_val_408_);
return v___x_409_;
}
else
{
lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_426_; 
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_426_ == 0)
{
lean_object* v_unused_427_; 
v_unused_427_ = lean_ctor_get(v___x_409_, 0);
lean_dec(v_unused_427_);
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_426_;
goto v_resetjp_411_;
}
else
{
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_426_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v_val_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_425_; 
v_val_414_ = lean_ctor_get(v_a_410_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v_a_410_);
if (v_isSharedCheck_425_ == 0)
{
v___x_416_ = v_a_410_;
v_isShared_417_ = v_isSharedCheck_425_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_val_414_);
lean_dec(v_a_410_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_425_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_418_ = lean_int_mul(v_val_408_, v_val_414_);
lean_dec(v_val_414_);
lean_dec(v_val_408_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_418_);
v___x_420_ = v___x_416_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_424_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_object* v___x_422_; 
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_420_);
v___x_422_ = v___x_412_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
}
}
else
{
lean_dec(v_val_408_);
return v___x_409_;
}
}
}
else
{
lean_dec_ref(v_arg_280_);
return v___x_406_;
}
}
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_arg_280_);
v_a_429_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_396_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_396_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
else
{
lean_object* v___x_437_; 
lean_dec_ref(v___x_301_);
lean_del_object(v___x_271_);
v___x_437_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_arg_286_, v_a_201_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_469_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_469_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_469_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_469_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
uint8_t v___x_442_; 
v___x_442_ = lean_unbox(v_a_438_);
lean_dec(v_a_438_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_445_; 
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_arg_280_);
v___x_443_ = lean_box(0);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_443_);
v___x_445_ = v___x_440_;
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
else
{
lean_object* v___x_447_; 
lean_del_object(v___x_440_);
v___x_447_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_283_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
if (lean_obj_tag(v_a_448_) == 0)
{
lean_dec_ref(v_arg_280_);
return v___x_447_;
}
else
{
lean_object* v_val_449_; lean_object* v___x_450_; 
lean_dec_ref(v___x_447_);
v_val_449_ = lean_ctor_get(v_a_448_, 0);
lean_inc(v_val_449_);
lean_dec_ref(v_a_448_);
v___x_450_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_280_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_a_451_);
if (lean_obj_tag(v_a_451_) == 0)
{
lean_dec(v_val_449_);
return v___x_450_;
}
else
{
lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_467_; 
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_467_ == 0)
{
lean_object* v_unused_468_; 
v_unused_468_ = lean_ctor_get(v___x_450_, 0);
lean_dec(v_unused_468_);
v___x_453_ = v___x_450_;
v_isShared_454_ = v_isSharedCheck_467_;
goto v_resetjp_452_;
}
else
{
lean_dec(v___x_450_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_467_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v_val_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_466_; 
v_val_455_ = lean_ctor_get(v_a_451_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v_a_451_);
if (v_isSharedCheck_466_ == 0)
{
v___x_457_ = v_a_451_;
v_isShared_458_ = v_isSharedCheck_466_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_val_455_);
lean_dec(v_a_451_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_466_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_459_ = lean_int_ediv(v_val_449_, v_val_455_);
lean_dec(v_val_455_);
lean_dec(v_val_449_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_459_);
v___x_461_ = v___x_457_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_459_);
v___x_461_ = v_reuseFailAlloc_465_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_463_; 
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_461_);
v___x_463_ = v___x_453_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
}
}
else
{
lean_dec(v_val_449_);
return v___x_450_;
}
}
}
else
{
lean_dec_ref(v_arg_280_);
return v___x_447_;
}
}
}
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_477_; 
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_arg_280_);
v_a_470_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_477_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_477_ == 0)
{
v___x_472_ = v___x_437_;
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_437_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_477_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_475_; 
if (v_isShared_473_ == 0)
{
v___x_475_ = v___x_472_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_a_470_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
else
{
lean_object* v___x_478_; 
lean_dec_ref(v___x_301_);
lean_del_object(v___x_271_);
v___x_478_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_arg_286_, v_a_201_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_510_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_510_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_510_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_510_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
uint8_t v___x_483_; 
v___x_483_ = lean_unbox(v_a_479_);
lean_dec(v_a_479_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_486_; 
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_arg_280_);
v___x_484_ = lean_box(0);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_484_);
v___x_486_ = v___x_481_;
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
else
{
lean_object* v___x_488_; 
lean_del_object(v___x_481_);
v___x_488_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_283_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
if (lean_obj_tag(v_a_489_) == 0)
{
lean_dec_ref(v_arg_280_);
return v___x_488_;
}
else
{
lean_object* v_val_490_; lean_object* v___x_491_; 
lean_dec_ref(v___x_488_);
v_val_490_ = lean_ctor_get(v_a_489_, 0);
lean_inc(v_val_490_);
lean_dec_ref(v_a_489_);
v___x_491_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_280_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
if (lean_obj_tag(v_a_492_) == 0)
{
lean_dec(v_val_490_);
return v___x_491_;
}
else
{
lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_508_; 
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; 
v_unused_509_ = lean_ctor_get(v___x_491_, 0);
lean_dec(v_unused_509_);
v___x_494_ = v___x_491_;
v_isShared_495_ = v_isSharedCheck_508_;
goto v_resetjp_493_;
}
else
{
lean_dec(v___x_491_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_508_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v_val_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_507_; 
v_val_496_ = lean_ctor_get(v_a_492_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v_a_492_);
if (v_isSharedCheck_507_ == 0)
{
v___x_498_ = v_a_492_;
v_isShared_499_ = v_isSharedCheck_507_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_val_496_);
lean_dec(v_a_492_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_507_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_500_ = lean_int_emod(v_val_490_, v_val_496_);
lean_dec(v_val_496_);
lean_dec(v_val_490_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_500_);
v___x_502_ = v___x_498_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_506_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_504_; 
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 0, v___x_502_);
v___x_504_ = v___x_494_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
}
else
{
lean_dec(v_val_490_);
return v___x_491_;
}
}
}
else
{
lean_dec_ref(v_arg_280_);
return v___x_488_;
}
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_arg_280_);
v_a_511_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_478_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_478_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
else
{
lean_object* v___x_519_; 
lean_dec_ref(v___x_301_);
lean_del_object(v___x_271_);
v___x_519_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_arg_286_, v_a_201_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_581_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_581_ == 0)
{
v___x_522_ = v___x_519_;
v_isShared_523_ = v_isSharedCheck_581_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_581_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
uint8_t v___x_524_; 
v___x_524_ = lean_unbox(v_a_520_);
lean_dec(v_a_520_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_527_; 
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_arg_280_);
v___x_525_ = lean_box(0);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_525_);
v___x_527_ = v___x_522_;
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
else
{
lean_object* v___x_529_; 
lean_del_object(v___x_522_);
v___x_529_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_283_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
if (lean_obj_tag(v_a_530_) == 0)
{
lean_dec_ref(v_arg_280_);
return v___x_529_;
}
else
{
lean_object* v_val_531_; lean_object* v___x_532_; 
lean_dec_ref(v___x_529_);
v_val_531_ = lean_ctor_get(v_a_530_, 0);
lean_inc(v_val_531_);
lean_dec_ref(v_a_530_);
v___x_532_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_280_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_572_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_572_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_572_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_572_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
if (lean_obj_tag(v_a_533_) == 0)
{
lean_object* v___x_537_; lean_object* v___x_539_; 
lean_dec(v_val_531_);
v___x_537_ = lean_box(0);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 0, v___x_537_);
v___x_539_ = v___x_535_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
else
{
lean_object* v_val_541_; lean_object* v___x_542_; 
lean_del_object(v___x_535_);
v_val_541_ = lean_ctor_get(v_a_533_, 0);
lean_inc_n(v_val_541_, 2);
lean_dec_ref(v_a_533_);
v___x_542_ = l_Lean_Meta_Grind_Arith_checkExp___redArg(v_val_541_, v_a_196_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_563_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_563_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_563_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_563_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
if (lean_obj_tag(v_a_543_) == 0)
{
lean_object* v___x_547_; lean_object* v___x_549_; 
lean_dec(v_val_541_);
lean_dec(v_val_531_);
v___x_547_ = lean_box(0);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_547_);
v___x_549_ = v___x_545_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
else
{
lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_561_; 
v_isSharedCheck_561_ = !lean_is_exclusive(v_a_543_);
if (v_isSharedCheck_561_ == 0)
{
lean_object* v_unused_562_; 
v_unused_562_ = lean_ctor_get(v_a_543_, 0);
lean_dec(v_unused_562_);
v___x_552_ = v_a_543_;
v_isShared_553_ = v_isSharedCheck_561_;
goto v_resetjp_551_;
}
else
{
lean_dec(v_a_543_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_561_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_554_ = l_Int_pow(v_val_531_, v_val_541_);
lean_dec(v_val_541_);
lean_dec(v_val_531_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_554_);
v___x_556_ = v___x_552_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_560_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_556_);
v___x_558_ = v___x_545_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_556_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec(v_val_541_);
lean_dec(v_val_531_);
v_a_564_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_542_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_542_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
}
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_dec(v_val_531_);
v_a_573_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_532_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_532_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_280_);
return v___x_529_;
}
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_arg_280_);
v_a_582_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_519_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_519_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
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
lean_object* v___x_590_; 
lean_dec_ref(v___x_287_);
lean_dec_ref(v_arg_286_);
lean_del_object(v___x_271_);
v___x_590_ = l_Lean_Meta_Structural_isInstNegInt___redArg(v_arg_283_, v_a_201_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_619_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_619_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_619_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_619_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
uint8_t v___x_595_; 
v___x_595_ = lean_unbox(v_a_591_);
lean_dec(v_a_591_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_598_; 
lean_dec_ref(v_arg_280_);
v___x_596_ = lean_box(0);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_596_);
v___x_598_ = v___x_593_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
else
{
lean_object* v___x_600_; 
lean_del_object(v___x_593_);
v___x_600_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_280_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
if (lean_obj_tag(v_a_601_) == 0)
{
return v___x_600_;
}
else
{
lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_617_; 
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; 
v_unused_618_ = lean_ctor_get(v___x_600_, 0);
lean_dec(v_unused_618_);
v___x_603_ = v___x_600_;
v_isShared_604_ = v_isSharedCheck_617_;
goto v_resetjp_602_;
}
else
{
lean_dec(v___x_600_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_617_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v_val_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_616_; 
v_val_605_ = lean_ctor_get(v_a_601_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v_a_601_);
if (v_isSharedCheck_616_ == 0)
{
v___x_607_ = v_a_601_;
v_isShared_608_ = v_isSharedCheck_616_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_val_605_);
lean_dec(v_a_601_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_616_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_609_ = lean_int_neg(v_val_605_);
lean_dec(v_val_605_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_609_);
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_609_);
v___x_611_ = v_reuseFailAlloc_615_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_613_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_611_);
v___x_613_ = v___x_603_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
}
else
{
return v___x_600_;
}
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec_ref(v_arg_280_);
v_a_620_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_590_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_590_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
else
{
lean_object* v___x_628_; 
lean_dec_ref(v___x_287_);
lean_dec_ref(v_arg_286_);
lean_dec_ref(v_arg_283_);
lean_dec_ref(v_arg_280_);
lean_del_object(v___x_271_);
v___x_628_ = l_Lean_Meta_getIntValue_x3f(v_e_194_, v_a_200_, v_a_201_, v_a_202_, v_a_203_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
if (lean_obj_tag(v_a_629_) == 1)
{
lean_dec_ref(v_a_629_);
return v___x_628_;
}
else
{
lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_637_; 
lean_dec(v_a_629_);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; 
v_unused_638_ = lean_ctor_get(v___x_628_, 0);
lean_dec(v_unused_638_);
v___x_631_ = v___x_628_;
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
else
{
lean_dec(v___x_628_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_637_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_635_; 
v___x_633_ = lean_box(0);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_633_);
v___x_635_ = v___x_631_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v___x_633_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
else
{
return v___x_628_;
}
}
}
else
{
lean_dec_ref(v___x_287_);
lean_dec_ref(v_arg_286_);
lean_del_object(v___x_271_);
lean_dec_ref(v_e_194_);
v_i_206_ = v_arg_283_;
v_a_207_ = v_arg_280_;
v___y_208_ = v_a_195_;
v___y_209_ = v_a_196_;
v___y_210_ = v_a_197_;
v___y_211_ = v_a_198_;
v___y_212_ = v_a_199_;
v___y_213_ = v_a_200_;
v___y_214_ = v_a_201_;
v___y_215_ = v_a_202_;
v___y_216_ = v_a_203_;
goto v___jp_205_;
}
}
else
{
lean_dec_ref(v___x_287_);
lean_dec_ref(v_arg_286_);
lean_del_object(v___x_271_);
lean_dec_ref(v_e_194_);
v_i_206_ = v_arg_283_;
v_a_207_ = v_arg_280_;
v___y_208_ = v_a_195_;
v___y_209_ = v_a_196_;
v___y_210_ = v_a_197_;
v___y_211_ = v_a_198_;
v___y_212_ = v_a_199_;
v___y_213_ = v_a_200_;
v___y_214_ = v_a_201_;
v___y_215_ = v_a_202_;
v___y_216_ = v_a_203_;
goto v___jp_205_;
}
}
}
}
v___jp_273_:
{
lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_274_ = lean_box(0);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_274_);
v___x_276_ = v___x_271_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v_e_194_);
v_a_640_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_268_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_268_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
v___jp_205_:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_i_206_, v___y_214_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_259_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_259_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_259_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_259_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_222_ = l_Lean_Expr_cleanupAnnotations(v_a_218_);
v___x_223_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1));
v___x_224_ = l_Lean_Expr_isConstOf(v___x_222_, v___x_223_);
lean_dec_ref(v___x_222_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_227_; 
lean_dec_ref(v_a_207_);
v___x_225_ = lean_box(0);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_225_);
v___x_227_ = v___x_220_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
else
{
lean_object* v___x_229_; 
lean_del_object(v___x_220_);
v___x_229_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_a_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_250_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_250_ == 0)
{
v___x_232_ = v___x_229_;
v_isShared_233_ = v_isSharedCheck_250_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_229_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_250_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
if (lean_obj_tag(v_a_230_) == 0)
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = lean_box(0);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_234_);
v___x_236_ = v___x_232_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
else
{
lean_object* v_val_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_249_; 
v_val_238_ = lean_ctor_get(v_a_230_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v_a_230_);
if (v_isSharedCheck_249_ == 0)
{
v___x_240_ = v_a_230_;
v_isShared_241_ = v_isSharedCheck_249_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_val_238_);
lean_dec(v_a_230_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_249_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_242_ = lean_nat_to_int(v_val_238_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v___x_242_);
v___x_244_ = v___x_240_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_242_);
v___x_244_ = v_reuseFailAlloc_248_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_246_; 
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_244_);
v___x_246_ = v___x_232_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
v_a_251_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_229_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_229_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
}
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
lean_dec_ref(v_a_207_);
v_a_260_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_217_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_217_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_260_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(lean_object* v_e_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v___x_662_; 
lean_inc_ref(v_e_648_);
v___x_662_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_648_, v_a_655_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_1064_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_1064_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_1064_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_667_ = l_Lean_Expr_cleanupAnnotations(v_a_663_);
v___x_668_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2));
v___x_669_ = l_Lean_Expr_isConstOf(v___x_667_, v___x_668_);
if (v___x_669_ == 0)
{
uint8_t v___x_670_; 
lean_del_object(v___x_665_);
v___x_670_ = l_Lean_Expr_isApp(v___x_667_);
if (v___x_670_ == 0)
{
lean_dec_ref(v___x_667_);
lean_dec_ref(v_e_648_);
goto v___jp_659_;
}
else
{
lean_object* v_arg_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_arg_671_ = lean_ctor_get(v___x_667_, 1);
lean_inc_ref(v_arg_671_);
v___x_672_ = l_Lean_Expr_appFnCleanup___redArg(v___x_667_);
v___x_673_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5));
v___x_674_ = l_Lean_Expr_isConstOf(v___x_672_, v___x_673_);
if (v___x_674_ == 0)
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7));
v___x_676_ = l_Lean_Expr_isConstOf(v___x_672_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9));
v___x_678_ = l_Lean_Expr_isConstOf(v___x_672_, v___x_677_);
if (v___x_678_ == 0)
{
uint8_t v___x_679_; 
v___x_679_ = l_Lean_Expr_isApp(v___x_672_);
if (v___x_679_ == 0)
{
lean_dec_ref(v___x_672_);
lean_dec_ref(v_arg_671_);
lean_dec_ref(v_e_648_);
goto v___jp_659_;
}
else
{
lean_object* v_arg_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_arg_680_ = lean_ctor_get(v___x_672_, 1);
lean_inc_ref(v_arg_680_);
v___x_681_ = l_Lean_Expr_appFnCleanup___redArg(v___x_672_);
v___x_682_ = l_Lean_Expr_isApp(v___x_681_);
if (v___x_682_ == 0)
{
lean_dec_ref(v___x_681_);
lean_dec_ref(v_arg_680_);
lean_dec_ref(v_arg_671_);
lean_dec_ref(v_e_648_);
goto v___jp_659_;
}
else
{
lean_object* v_arg_683_; lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v_arg_683_ = lean_ctor_get(v___x_681_, 1);
lean_inc_ref(v_arg_683_);
v___x_684_ = l_Lean_Expr_appFnCleanup___redArg(v___x_681_);
v___x_685_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12));
v___x_686_ = l_Lean_Expr_isConstOf(v___x_684_, v___x_685_);
if (v___x_686_ == 0)
{
uint8_t v___x_687_; 
lean_dec_ref(v_e_648_);
v___x_687_ = l_Lean_Expr_isApp(v___x_684_);
if (v___x_687_ == 0)
{
lean_dec_ref(v___x_684_);
lean_dec_ref(v_arg_683_);
lean_dec_ref(v_arg_680_);
lean_dec_ref(v_arg_671_);
goto v___jp_659_;
}
else
{
lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_688_ = l_Lean_Expr_appFnCleanup___redArg(v___x_684_);
v___x_689_ = l_Lean_Expr_isApp(v___x_688_);
if (v___x_689_ == 0)
{
lean_dec_ref(v___x_688_);
lean_dec_ref(v_arg_683_);
lean_dec_ref(v_arg_680_);
lean_dec_ref(v_arg_671_);
goto v___jp_659_;
}
else
{
lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_690_ = l_Lean_Expr_appFnCleanup___redArg(v___x_688_);
v___x_691_ = l_Lean_Expr_isApp(v___x_690_);
if (v___x_691_ == 0)
{
lean_dec_ref(v___x_690_);
lean_dec_ref(v_arg_683_);
lean_dec_ref(v_arg_680_);
lean_dec_ref(v_arg_671_);
goto v___jp_659_;
}
else
{
lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_692_ = l_Lean_Expr_appFnCleanup___redArg(v___x_690_);
v___x_693_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15));
v___x_694_ = l_Lean_Expr_isConstOf(v___x_692_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_695_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18));
v___x_696_ = l_Lean_Expr_isConstOf(v___x_692_, v___x_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_697_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21));
v___x_698_ = l_Lean_Expr_isConstOf(v___x_692_, v___x_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_699_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24));
v___x_700_ = l_Lean_Expr_isConstOf(v___x_692_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; uint8_t v___x_702_; 
v___x_701_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27));
v___x_702_ = l_Lean_Expr_isConstOf(v___x_692_, v___x_701_);
if (v___x_702_ == 0)
{
lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_703_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30));
v___x_704_ = l_Lean_Expr_isConstOf(v___x_692_, v___x_703_);
lean_dec_ref(v___x_692_);
if (v___x_704_ == 0)
{
lean_dec_ref(v_arg_683_);
lean_dec_ref(v_arg_680_);
lean_dec_ref(v_arg_671_);
goto v___jp_659_;
}
else
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_683_, v_a_655_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_737_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_737_ == 0)
{
v___x_708_ = v___x_705_;
v_isShared_709_ = v_isSharedCheck_737_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_737_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
uint8_t v___x_710_; 
v___x_710_ = lean_unbox(v_a_706_);
lean_dec(v_a_706_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_713_; 
lean_dec_ref(v_arg_680_);
lean_dec_ref(v_arg_671_);
v___x_711_ = lean_box(0);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v___x_711_);
v___x_713_ = v___x_708_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
else
{
lean_object* v___x_715_; 
lean_del_object(v___x_708_);
v___x_715_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_680_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_716_);
if (lean_obj_tag(v_a_716_) == 0)
{
lean_dec_ref(v_arg_671_);
return v___x_715_;
}
else
{
lean_object* v_val_717_; lean_object* v___x_718_; 
lean_dec_ref(v___x_715_);
v_val_717_ = lean_ctor_get(v_a_716_, 0);
lean_inc(v_val_717_);
lean_dec_ref(v_a_716_);
v___x_718_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_671_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
if (lean_obj_tag(v_a_719_) == 0)
{
lean_dec(v_val_717_);
return v___x_718_;
}
else
{
lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_735_; 
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_735_ == 0)
{
lean_object* v_unused_736_; 
v_unused_736_ = lean_ctor_get(v___x_718_, 0);
lean_dec(v_unused_736_);
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_735_;
goto v_resetjp_720_;
}
else
{
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_735_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v_val_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_734_; 
v_val_723_ = lean_ctor_get(v_a_719_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v_a_719_);
if (v_isSharedCheck_734_ == 0)
{
v___x_725_ = v_a_719_;
v_isShared_726_ = v_isSharedCheck_734_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_val_723_);
lean_dec(v_a_719_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_734_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_727_ = lean_nat_add(v_val_717_, v_val_723_);
lean_dec(v_val_723_);
lean_dec(v_val_717_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_727_);
v___x_729_ = v___x_725_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_727_);
v___x_729_ = v_reuseFailAlloc_733_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_731_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v___x_729_);
v___x_731_ = v___x_721_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
}
}
else
{
lean_dec(v_val_717_);
return v___x_718_;
}
}
}
else
{
lean_dec_ref(v_arg_671_);
return v___x_715_;
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec_ref(v_arg_680_);
lean_dec_ref(v_arg_671_);
v_a_738_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_705_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_705_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
else
{
lean_object* v___x_746_; 
lean_dec_ref(v___x_692_);
v___x_746_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_arg_683_, v_a_655_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_778_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_778_ == 0)
{
v___x_749_ = v___x_746_;
v_isShared_750_ = v_isSharedCheck_778_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_746_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_778_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
uint8_t v___x_751_; 
v___x_751_ = lean_unbox(v_a_747_);
lean_dec(v_a_747_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_754_; 
lean_dec_ref(v_arg_680_);
lean_dec_ref(v_arg_671_);
v___x_752_ = lean_box(0);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_752_);
v___x_754_ = v___x_749_;
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
else
{
lean_object* v___x_756_; 
lean_del_object(v___x_749_);
v___x_756_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_680_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
if (lean_obj_tag(v_a_757_) == 0)
{
lean_dec_ref(v_arg_671_);
return v___x_756_;
}
else
{
lean_object* v_val_758_; lean_object* v___x_759_; 
lean_dec_ref(v___x_756_);
v_val_758_ = lean_ctor_get(v_a_757_, 0);
lean_inc(v_val_758_);
lean_dec_ref(v_a_757_);
v___x_759_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_671_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
if (lean_obj_tag(v_a_760_) == 0)
{
lean_dec(v_val_758_);
return v___x_759_;
}
else
{
lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_776_; 
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; 
v_unused_777_ = lean_ctor_get(v___x_759_, 0);
lean_dec(v_unused_777_);
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_776_;
goto v_resetjp_761_;
}
else
{
lean_dec(v___x_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_776_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v_val_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_775_; 
v_val_764_ = lean_ctor_get(v_a_760_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v_a_760_);
if (v_isSharedCheck_775_ == 0)
{
v___x_766_ = v_a_760_;
v_isShared_767_ = v_isSharedCheck_775_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_val_764_);
lean_dec(v_a_760_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_775_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_768_ = lean_nat_mul(v_val_758_, v_val_764_);
lean_dec(v_val_764_);
lean_dec(v_val_758_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v___x_768_);
v___x_770_ = v___x_766_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_768_);
v___x_770_ = v_reuseFailAlloc_774_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_772_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v___x_770_);
v___x_772_ = v___x_762_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
}
else
{
lean_dec(v_val_758_);
return v___x_759_;
}
}
}
else
{
lean_dec_ref(v_arg_671_);
return v___x_756_;
}
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec_ref(v_arg_680_);
lean_dec_ref(v_arg_671_);
v_a_779_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_746_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_746_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
}
else
{
lean_object* v___x_787_; 
lean_dec_ref(v___x_692_);
v___x_787_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_arg_683_, v_a_655_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_819_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_819_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_819_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_819_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
uint8_t v___x_792_; 
v___x_792_ = lean_unbox(v_a_788_);
lean_dec(v_a_788_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; lean_object* v___x_795_; 
lean_dec_ref(v_arg_680_);
lean_dec_ref(v_arg_671_);
v___x_793_ = lean_box(0);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_793_);
v___x_795_ = v___x_790_;
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
else
{
lean_object* v___x_797_; 
lean_del_object(v___x_790_);
v___x_797_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_680_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
if (lean_obj_tag(v_a_798_) == 0)
{
lean_dec_ref(v_arg_671_);
return v___x_797_;
}
else
{
lean_object* v_val_799_; lean_object* v___x_800_; 
lean_dec_ref(v___x_797_);
v_val_799_ = lean_ctor_get(v_a_798_, 0);
lean_inc(v_val_799_);
lean_dec_ref(v_a_798_);
v___x_800_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_671_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
if (lean_obj_tag(v_a_801_) == 0)
{
lean_dec(v_val_799_);
return v___x_800_;
}
else
{
lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_817_; 
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_817_ == 0)
{
lean_object* v_unused_818_; 
v_unused_818_ = lean_ctor_get(v___x_800_, 0);
lean_dec(v_unused_818_);
v___x_803_ = v___x_800_;
v_isShared_804_ = v_isSharedCheck_817_;
goto v_resetjp_802_;
}
else
{
lean_dec(v___x_800_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_817_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v_val_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_816_; 
v_val_805_ = lean_ctor_get(v_a_801_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v_a_801_);
if (v_isSharedCheck_816_ == 0)
{
v___x_807_ = v_a_801_;
v_isShared_808_ = v_isSharedCheck_816_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_val_805_);
lean_dec(v_a_801_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_816_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_809_ = lean_nat_sub(v_val_799_, v_val_805_);
lean_dec(v_val_805_);
lean_dec(v_val_799_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_809_);
v___x_811_ = v___x_807_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_815_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_813_; 
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 0, v___x_811_);
v___x_813_ = v___x_803_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_811_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
}
else
{
lean_dec(v_val_799_);
return v___x_800_;
}
}
}
else
{
lean_dec_ref(v_arg_671_);
return v___x_797_;
}
}
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec_ref(v_arg_680_);
lean_dec_ref(v_arg_671_);
v_a_820_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_787_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_787_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
else
{
lean_object* v___x_828_; 
lean_dec_ref(v___x_692_);
v___x_828_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_arg_683_, v_a_655_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_860_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_860_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_860_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_860_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
uint8_t v___x_833_; 
v___x_833_ = lean_unbox(v_a_829_);
lean_dec(v_a_829_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_836_; 
lean_dec_ref(v_arg_680_);
lean_dec_ref(v_arg_671_);
v___x_834_ = lean_box(0);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_834_);
v___x_836_ = v___x_831_;
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
else
{
lean_object* v___x_838_; 
lean_del_object(v___x_831_);
v___x_838_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_680_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
if (lean_obj_tag(v_a_839_) == 0)
{
lean_dec_ref(v_arg_671_);
return v___x_838_;
}
else
{
lean_object* v_val_840_; lean_object* v___x_841_; 
lean_dec_ref(v___x_838_);
v_val_840_ = lean_ctor_get(v_a_839_, 0);
lean_inc(v_val_840_);
lean_dec_ref(v_a_839_);
v___x_841_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_671_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
if (lean_obj_tag(v_a_842_) == 0)
{
lean_dec(v_val_840_);
return v___x_841_;
}
else
{
lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_858_; 
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v___x_841_, 0);
lean_dec(v_unused_859_);
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_858_;
goto v_resetjp_843_;
}
else
{
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_858_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v_val_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_857_; 
v_val_846_ = lean_ctor_get(v_a_842_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v_a_842_);
if (v_isSharedCheck_857_ == 0)
{
v___x_848_ = v_a_842_;
v_isShared_849_ = v_isSharedCheck_857_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_val_846_);
lean_dec(v_a_842_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_857_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_850_ = lean_nat_div(v_val_840_, v_val_846_);
lean_dec(v_val_846_);
lean_dec(v_val_840_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_850_);
v___x_852_ = v___x_848_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_850_);
v___x_852_ = v_reuseFailAlloc_856_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_854_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_852_);
v___x_854_ = v___x_844_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
}
else
{
lean_dec(v_val_840_);
return v___x_841_;
}
}
}
else
{
lean_dec_ref(v_arg_671_);
return v___x_838_;
}
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_dec_ref(v_arg_680_);
lean_dec_ref(v_arg_671_);
v_a_861_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_828_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_828_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
else
{
lean_object* v___x_869_; 
lean_dec_ref(v___x_692_);
v___x_869_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_arg_683_, v_a_655_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_901_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_901_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_901_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_901_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
uint8_t v___x_874_; 
v___x_874_ = lean_unbox(v_a_870_);
lean_dec(v_a_870_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; lean_object* v___x_877_; 
lean_dec_ref(v_arg_680_);
lean_dec_ref(v_arg_671_);
v___x_875_ = lean_box(0);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_875_);
v___x_877_ = v___x_872_;
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
else
{
lean_object* v___x_879_; 
lean_del_object(v___x_872_);
v___x_879_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_680_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_a_880_);
if (lean_obj_tag(v_a_880_) == 0)
{
lean_dec_ref(v_arg_671_);
return v___x_879_;
}
else
{
lean_object* v_val_881_; lean_object* v___x_882_; 
lean_dec_ref(v___x_879_);
v_val_881_ = lean_ctor_get(v_a_880_, 0);
lean_inc(v_val_881_);
lean_dec_ref(v_a_880_);
v___x_882_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_671_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
if (lean_obj_tag(v_a_883_) == 0)
{
lean_dec(v_val_881_);
return v___x_882_;
}
else
{
lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_899_; 
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; 
v_unused_900_ = lean_ctor_get(v___x_882_, 0);
lean_dec(v_unused_900_);
v___x_885_ = v___x_882_;
v_isShared_886_ = v_isSharedCheck_899_;
goto v_resetjp_884_;
}
else
{
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_899_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v_val_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_898_; 
v_val_887_ = lean_ctor_get(v_a_883_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v_a_883_);
if (v_isSharedCheck_898_ == 0)
{
v___x_889_ = v_a_883_;
v_isShared_890_ = v_isSharedCheck_898_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_val_887_);
lean_dec(v_a_883_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_898_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_891_ = lean_nat_mod(v_val_881_, v_val_887_);
lean_dec(v_val_887_);
lean_dec(v_val_881_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_891_);
v___x_893_ = v___x_889_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_897_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_895_; 
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_893_);
v___x_895_ = v___x_885_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
}
else
{
lean_dec(v_val_881_);
return v___x_882_;
}
}
}
else
{
lean_dec_ref(v_arg_671_);
return v___x_879_;
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec_ref(v_arg_680_);
lean_dec_ref(v_arg_671_);
v_a_902_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_869_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_869_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
else
{
lean_object* v___x_910_; 
lean_dec_ref(v___x_692_);
v___x_910_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_arg_683_, v_a_655_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_960_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_960_ == 0)
{
v___x_913_ = v___x_910_;
v_isShared_914_ = v_isSharedCheck_960_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_960_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
uint8_t v___x_915_; 
v___x_915_ = lean_unbox(v_a_911_);
lean_dec(v_a_911_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_918_; 
lean_dec_ref(v_arg_680_);
lean_dec_ref(v_arg_671_);
v___x_916_ = lean_box(0);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_916_);
v___x_918_ = v___x_913_;
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
else
{
lean_object* v___x_920_; 
lean_del_object(v___x_913_);
v___x_920_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_671_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
if (lean_obj_tag(v_a_921_) == 0)
{
lean_dec_ref(v_arg_680_);
return v___x_920_;
}
else
{
lean_object* v_val_922_; lean_object* v___x_923_; 
lean_dec_ref(v___x_920_);
v_val_922_ = lean_ctor_get(v_a_921_, 0);
lean_inc_n(v_val_922_, 2);
lean_dec_ref(v_a_921_);
v___x_923_ = l_Lean_Meta_Grind_Arith_checkExp___redArg(v_val_922_, v_a_650_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_951_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_951_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_951_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_951_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
if (lean_obj_tag(v_a_924_) == 0)
{
lean_object* v___x_928_; lean_object* v___x_930_; 
lean_dec(v_val_922_);
lean_dec_ref(v_arg_680_);
v___x_928_ = lean_box(0);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_928_);
v___x_930_ = v___x_926_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
else
{
lean_object* v___x_932_; 
lean_dec_ref(v_a_924_);
lean_del_object(v___x_926_);
v___x_932_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_680_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
if (lean_obj_tag(v_a_933_) == 0)
{
lean_dec(v_val_922_);
return v___x_932_;
}
else
{
lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_949_; 
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_949_ == 0)
{
lean_object* v_unused_950_; 
v_unused_950_ = lean_ctor_get(v___x_932_, 0);
lean_dec(v_unused_950_);
v___x_935_ = v___x_932_;
v_isShared_936_ = v_isSharedCheck_949_;
goto v_resetjp_934_;
}
else
{
lean_dec(v___x_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_949_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v_val_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_948_; 
v_val_937_ = lean_ctor_get(v_a_933_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v_a_933_);
if (v_isSharedCheck_948_ == 0)
{
v___x_939_ = v_a_933_;
v_isShared_940_ = v_isSharedCheck_948_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_val_937_);
lean_dec(v_a_933_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_948_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_941_ = lean_nat_pow(v_val_937_, v_val_922_);
lean_dec(v_val_922_);
lean_dec(v_val_937_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v___x_941_);
v___x_943_ = v___x_939_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_941_);
v___x_943_ = v_reuseFailAlloc_947_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_945_; 
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_943_);
v___x_945_ = v___x_935_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
}
else
{
lean_dec(v_val_922_);
return v___x_932_;
}
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec(v_val_922_);
lean_dec_ref(v_arg_680_);
v_a_952_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_923_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_923_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_680_);
return v___x_920_;
}
}
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
lean_dec_ref(v_arg_680_);
lean_dec_ref(v_arg_671_);
v_a_961_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_910_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_910_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
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
lean_object* v___x_969_; 
lean_dec_ref(v___x_684_);
lean_dec_ref(v_arg_683_);
lean_dec_ref(v_arg_680_);
lean_dec_ref(v_arg_671_);
v___x_969_ = l_Lean_Meta_getNatValue_x3f(v_e_648_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
lean_dec_ref(v_e_648_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
if (lean_obj_tag(v_a_970_) == 1)
{
lean_dec_ref(v_a_970_);
return v___x_969_;
}
else
{
lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_978_; 
lean_dec(v_a_970_);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_978_ == 0)
{
lean_object* v_unused_979_; 
v_unused_979_ = lean_ctor_get(v___x_969_, 0);
lean_dec(v_unused_979_);
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
else
{
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_978_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_976_; 
v___x_974_ = lean_box(0);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_974_);
v___x_976_ = v___x_972_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_974_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
else
{
return v___x_969_;
}
}
}
}
}
else
{
lean_object* v___x_980_; 
lean_dec_ref(v___x_672_);
lean_dec_ref(v_e_648_);
v___x_980_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_arg_671_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc(v_a_981_);
if (lean_obj_tag(v_a_981_) == 0)
{
return v___x_980_;
}
else
{
lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_998_; 
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_998_ == 0)
{
lean_object* v_unused_999_; 
v_unused_999_ = lean_ctor_get(v___x_980_, 0);
lean_dec(v_unused_999_);
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_998_;
goto v_resetjp_982_;
}
else
{
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_998_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v_val_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_997_; 
v_val_985_ = lean_ctor_get(v_a_981_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v_a_981_);
if (v_isSharedCheck_997_ == 0)
{
v___x_987_ = v_a_981_;
v_isShared_988_ = v_isSharedCheck_997_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_val_985_);
lean_dec(v_a_981_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_997_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_989_ = lean_unsigned_to_nat(1u);
v___x_990_ = lean_nat_add(v_val_985_, v___x_989_);
lean_dec(v_val_985_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_990_);
v___x_992_ = v___x_987_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_990_);
v___x_992_ = v_reuseFailAlloc_996_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_994_; 
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_992_);
v___x_994_ = v___x_983_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_992_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
}
else
{
return v___x_980_;
}
}
}
else
{
lean_object* v___x_1000_; 
lean_dec_ref(v___x_672_);
lean_dec_ref(v_e_648_);
v___x_1000_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_671_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1021_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1021_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1021_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
if (lean_obj_tag(v_a_1001_) == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1005_ = lean_box(0);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___x_1005_);
v___x_1007_ = v___x_1003_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
else
{
lean_object* v_val_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1020_; 
v_val_1009_ = lean_ctor_get(v_a_1001_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v_a_1001_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1011_ = v_a_1001_;
v_isShared_1012_ = v_isSharedCheck_1020_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_val_1009_);
lean_dec(v_a_1001_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1020_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1013_ = l_Int_toNat(v_val_1009_);
lean_dec(v_val_1009_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1013_);
v___x_1015_ = v___x_1011_;
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
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___x_1015_);
v___x_1017_ = v___x_1003_;
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
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
v_a_1022_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1000_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1000_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
else
{
lean_object* v___x_1030_; 
lean_dec_ref(v___x_672_);
lean_dec_ref(v_e_648_);
v___x_1030_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_arg_671_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1051_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1051_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1051_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
if (lean_obj_tag(v_a_1031_) == 0)
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1035_ = lean_box(0);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1035_);
v___x_1037_ = v___x_1033_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
else
{
lean_object* v_val_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1050_; 
v_val_1039_ = lean_ctor_get(v_a_1031_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v_a_1031_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1041_ = v_a_1031_;
v_isShared_1042_ = v_isSharedCheck_1050_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_val_1039_);
lean_dec(v_a_1031_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1050_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1043_ = lean_nat_abs(v_val_1039_);
lean_dec(v_val_1039_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 0, v___x_1043_);
v___x_1045_ = v___x_1041_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1047_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1045_);
v___x_1047_ = v___x_1033_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
v_a_1052_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1030_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1030_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
lean_dec_ref(v___x_667_);
lean_dec_ref(v_e_648_);
v___x_1060_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31));
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_1060_);
v___x_1062_ = v___x_665_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1072_; 
lean_dec_ref(v_e_648_);
v_a_1065_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1067_ = v___x_662_;
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_a_1065_);
lean_dec(v___x_662_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1072_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1070_; 
if (v_isShared_1068_ == 0)
{
v___x_1070_ = v___x_1067_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_a_1065_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
v___jp_659_:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = lean_box(0);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
return v___x_661_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___boxed(lean_object* v_e_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_e_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___boxed(lean_object* v_e_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_e_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
lean_dec(v_a_1092_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1088_);
lean_dec_ref(v_a_1087_);
lean_dec(v_a_1086_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore_spec__1(lean_object* v_a_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_nat_to_int(v_a_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalNat_x3f(lean_object* v_e_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(v_e_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalNat_x3f___boxed(lean_object* v_e_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_Meta_Grind_Arith_evalNat_x3f(v_e_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1112_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalInt_x3f(lean_object* v_e_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(v_e_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalInt_x3f___boxed(lean_object* v_e_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_Meta_Grind_Arith_evalInt_x3f(v_e_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
lean_dec(v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
return v_res_1146_;
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

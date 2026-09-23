// Lean compiler output
// Module: Lean.Meta.Sym.Arith.EvalNum
// Imports: public import Lean.Meta.Sym.Arith.Types import Lean.Meta.Sym.LitValues import Lean.Meta.IntInstTesters import Lean.Meta.NatInstTesters
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
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_Arith_getExpThreshold___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
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
lean_object* l_Lean_Meta_Sym_getIntValue_x3f(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_abs(lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Arith_checkExp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_Arith_checkExp___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_checkExp___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_checkExp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "exponent "};
static const lean_object* l_Lean_Meta_Sym_Arith_checkExp___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_checkExp___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_checkExp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_checkExp___closed__2;
static const lean_string_object l_Lean_Meta_Sym_Arith_checkExp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = " exceeds threshold for exponentiation `(exp := "};
static const lean_object* l_Lean_Meta_Sym_Arith_checkExp___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_checkExp___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_checkExp___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_checkExp___closed__4;
static const lean_string_object l_Lean_Meta_Sym_Arith_checkExp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ")`"};
static const lean_object* l_Lean_Meta_Sym_Arith_checkExp___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_checkExp___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_checkExp___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_checkExp___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_checkExp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_checkExp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 81, 163, 94, 71, 156, 90, 186)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natAbs"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__4_value),LEAN_SCALAR_PTR_LITERAL(255, 186, 174, 182, 213, 167, 94, 168)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNat"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__6_value),LEAN_SCALAR_PTR_LITERAL(147, 74, 209, 32, 95, 50, 220, 192)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__8_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__10 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__11 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__10_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__11_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__12 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__13 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__13_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__14_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__15 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__16 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__17 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__16_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__18_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__17_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__18 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__19 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__20 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__19_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__21_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__20_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__21 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__22 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__23 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__23_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__22_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__23_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__24 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__25 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__26 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__25_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__26_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__27 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__27_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__28 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__28_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__29 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__28_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__29_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__30 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__30_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__31 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__31_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNatCastInt"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 224, 75, 57, 255, 108, 159, 197)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__2_value),LEAN_SCALAR_PTR_LITERAL(19, 237, 167, 212, 100, 179, 19, 112)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__4_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__5_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__7_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__8_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_evalNat_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_evalNat_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_evalInt_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_evalInt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_getOffset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_getOffset___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isOffset_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Sym_Arith_checkExp___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_checkExp___closed__1));
v___x_5_ = l_Lean_stringToMessageData(v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_checkExp___closed__4(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_checkExp___closed__3));
v___x_8_ = l_Lean_stringToMessageData(v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_checkExp___closed__6(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_checkExp___closed__5));
v___x_11_ = l_Lean_stringToMessageData(v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_checkExp(lean_object* v_k_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_Meta_Sym_Arith_getExpThreshold___redArg(v_a_14_, v_a_17_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_66_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_66_ == 0)
{
v___x_26_ = v___x_23_;
v_isShared_27_ = v_isSharedCheck_66_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_a_24_);
lean_dec(v___x_23_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_66_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
uint8_t v___x_28_; 
v___x_28_ = lean_nat_dec_lt(v_a_24_, v_k_12_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; lean_object* v___x_31_; 
lean_dec(v_a_24_);
lean_dec(v_k_12_);
v___x_29_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_checkExp___closed__0));
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v___x_29_);
v___x_31_ = v___x_26_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v___x_29_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
else
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
lean_del_object(v___x_26_);
v___x_33_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_checkExp___closed__2, &l_Lean_Meta_Sym_Arith_checkExp___closed__2_once, _init_l_Lean_Meta_Sym_Arith_checkExp___closed__2);
v___x_34_ = l_Nat_reprFast(v_k_12_);
v___x_35_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
v___x_36_ = l_Lean_MessageData_ofFormat(v___x_35_);
v___x_37_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_33_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
v___x_38_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_checkExp___closed__4, &l_Lean_Meta_Sym_Arith_checkExp___closed__4_once, _init_l_Lean_Meta_Sym_Arith_checkExp___closed__4);
v___x_39_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_37_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
v___x_40_ = l_Nat_reprFast(v_a_24_);
v___x_41_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
v___x_42_ = l_Lean_MessageData_ofFormat(v___x_41_);
v___x_43_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_39_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
v___x_44_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_checkExp___closed__6, &l_Lean_Meta_Sym_Arith_checkExp___closed__6_once, _init_l_Lean_Meta_Sym_Arith_checkExp___closed__6);
v___x_45_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_43_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
v___x_46_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_13_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v_a_47_; uint8_t v_verbose_48_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_a_47_);
lean_dec_ref_known(v___x_46_, 1);
v_verbose_48_ = lean_ctor_get_uint8(v_a_47_, 0);
lean_dec(v_a_47_);
if (v_verbose_48_ == 0)
{
lean_dec_ref_known(v___x_45_, 2);
goto v___jp_20_;
}
else
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Meta_Sym_reportIssue(v___x_45_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_dec_ref_known(v___x_49_, 1);
goto v___jp_20_;
}
else
{
lean_object* v_a_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_57_; 
v_a_50_ = lean_ctor_get(v___x_49_, 0);
v_isSharedCheck_57_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_57_ == 0)
{
v___x_52_ = v___x_49_;
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_a_50_);
lean_dec(v___x_49_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_57_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___x_55_; 
if (v_isShared_53_ == 0)
{
v___x_55_ = v___x_52_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_a_50_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
}
}
}
else
{
lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_65_; 
lean_dec_ref_known(v___x_45_, 2);
v_a_58_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_65_ == 0)
{
v___x_60_ = v___x_46_;
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_46_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_63_; 
if (v_isShared_61_ == 0)
{
v___x_63_ = v___x_60_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_a_58_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
}
}
else
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_74_; 
lean_dec(v_k_12_);
v_a_67_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_74_ == 0)
{
v___x_69_ = v___x_23_;
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_23_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_74_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_72_; 
if (v_isShared_70_ == 0)
{
v___x_72_ = v___x_69_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_a_67_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
v___jp_20_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_box(0);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_checkExp___boxed(lean_object* v_k_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Meta_Sym_Arith_checkExp(v_k_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(lean_object* v_e_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_i_168_; lean_object* v_a_169_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_175_; lean_object* v___x_227_; 
lean_inc_ref(v_e_156_);
v___x_227_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_156_, v_a_160_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_590_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_590_ == 0)
{
v___x_230_ = v___x_227_;
v_isShared_231_ = v_isSharedCheck_590_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_227_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_590_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_232_ = l_Lean_Expr_cleanupAnnotations(v_a_228_);
v___x_233_ = l_Lean_Expr_isApp(v___x_232_);
if (v___x_233_ == 0)
{
lean_dec_ref(v___x_232_);
lean_del_object(v___x_230_);
lean_dec_ref(v_e_156_);
goto v___jp_164_;
}
else
{
lean_object* v_arg_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v_arg_234_ = lean_ctor_get(v___x_232_, 1);
lean_inc_ref(v_arg_234_);
v___x_235_ = l_Lean_Expr_appFnCleanup___redArg(v___x_232_);
v___x_236_ = l_Lean_Expr_isApp(v___x_235_);
if (v___x_236_ == 0)
{
lean_dec_ref(v___x_235_);
lean_dec_ref(v_arg_234_);
lean_del_object(v___x_230_);
lean_dec_ref(v_e_156_);
goto v___jp_164_;
}
else
{
lean_object* v_arg_237_; lean_object* v___x_238_; uint8_t v___x_239_; 
v_arg_237_ = lean_ctor_get(v___x_235_, 1);
lean_inc_ref(v_arg_237_);
v___x_238_ = l_Lean_Expr_appFnCleanup___redArg(v___x_235_);
v___x_239_ = l_Lean_Expr_isApp(v___x_238_);
if (v___x_239_ == 0)
{
lean_dec_ref(v___x_238_);
lean_dec_ref(v_arg_237_);
lean_dec_ref(v_arg_234_);
lean_del_object(v___x_230_);
lean_dec_ref(v_e_156_);
goto v___jp_164_;
}
else
{
lean_object* v_arg_240_; lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v_arg_240_ = lean_ctor_get(v___x_238_, 1);
lean_inc_ref(v_arg_240_);
v___x_241_ = l_Lean_Expr_appFnCleanup___redArg(v___x_238_);
v___x_242_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__3));
v___x_243_ = l_Lean_Expr_isConstOf(v___x_241_, v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__6));
v___x_245_ = l_Lean_Expr_isConstOf(v___x_241_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_246_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__12));
v___x_247_ = l_Lean_Expr_isConstOf(v___x_241_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; uint8_t v___x_249_; 
lean_del_object(v___x_230_);
lean_dec_ref(v_e_156_);
v___x_248_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__9));
v___x_249_ = l_Lean_Expr_isConstOf(v___x_241_, v___x_248_);
if (v___x_249_ == 0)
{
uint8_t v___x_250_; 
v___x_250_ = l_Lean_Expr_isApp(v___x_241_);
if (v___x_250_ == 0)
{
lean_dec_ref(v___x_241_);
lean_dec_ref(v_arg_240_);
lean_dec_ref(v_arg_237_);
lean_dec_ref(v_arg_234_);
goto v___jp_164_;
}
else
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = l_Lean_Expr_appFnCleanup___redArg(v___x_241_);
v___x_252_ = l_Lean_Expr_isApp(v___x_251_);
if (v___x_252_ == 0)
{
lean_dec_ref(v___x_251_);
lean_dec_ref(v_arg_240_);
lean_dec_ref(v_arg_237_);
lean_dec_ref(v_arg_234_);
goto v___jp_164_;
}
else
{
lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_253_ = l_Lean_Expr_appFnCleanup___redArg(v___x_251_);
v___x_254_ = l_Lean_Expr_isApp(v___x_253_);
if (v___x_254_ == 0)
{
lean_dec_ref(v___x_253_);
lean_dec_ref(v_arg_240_);
lean_dec_ref(v_arg_237_);
lean_dec_ref(v_arg_234_);
goto v___jp_164_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_255_ = l_Lean_Expr_appFnCleanup___redArg(v___x_253_);
v___x_256_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__15));
v___x_257_ = l_Lean_Expr_isConstOf(v___x_255_, v___x_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__18));
v___x_259_ = l_Lean_Expr_isConstOf(v___x_255_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__21));
v___x_261_ = l_Lean_Expr_isConstOf(v___x_255_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_262_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__27));
v___x_263_ = l_Lean_Expr_isConstOf(v___x_255_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__24));
v___x_265_ = l_Lean_Expr_isConstOf(v___x_255_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__30));
v___x_267_ = l_Lean_Expr_isConstOf(v___x_255_, v___x_266_);
lean_dec_ref(v___x_255_);
if (v___x_267_ == 0)
{
lean_dec_ref(v_arg_240_);
lean_dec_ref(v_arg_237_);
lean_dec_ref(v_arg_234_);
goto v___jp_164_;
}
else
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_240_, v_a_160_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_300_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_300_ == 0)
{
v___x_271_ = v___x_268_;
v_isShared_272_ = v_isSharedCheck_300_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_268_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_300_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
uint8_t v___x_273_; 
v___x_273_ = lean_unbox(v_a_269_);
lean_dec(v_a_269_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_276_; 
lean_dec_ref(v_arg_237_);
lean_dec_ref(v_arg_234_);
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
else
{
lean_object* v___x_278_; 
lean_del_object(v___x_271_);
v___x_278_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_237_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_279_);
if (lean_obj_tag(v_a_279_) == 0)
{
lean_dec_ref(v_arg_234_);
return v___x_278_;
}
else
{
lean_object* v_val_280_; lean_object* v___x_281_; 
lean_dec_ref_known(v___x_278_, 1);
v_val_280_ = lean_ctor_get(v_a_279_, 0);
lean_inc(v_val_280_);
lean_dec_ref_known(v_a_279_, 1);
v___x_281_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_234_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_a_282_; 
v_a_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_a_282_);
if (lean_obj_tag(v_a_282_) == 0)
{
lean_dec(v_val_280_);
return v___x_281_;
}
else
{
lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_298_; 
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; 
v_unused_299_ = lean_ctor_get(v___x_281_, 0);
lean_dec(v_unused_299_);
v___x_284_ = v___x_281_;
v_isShared_285_ = v_isSharedCheck_298_;
goto v_resetjp_283_;
}
else
{
lean_dec(v___x_281_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_298_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v_val_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_297_; 
v_val_286_ = lean_ctor_get(v_a_282_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v_a_282_);
if (v_isSharedCheck_297_ == 0)
{
v___x_288_ = v_a_282_;
v_isShared_289_ = v_isSharedCheck_297_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_val_286_);
lean_dec(v_a_282_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_297_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_290_ = lean_int_add(v_val_280_, v_val_286_);
lean_dec(v_val_286_);
lean_dec(v_val_280_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_290_);
v___x_292_ = v___x_288_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_296_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_294_; 
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v___x_292_);
v___x_294_ = v___x_284_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
}
}
else
{
lean_dec(v_val_280_);
return v___x_281_;
}
}
}
else
{
lean_dec_ref(v_arg_234_);
return v___x_278_;
}
}
}
}
else
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
lean_dec_ref(v_arg_237_);
lean_dec_ref(v_arg_234_);
v_a_301_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_268_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_268_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
}
else
{
lean_object* v___x_309_; 
lean_dec_ref(v___x_255_);
v___x_309_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_arg_240_, v_a_160_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_341_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_341_ == 0)
{
v___x_312_ = v___x_309_;
v_isShared_313_ = v_isSharedCheck_341_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_a_310_);
lean_dec(v___x_309_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_341_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
uint8_t v___x_314_; 
v___x_314_ = lean_unbox(v_a_310_);
lean_dec(v_a_310_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_317_; 
lean_dec_ref(v_arg_237_);
lean_dec_ref(v_arg_234_);
v___x_315_ = lean_box(0);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v___x_315_);
v___x_317_ = v___x_312_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
else
{
lean_object* v___x_319_; 
lean_del_object(v___x_312_);
v___x_319_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_237_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_320_);
if (lean_obj_tag(v_a_320_) == 0)
{
lean_dec_ref(v_arg_234_);
return v___x_319_;
}
else
{
lean_object* v_val_321_; lean_object* v___x_322_; 
lean_dec_ref_known(v___x_319_, 1);
v_val_321_ = lean_ctor_get(v_a_320_, 0);
lean_inc(v_val_321_);
lean_dec_ref_known(v_a_320_, 1);
v___x_322_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_234_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_323_);
if (lean_obj_tag(v_a_323_) == 0)
{
lean_dec(v_val_321_);
return v___x_322_;
}
else
{
lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_339_; 
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_339_ == 0)
{
lean_object* v_unused_340_; 
v_unused_340_ = lean_ctor_get(v___x_322_, 0);
lean_dec(v_unused_340_);
v___x_325_ = v___x_322_;
v_isShared_326_ = v_isSharedCheck_339_;
goto v_resetjp_324_;
}
else
{
lean_dec(v___x_322_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_339_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v_val_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_338_; 
v_val_327_ = lean_ctor_get(v_a_323_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v_a_323_);
if (v_isSharedCheck_338_ == 0)
{
v___x_329_ = v_a_323_;
v_isShared_330_ = v_isSharedCheck_338_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_val_327_);
lean_dec(v_a_323_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_338_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_331_ = lean_int_sub(v_val_321_, v_val_327_);
lean_dec(v_val_327_);
lean_dec(v_val_321_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_331_);
v___x_333_ = v___x_329_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_331_);
v___x_333_ = v_reuseFailAlloc_337_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_335_; 
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v___x_333_);
v___x_335_ = v___x_325_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
}
else
{
lean_dec(v_val_321_);
return v___x_322_;
}
}
}
else
{
lean_dec_ref(v_arg_234_);
return v___x_319_;
}
}
}
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec_ref(v_arg_237_);
lean_dec_ref(v_arg_234_);
v_a_342_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_309_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_309_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
}
else
{
lean_object* v___x_350_; 
lean_dec_ref(v___x_255_);
v___x_350_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_240_, v_a_160_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_382_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_382_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_382_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_382_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
uint8_t v___x_355_; 
v___x_355_ = lean_unbox(v_a_351_);
lean_dec(v_a_351_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; lean_object* v___x_358_; 
lean_dec_ref(v_arg_237_);
lean_dec_ref(v_arg_234_);
v___x_356_ = lean_box(0);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_356_);
v___x_358_ = v___x_353_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
else
{
lean_object* v___x_360_; 
lean_del_object(v___x_353_);
v___x_360_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_237_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_a_361_);
if (lean_obj_tag(v_a_361_) == 0)
{
lean_dec_ref(v_arg_234_);
return v___x_360_;
}
else
{
lean_object* v_val_362_; lean_object* v___x_363_; 
lean_dec_ref_known(v___x_360_, 1);
v_val_362_ = lean_ctor_get(v_a_361_, 0);
lean_inc(v_val_362_);
lean_dec_ref_known(v_a_361_, 1);
v___x_363_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_234_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
if (lean_obj_tag(v_a_364_) == 0)
{
lean_dec(v_val_362_);
return v___x_363_;
}
else
{
lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_380_; 
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; 
v_unused_381_ = lean_ctor_get(v___x_363_, 0);
lean_dec(v_unused_381_);
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_380_;
goto v_resetjp_365_;
}
else
{
lean_dec(v___x_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_380_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v_val_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_379_; 
v_val_368_ = lean_ctor_get(v_a_364_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v_a_364_);
if (v_isSharedCheck_379_ == 0)
{
v___x_370_ = v_a_364_;
v_isShared_371_ = v_isSharedCheck_379_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_val_368_);
lean_dec(v_a_364_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_379_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = lean_int_mul(v_val_362_, v_val_368_);
lean_dec(v_val_368_);
lean_dec(v_val_362_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_372_);
v___x_374_ = v___x_370_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_372_);
v___x_374_ = v_reuseFailAlloc_378_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_376_; 
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_374_);
v___x_376_ = v___x_366_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
}
else
{
lean_dec(v_val_362_);
return v___x_363_;
}
}
}
else
{
lean_dec_ref(v_arg_234_);
return v___x_360_;
}
}
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec_ref(v_arg_237_);
lean_dec_ref(v_arg_234_);
v_a_383_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_350_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_350_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
else
{
lean_object* v___x_391_; 
lean_dec_ref(v___x_255_);
v___x_391_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_arg_240_, v_a_160_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_423_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_423_ == 0)
{
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_423_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_423_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
uint8_t v___x_396_; 
v___x_396_ = lean_unbox(v_a_392_);
lean_dec(v_a_392_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_399_; 
lean_dec_ref(v_arg_237_);
lean_dec_ref(v_arg_234_);
v___x_397_ = lean_box(0);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_397_);
v___x_399_ = v___x_394_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
else
{
lean_object* v___x_401_; 
lean_del_object(v___x_394_);
v___x_401_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_237_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
if (lean_obj_tag(v_a_402_) == 0)
{
lean_dec_ref(v_arg_234_);
return v___x_401_;
}
else
{
lean_object* v_val_403_; lean_object* v___x_404_; 
lean_dec_ref_known(v___x_401_, 1);
v_val_403_ = lean_ctor_get(v_a_402_, 0);
lean_inc(v_val_403_);
lean_dec_ref_known(v_a_402_, 1);
v___x_404_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_234_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
if (lean_obj_tag(v_a_405_) == 0)
{
lean_dec(v_val_403_);
return v___x_404_;
}
else
{
lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_421_; 
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v___x_404_, 0);
lean_dec(v_unused_422_);
v___x_407_ = v___x_404_;
v_isShared_408_ = v_isSharedCheck_421_;
goto v_resetjp_406_;
}
else
{
lean_dec(v___x_404_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_421_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v_val_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_420_; 
v_val_409_ = lean_ctor_get(v_a_405_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v_a_405_);
if (v_isSharedCheck_420_ == 0)
{
v___x_411_ = v_a_405_;
v_isShared_412_ = v_isSharedCheck_420_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_val_409_);
lean_dec(v_a_405_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_420_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_413_ = lean_int_ediv(v_val_403_, v_val_409_);
lean_dec(v_val_409_);
lean_dec(v_val_403_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_413_);
v___x_415_ = v___x_411_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_419_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
lean_object* v___x_417_; 
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___x_415_);
v___x_417_ = v___x_407_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
}
else
{
lean_dec(v_val_403_);
return v___x_404_;
}
}
}
else
{
lean_dec_ref(v_arg_234_);
return v___x_401_;
}
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
lean_dec_ref(v_arg_237_);
lean_dec_ref(v_arg_234_);
v_a_424_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_391_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_391_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
else
{
lean_object* v___x_432_; 
lean_dec_ref(v___x_255_);
v___x_432_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_arg_240_, v_a_160_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_464_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_464_ == 0)
{
v___x_435_ = v___x_432_;
v_isShared_436_ = v_isSharedCheck_464_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_432_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_464_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
uint8_t v___x_437_; 
v___x_437_ = lean_unbox(v_a_433_);
lean_dec(v_a_433_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_440_; 
lean_dec_ref(v_arg_237_);
lean_dec_ref(v_arg_234_);
v___x_438_ = lean_box(0);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_438_);
v___x_440_ = v___x_435_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_438_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
else
{
lean_object* v___x_442_; 
lean_del_object(v___x_435_);
v___x_442_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_237_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_a_443_);
if (lean_obj_tag(v_a_443_) == 0)
{
lean_dec_ref(v_arg_234_);
return v___x_442_;
}
else
{
lean_object* v_val_444_; lean_object* v___x_445_; 
lean_dec_ref_known(v___x_442_, 1);
v_val_444_ = lean_ctor_get(v_a_443_, 0);
lean_inc(v_val_444_);
lean_dec_ref_known(v_a_443_, 1);
v___x_445_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_234_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
if (lean_obj_tag(v_a_446_) == 0)
{
lean_dec(v_val_444_);
return v___x_445_;
}
else
{
lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_462_; 
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; 
v_unused_463_ = lean_ctor_get(v___x_445_, 0);
lean_dec(v_unused_463_);
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_462_;
goto v_resetjp_447_;
}
else
{
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_462_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v_val_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_461_; 
v_val_450_ = lean_ctor_get(v_a_446_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v_a_446_);
if (v_isSharedCheck_461_ == 0)
{
v___x_452_ = v_a_446_;
v_isShared_453_ = v_isSharedCheck_461_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_val_450_);
lean_dec(v_a_446_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_461_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_454_ = lean_int_emod(v_val_444_, v_val_450_);
lean_dec(v_val_450_);
lean_dec(v_val_444_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_454_);
v___x_456_ = v___x_452_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_460_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_458_; 
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_456_);
v___x_458_ = v___x_448_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
}
}
else
{
lean_dec(v_val_444_);
return v___x_445_;
}
}
}
else
{
lean_dec_ref(v_arg_234_);
return v___x_442_;
}
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec_ref(v_arg_237_);
lean_dec_ref(v_arg_234_);
v_a_465_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_432_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_432_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
else
{
lean_object* v___x_473_; 
lean_dec_ref(v___x_255_);
v___x_473_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_arg_240_, v_a_160_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_535_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_535_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_535_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_535_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
uint8_t v___x_478_; 
v___x_478_ = lean_unbox(v_a_474_);
lean_dec(v_a_474_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_481_; 
lean_dec_ref(v_arg_237_);
lean_dec_ref(v_arg_234_);
v___x_479_ = lean_box(0);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_479_);
v___x_481_ = v___x_476_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
else
{
lean_object* v___x_483_; 
lean_del_object(v___x_476_);
v___x_483_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_237_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
lean_inc(v_a_484_);
if (lean_obj_tag(v_a_484_) == 0)
{
lean_dec_ref(v_arg_234_);
return v___x_483_;
}
else
{
lean_object* v_val_485_; lean_object* v___x_486_; 
lean_dec_ref_known(v___x_483_, 1);
v_val_485_ = lean_ctor_get(v_a_484_, 0);
lean_inc(v_val_485_);
lean_dec_ref_known(v_a_484_, 1);
v___x_486_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_234_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_526_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_526_ == 0)
{
v___x_489_ = v___x_486_;
v_isShared_490_ = v_isSharedCheck_526_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_526_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
if (lean_obj_tag(v_a_487_) == 0)
{
lean_object* v___x_491_; lean_object* v___x_493_; 
lean_dec(v_val_485_);
v___x_491_ = lean_box(0);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_491_);
v___x_493_ = v___x_489_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
else
{
lean_object* v_val_495_; lean_object* v___x_496_; 
lean_del_object(v___x_489_);
v_val_495_ = lean_ctor_get(v_a_487_, 0);
lean_inc_n(v_val_495_, 2);
lean_dec_ref_known(v_a_487_, 1);
v___x_496_ = l_Lean_Meta_Sym_Arith_checkExp(v_val_495_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_517_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_517_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_517_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_517_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
if (lean_obj_tag(v_a_497_) == 0)
{
lean_object* v___x_501_; lean_object* v___x_503_; 
lean_dec(v_val_495_);
lean_dec(v_val_485_);
v___x_501_ = lean_box(0);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_501_);
v___x_503_ = v___x_499_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
else
{
lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_515_; 
v_isSharedCheck_515_ = !lean_is_exclusive(v_a_497_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; 
v_unused_516_ = lean_ctor_get(v_a_497_, 0);
lean_dec(v_unused_516_);
v___x_506_ = v_a_497_;
v_isShared_507_ = v_isSharedCheck_515_;
goto v_resetjp_505_;
}
else
{
lean_dec(v_a_497_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_515_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_508_ = l_Int_pow(v_val_485_, v_val_495_);
lean_dec(v_val_495_);
lean_dec(v_val_485_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_508_);
v___x_510_ = v___x_506_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_514_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_512_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_510_);
v___x_512_ = v___x_499_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec(v_val_495_);
lean_dec(v_val_485_);
v_a_518_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_496_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_496_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec(v_val_485_);
v_a_527_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_486_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_486_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_234_);
return v___x_483_;
}
}
}
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec_ref(v_arg_237_);
lean_dec_ref(v_arg_234_);
v_a_536_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_473_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_473_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
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
lean_object* v___x_544_; 
lean_dec_ref(v___x_241_);
lean_dec_ref(v_arg_240_);
v___x_544_ = l_Lean_Meta_Structural_isInstNegInt___redArg(v_arg_237_, v_a_160_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_573_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_573_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_573_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_573_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
uint8_t v___x_549_; 
v___x_549_ = lean_unbox(v_a_545_);
lean_dec(v_a_545_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; lean_object* v___x_552_; 
lean_dec_ref(v_arg_234_);
v___x_550_ = lean_box(0);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_550_);
v___x_552_ = v___x_547_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
else
{
lean_object* v___x_554_; 
lean_del_object(v___x_547_);
v___x_554_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_234_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
if (lean_obj_tag(v_a_555_) == 0)
{
return v___x_554_;
}
else
{
lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_571_; 
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_571_ == 0)
{
lean_object* v_unused_572_; 
v_unused_572_ = lean_ctor_get(v___x_554_, 0);
lean_dec(v_unused_572_);
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_571_;
goto v_resetjp_556_;
}
else
{
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_571_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v_val_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_570_; 
v_val_559_ = lean_ctor_get(v_a_555_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v_a_555_);
if (v_isSharedCheck_570_ == 0)
{
v___x_561_ = v_a_555_;
v_isShared_562_ = v_isSharedCheck_570_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_val_559_);
lean_dec(v_a_555_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_570_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = lean_int_neg(v_val_559_);
lean_dec(v_val_559_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_563_);
v___x_565_ = v_reuseFailAlloc_569_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_567_; 
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_565_);
v___x_567_ = v___x_557_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
}
else
{
return v___x_554_;
}
}
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_dec_ref(v_arg_234_);
v_a_574_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_544_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_544_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
}
else
{
lean_object* v___x_582_; 
lean_dec_ref(v___x_241_);
lean_dec_ref(v_arg_240_);
lean_dec_ref(v_arg_237_);
lean_dec_ref(v_arg_234_);
v___x_582_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_156_);
if (lean_obj_tag(v___x_582_) == 1)
{
lean_object* v___x_584_; 
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_582_);
v___x_584_ = v___x_230_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
else
{
lean_object* v___x_586_; lean_object* v___x_588_; 
lean_dec(v___x_582_);
v___x_586_ = lean_box(0);
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v___x_586_);
v___x_588_ = v___x_230_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
else
{
lean_dec_ref(v___x_241_);
lean_dec_ref(v_arg_240_);
lean_del_object(v___x_230_);
lean_dec_ref(v_e_156_);
v_i_168_ = v_arg_237_;
v_a_169_ = v_arg_234_;
v___y_170_ = v_a_157_;
v___y_171_ = v_a_158_;
v___y_172_ = v_a_159_;
v___y_173_ = v_a_160_;
v___y_174_ = v_a_161_;
v___y_175_ = v_a_162_;
goto v___jp_167_;
}
}
else
{
lean_dec_ref(v___x_241_);
lean_dec_ref(v_arg_240_);
lean_del_object(v___x_230_);
lean_dec_ref(v_e_156_);
v_i_168_ = v_arg_237_;
v_a_169_ = v_arg_234_;
v___y_170_ = v_a_157_;
v___y_171_ = v_a_158_;
v___y_172_ = v_a_159_;
v___y_173_ = v_a_160_;
v___y_174_ = v_a_161_;
v___y_175_ = v_a_162_;
goto v___jp_167_;
}
}
}
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_dec_ref(v_e_156_);
v_a_591_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_227_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_227_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
v___jp_164_:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_box(0);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
v___jp_167_:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_i_168_, v___y_173_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_218_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_218_ == 0)
{
v___x_179_ = v___x_176_;
v_isShared_180_ = v_isSharedCheck_218_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_176_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_218_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_181_ = l_Lean_Expr_cleanupAnnotations(v_a_177_);
v___x_182_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__1));
v___x_183_ = l_Lean_Expr_isConstOf(v___x_181_, v___x_182_);
lean_dec_ref(v___x_181_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_186_; 
lean_dec_ref(v_a_169_);
v___x_184_ = lean_box(0);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_184_);
v___x_186_ = v___x_179_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
else
{
lean_object* v___x_188_; 
lean_del_object(v___x_179_);
v___x_188_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_a_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_209_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_209_ == 0)
{
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_209_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_209_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
if (lean_obj_tag(v_a_189_) == 0)
{
lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_193_ = lean_box(0);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_193_);
v___x_195_ = v___x_191_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_193_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
else
{
lean_object* v_val_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_208_; 
v_val_197_ = lean_ctor_get(v_a_189_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v_a_189_);
if (v_isSharedCheck_208_ == 0)
{
v___x_199_ = v_a_189_;
v_isShared_200_ = v_isSharedCheck_208_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_val_197_);
lean_dec(v_a_189_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_208_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_201_ = lean_nat_to_int(v_val_197_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 0, v___x_201_);
v___x_203_ = v___x_199_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_201_);
v___x_203_ = v_reuseFailAlloc_207_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
lean_object* v___x_205_; 
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_203_);
v___x_205_ = v___x_191_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
v_a_210_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_188_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_188_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
}
}
else
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
lean_dec_ref(v_a_169_);
v_a_219_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_176_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_176_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_a_219_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(lean_object* v_e_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v___x_610_; 
lean_inc_ref(v_e_599_);
v___x_610_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_599_, v_a_603_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_1009_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_1009_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_1009_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_615_ = l_Lean_Expr_cleanupAnnotations(v_a_611_);
v___x_616_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__2));
v___x_617_ = l_Lean_Expr_isConstOf(v___x_615_, v___x_616_);
if (v___x_617_ == 0)
{
uint8_t v___x_618_; 
v___x_618_ = l_Lean_Expr_isApp(v___x_615_);
if (v___x_618_ == 0)
{
lean_dec_ref(v___x_615_);
lean_del_object(v___x_613_);
lean_dec_ref(v_e_599_);
goto v___jp_607_;
}
else
{
lean_object* v_arg_619_; lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v_arg_619_ = lean_ctor_get(v___x_615_, 1);
lean_inc_ref(v_arg_619_);
v___x_620_ = l_Lean_Expr_appFnCleanup___redArg(v___x_615_);
v___x_621_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__5));
v___x_622_ = l_Lean_Expr_isConstOf(v___x_620_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__7));
v___x_624_ = l_Lean_Expr_isConstOf(v___x_620_, v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_625_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__9));
v___x_626_ = l_Lean_Expr_isConstOf(v___x_620_, v___x_625_);
if (v___x_626_ == 0)
{
uint8_t v___x_627_; 
v___x_627_ = l_Lean_Expr_isApp(v___x_620_);
if (v___x_627_ == 0)
{
lean_dec_ref(v___x_620_);
lean_dec_ref(v_arg_619_);
lean_del_object(v___x_613_);
lean_dec_ref(v_e_599_);
goto v___jp_607_;
}
else
{
lean_object* v_arg_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v_arg_628_ = lean_ctor_get(v___x_620_, 1);
lean_inc_ref(v_arg_628_);
v___x_629_ = l_Lean_Expr_appFnCleanup___redArg(v___x_620_);
v___x_630_ = l_Lean_Expr_isApp(v___x_629_);
if (v___x_630_ == 0)
{
lean_dec_ref(v___x_629_);
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_619_);
lean_del_object(v___x_613_);
lean_dec_ref(v_e_599_);
goto v___jp_607_;
}
else
{
lean_object* v_arg_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v_arg_631_ = lean_ctor_get(v___x_629_, 1);
lean_inc_ref(v_arg_631_);
v___x_632_ = l_Lean_Expr_appFnCleanup___redArg(v___x_629_);
v___x_633_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__12));
v___x_634_ = l_Lean_Expr_isConstOf(v___x_632_, v___x_633_);
if (v___x_634_ == 0)
{
uint8_t v___x_635_; 
lean_del_object(v___x_613_);
lean_dec_ref(v_e_599_);
v___x_635_ = l_Lean_Expr_isApp(v___x_632_);
if (v___x_635_ == 0)
{
lean_dec_ref(v___x_632_);
lean_dec_ref(v_arg_631_);
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_619_);
goto v___jp_607_;
}
else
{
lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_636_ = l_Lean_Expr_appFnCleanup___redArg(v___x_632_);
v___x_637_ = l_Lean_Expr_isApp(v___x_636_);
if (v___x_637_ == 0)
{
lean_dec_ref(v___x_636_);
lean_dec_ref(v_arg_631_);
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_619_);
goto v___jp_607_;
}
else
{
lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_638_ = l_Lean_Expr_appFnCleanup___redArg(v___x_636_);
v___x_639_ = l_Lean_Expr_isApp(v___x_638_);
if (v___x_639_ == 0)
{
lean_dec_ref(v___x_638_);
lean_dec_ref(v_arg_631_);
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_619_);
goto v___jp_607_;
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_640_ = l_Lean_Expr_appFnCleanup___redArg(v___x_638_);
v___x_641_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__15));
v___x_642_ = l_Lean_Expr_isConstOf(v___x_640_, v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_643_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__18));
v___x_644_ = l_Lean_Expr_isConstOf(v___x_640_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__21));
v___x_646_ = l_Lean_Expr_isConstOf(v___x_640_, v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__24));
v___x_648_ = l_Lean_Expr_isConstOf(v___x_640_, v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__27));
v___x_650_ = l_Lean_Expr_isConstOf(v___x_640_, v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_651_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__30));
v___x_652_ = l_Lean_Expr_isConstOf(v___x_640_, v___x_651_);
lean_dec_ref(v___x_640_);
if (v___x_652_ == 0)
{
lean_dec_ref(v_arg_631_);
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_619_);
goto v___jp_607_;
}
else
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_631_, v_a_603_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_685_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_685_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_685_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_685_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
uint8_t v___x_658_; 
v___x_658_ = lean_unbox(v_a_654_);
lean_dec(v_a_654_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_661_; 
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_619_);
v___x_659_ = lean_box(0);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_659_);
v___x_661_ = v___x_656_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
else
{
lean_object* v___x_663_; 
lean_del_object(v___x_656_);
v___x_663_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_628_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_a_664_);
if (lean_obj_tag(v_a_664_) == 0)
{
lean_dec_ref(v_arg_619_);
return v___x_663_;
}
else
{
lean_object* v_val_665_; lean_object* v___x_666_; 
lean_dec_ref_known(v___x_663_, 1);
v_val_665_ = lean_ctor_get(v_a_664_, 0);
lean_inc(v_val_665_);
lean_dec_ref_known(v_a_664_, 1);
v___x_666_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_619_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
if (lean_obj_tag(v_a_667_) == 0)
{
lean_dec(v_val_665_);
return v___x_666_;
}
else
{
lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_683_; 
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_683_ == 0)
{
lean_object* v_unused_684_; 
v_unused_684_ = lean_ctor_get(v___x_666_, 0);
lean_dec(v_unused_684_);
v___x_669_ = v___x_666_;
v_isShared_670_ = v_isSharedCheck_683_;
goto v_resetjp_668_;
}
else
{
lean_dec(v___x_666_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_683_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v_val_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_682_; 
v_val_671_ = lean_ctor_get(v_a_667_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v_a_667_);
if (v_isSharedCheck_682_ == 0)
{
v___x_673_ = v_a_667_;
v_isShared_674_ = v_isSharedCheck_682_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_val_671_);
lean_dec(v_a_667_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_682_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = lean_nat_add(v_val_665_, v_val_671_);
lean_dec(v_val_671_);
lean_dec(v_val_665_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_675_);
v___x_677_ = v___x_673_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_681_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
lean_object* v___x_679_; 
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 0, v___x_677_);
v___x_679_ = v___x_669_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
}
else
{
lean_dec(v_val_665_);
return v___x_666_;
}
}
}
else
{
lean_dec_ref(v_arg_619_);
return v___x_663_;
}
}
}
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_619_);
v_a_686_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_653_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_653_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
else
{
lean_object* v___x_694_; 
lean_dec_ref(v___x_640_);
v___x_694_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_arg_631_, v_a_603_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_726_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_726_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_726_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_726_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
uint8_t v___x_699_; 
v___x_699_ = lean_unbox(v_a_695_);
lean_dec(v_a_695_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_702_; 
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_619_);
v___x_700_ = lean_box(0);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_700_);
v___x_702_ = v___x_697_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
else
{
lean_object* v___x_704_; 
lean_del_object(v___x_697_);
v___x_704_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_628_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
if (lean_obj_tag(v_a_705_) == 0)
{
lean_dec_ref(v_arg_619_);
return v___x_704_;
}
else
{
lean_object* v_val_706_; lean_object* v___x_707_; 
lean_dec_ref_known(v___x_704_, 1);
v_val_706_ = lean_ctor_get(v_a_705_, 0);
lean_inc(v_val_706_);
lean_dec_ref_known(v_a_705_, 1);
v___x_707_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_619_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
if (lean_obj_tag(v_a_708_) == 0)
{
lean_dec(v_val_706_);
return v___x_707_;
}
else
{
lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_724_; 
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v___x_707_, 0);
lean_dec(v_unused_725_);
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_724_;
goto v_resetjp_709_;
}
else
{
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_724_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v_val_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_723_; 
v_val_712_ = lean_ctor_get(v_a_708_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v_a_708_);
if (v_isSharedCheck_723_ == 0)
{
v___x_714_ = v_a_708_;
v_isShared_715_ = v_isSharedCheck_723_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_val_712_);
lean_dec(v_a_708_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_723_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_716_ = lean_nat_mul(v_val_706_, v_val_712_);
lean_dec(v_val_712_);
lean_dec(v_val_706_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_716_);
v___x_718_ = v___x_714_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_722_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_720_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_718_);
v___x_720_ = v___x_710_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
}
else
{
lean_dec(v_val_706_);
return v___x_707_;
}
}
}
else
{
lean_dec_ref(v_arg_619_);
return v___x_704_;
}
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_619_);
v_a_727_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_694_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_694_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
else
{
lean_object* v___x_735_; 
lean_dec_ref(v___x_640_);
v___x_735_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_arg_631_, v_a_603_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_767_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_767_ == 0)
{
v___x_738_ = v___x_735_;
v_isShared_739_ = v_isSharedCheck_767_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_735_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_767_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
uint8_t v___x_740_; 
v___x_740_ = lean_unbox(v_a_736_);
lean_dec(v_a_736_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___x_743_; 
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_619_);
v___x_741_ = lean_box(0);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 0, v___x_741_);
v___x_743_ = v___x_738_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
else
{
lean_object* v___x_745_; 
lean_del_object(v___x_738_);
v___x_745_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_628_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_746_);
if (lean_obj_tag(v_a_746_) == 0)
{
lean_dec_ref(v_arg_619_);
return v___x_745_;
}
else
{
lean_object* v_val_747_; lean_object* v___x_748_; 
lean_dec_ref_known(v___x_745_, 1);
v_val_747_ = lean_ctor_get(v_a_746_, 0);
lean_inc(v_val_747_);
lean_dec_ref_known(v_a_746_, 1);
v___x_748_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_619_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
if (lean_obj_tag(v_a_749_) == 0)
{
lean_dec(v_val_747_);
return v___x_748_;
}
else
{
lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_765_; 
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v___x_748_, 0);
lean_dec(v_unused_766_);
v___x_751_ = v___x_748_;
v_isShared_752_ = v_isSharedCheck_765_;
goto v_resetjp_750_;
}
else
{
lean_dec(v___x_748_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_765_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_val_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_764_; 
v_val_753_ = lean_ctor_get(v_a_749_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v_a_749_);
if (v_isSharedCheck_764_ == 0)
{
v___x_755_ = v_a_749_;
v_isShared_756_ = v_isSharedCheck_764_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_val_753_);
lean_dec(v_a_749_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_764_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_757_ = lean_nat_sub(v_val_747_, v_val_753_);
lean_dec(v_val_753_);
lean_dec(v_val_747_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_757_);
v___x_759_ = v___x_755_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_763_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_761_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_759_);
v___x_761_ = v___x_751_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_759_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
}
else
{
lean_dec(v_val_747_);
return v___x_748_;
}
}
}
else
{
lean_dec_ref(v_arg_619_);
return v___x_745_;
}
}
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_619_);
v_a_768_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_735_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_735_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
else
{
lean_object* v___x_776_; 
lean_dec_ref(v___x_640_);
v___x_776_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_arg_631_, v_a_603_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_808_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_808_ == 0)
{
v___x_779_ = v___x_776_;
v_isShared_780_ = v_isSharedCheck_808_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_776_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_808_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
uint8_t v___x_781_; 
v___x_781_ = lean_unbox(v_a_777_);
lean_dec(v_a_777_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; lean_object* v___x_784_; 
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_619_);
v___x_782_ = lean_box(0);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_782_);
v___x_784_ = v___x_779_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
else
{
lean_object* v___x_786_; 
lean_del_object(v___x_779_);
v___x_786_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_628_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
if (lean_obj_tag(v_a_787_) == 0)
{
lean_dec_ref(v_arg_619_);
return v___x_786_;
}
else
{
lean_object* v_val_788_; lean_object* v___x_789_; 
lean_dec_ref_known(v___x_786_, 1);
v_val_788_ = lean_ctor_get(v_a_787_, 0);
lean_inc(v_val_788_);
lean_dec_ref_known(v_a_787_, 1);
v___x_789_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_619_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
if (lean_obj_tag(v_a_790_) == 0)
{
lean_dec(v_val_788_);
return v___x_789_;
}
else
{
lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_806_; 
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_806_ == 0)
{
lean_object* v_unused_807_; 
v_unused_807_ = lean_ctor_get(v___x_789_, 0);
lean_dec(v_unused_807_);
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_806_;
goto v_resetjp_791_;
}
else
{
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_806_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v_val_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_805_; 
v_val_794_ = lean_ctor_get(v_a_790_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v_a_790_);
if (v_isSharedCheck_805_ == 0)
{
v___x_796_ = v_a_790_;
v_isShared_797_ = v_isSharedCheck_805_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_val_794_);
lean_dec(v_a_790_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_805_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = lean_nat_div(v_val_788_, v_val_794_);
lean_dec(v_val_794_);
lean_dec(v_val_788_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_798_);
v___x_800_ = v___x_796_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_804_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_802_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_800_);
v___x_802_ = v___x_792_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
}
else
{
lean_dec(v_val_788_);
return v___x_789_;
}
}
}
else
{
lean_dec_ref(v_arg_619_);
return v___x_786_;
}
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_619_);
v_a_809_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_776_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_776_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
else
{
lean_object* v___x_817_; 
lean_dec_ref(v___x_640_);
v___x_817_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_arg_631_, v_a_603_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_849_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_849_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_849_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_849_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
uint8_t v___x_822_; 
v___x_822_ = lean_unbox(v_a_818_);
lean_dec(v_a_818_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_825_; 
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_619_);
v___x_823_ = lean_box(0);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_823_);
v___x_825_ = v___x_820_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_823_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
else
{
lean_object* v___x_827_; 
lean_del_object(v___x_820_);
v___x_827_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_628_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
if (lean_obj_tag(v_a_828_) == 0)
{
lean_dec_ref(v_arg_619_);
return v___x_827_;
}
else
{
lean_object* v_val_829_; lean_object* v___x_830_; 
lean_dec_ref_known(v___x_827_, 1);
v_val_829_ = lean_ctor_get(v_a_828_, 0);
lean_inc(v_val_829_);
lean_dec_ref_known(v_a_828_, 1);
v___x_830_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_619_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
if (lean_obj_tag(v_a_831_) == 0)
{
lean_dec(v_val_829_);
return v___x_830_;
}
else
{
lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_847_; 
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_847_ == 0)
{
lean_object* v_unused_848_; 
v_unused_848_ = lean_ctor_get(v___x_830_, 0);
lean_dec(v_unused_848_);
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_847_;
goto v_resetjp_832_;
}
else
{
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_847_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v_val_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_846_; 
v_val_835_ = lean_ctor_get(v_a_831_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v_a_831_);
if (v_isSharedCheck_846_ == 0)
{
v___x_837_ = v_a_831_;
v_isShared_838_ = v_isSharedCheck_846_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_val_835_);
lean_dec(v_a_831_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_846_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_839_ = lean_nat_mod(v_val_829_, v_val_835_);
lean_dec(v_val_835_);
lean_dec(v_val_829_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_839_);
v___x_841_ = v___x_837_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_839_);
v___x_841_ = v_reuseFailAlloc_845_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
lean_object* v___x_843_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_841_);
v___x_843_ = v___x_833_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
}
}
else
{
lean_dec(v_val_829_);
return v___x_830_;
}
}
}
else
{
lean_dec_ref(v_arg_619_);
return v___x_827_;
}
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_619_);
v_a_850_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_817_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_817_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
else
{
lean_object* v___x_858_; 
lean_dec_ref(v___x_640_);
v___x_858_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_arg_631_, v_a_603_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_908_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_908_ == 0)
{
v___x_861_ = v___x_858_;
v_isShared_862_ = v_isSharedCheck_908_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_908_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
uint8_t v___x_863_; 
v___x_863_ = lean_unbox(v_a_859_);
lean_dec(v_a_859_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; lean_object* v___x_866_; 
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_619_);
v___x_864_ = lean_box(0);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_864_);
v___x_866_ = v___x_861_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
else
{
lean_object* v___x_868_; 
lean_del_object(v___x_861_);
v___x_868_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_619_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
if (lean_obj_tag(v_a_869_) == 0)
{
lean_dec_ref(v_arg_628_);
return v___x_868_;
}
else
{
lean_object* v_val_870_; lean_object* v___x_871_; 
lean_dec_ref_known(v___x_868_, 1);
v_val_870_ = lean_ctor_get(v_a_869_, 0);
lean_inc_n(v_val_870_, 2);
lean_dec_ref_known(v_a_869_, 1);
v___x_871_ = l_Lean_Meta_Sym_Arith_checkExp(v_val_870_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_899_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_899_ == 0)
{
v___x_874_ = v___x_871_;
v_isShared_875_ = v_isSharedCheck_899_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_899_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
if (lean_obj_tag(v_a_872_) == 0)
{
lean_object* v___x_876_; lean_object* v___x_878_; 
lean_dec(v_val_870_);
lean_dec_ref(v_arg_628_);
v___x_876_ = lean_box(0);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_876_);
v___x_878_ = v___x_874_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
else
{
lean_object* v___x_880_; 
lean_dec_ref_known(v_a_872_, 1);
lean_del_object(v___x_874_);
v___x_880_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_628_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
if (lean_obj_tag(v_a_881_) == 0)
{
lean_dec(v_val_870_);
return v___x_880_;
}
else
{
lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_897_; 
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_897_ == 0)
{
lean_object* v_unused_898_; 
v_unused_898_ = lean_ctor_get(v___x_880_, 0);
lean_dec(v_unused_898_);
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_897_;
goto v_resetjp_882_;
}
else
{
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_897_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v_val_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_896_; 
v_val_885_ = lean_ctor_get(v_a_881_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v_a_881_);
if (v_isSharedCheck_896_ == 0)
{
v___x_887_ = v_a_881_;
v_isShared_888_ = v_isSharedCheck_896_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_val_885_);
lean_dec(v_a_881_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_896_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_889_ = lean_nat_pow(v_val_885_, v_val_870_);
lean_dec(v_val_870_);
lean_dec(v_val_885_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_889_);
v___x_891_ = v___x_887_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_895_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_893_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_891_);
v___x_893_ = v___x_883_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
}
}
else
{
lean_dec(v_val_870_);
return v___x_880_;
}
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_dec(v_val_870_);
lean_dec_ref(v_arg_628_);
v_a_900_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_871_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_871_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_628_);
return v___x_868_;
}
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_619_);
v_a_909_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_858_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_858_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
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
lean_object* v___x_917_; 
lean_dec_ref(v___x_632_);
lean_dec_ref(v_arg_631_);
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_619_);
v___x_917_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_599_);
if (lean_obj_tag(v___x_917_) == 1)
{
lean_object* v___x_919_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_917_);
v___x_919_ = v___x_613_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
else
{
lean_object* v___x_921_; lean_object* v___x_923_; 
lean_dec(v___x_917_);
v___x_921_ = lean_box(0);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_921_);
v___x_923_ = v___x_613_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
}
else
{
lean_object* v___x_925_; 
lean_dec_ref(v___x_620_);
lean_del_object(v___x_613_);
lean_dec_ref(v_e_599_);
v___x_925_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_619_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
if (lean_obj_tag(v_a_926_) == 0)
{
return v___x_925_;
}
else
{
lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_943_; 
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_943_ == 0)
{
lean_object* v_unused_944_; 
v_unused_944_ = lean_ctor_get(v___x_925_, 0);
lean_dec(v_unused_944_);
v___x_928_ = v___x_925_;
v_isShared_929_ = v_isSharedCheck_943_;
goto v_resetjp_927_;
}
else
{
lean_dec(v___x_925_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_943_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v_val_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_942_; 
v_val_930_ = lean_ctor_get(v_a_926_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v_a_926_);
if (v_isSharedCheck_942_ == 0)
{
v___x_932_ = v_a_926_;
v_isShared_933_ = v_isSharedCheck_942_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_val_930_);
lean_dec(v_a_926_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_942_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_934_ = lean_unsigned_to_nat(1u);
v___x_935_ = lean_nat_add(v_val_930_, v___x_934_);
lean_dec(v_val_930_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_935_);
v___x_937_ = v___x_932_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_941_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_939_; 
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v___x_937_);
v___x_939_ = v___x_928_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
}
else
{
return v___x_925_;
}
}
}
else
{
lean_object* v___x_945_; 
lean_dec_ref(v___x_620_);
lean_del_object(v___x_613_);
lean_dec_ref(v_e_599_);
v___x_945_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_619_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_966_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_966_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_966_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_966_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
if (lean_obj_tag(v_a_946_) == 0)
{
lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_950_ = lean_box(0);
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_950_);
v___x_952_ = v___x_948_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
else
{
lean_object* v_val_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_965_; 
v_val_954_ = lean_ctor_get(v_a_946_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v_a_946_);
if (v_isSharedCheck_965_ == 0)
{
v___x_956_ = v_a_946_;
v_isShared_957_ = v_isSharedCheck_965_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_val_954_);
lean_dec(v_a_946_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_965_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_958_ = l_Int_toNat(v_val_954_);
lean_dec(v_val_954_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_958_);
v___x_960_ = v___x_956_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_958_);
v___x_960_ = v_reuseFailAlloc_964_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_962_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_960_);
v___x_962_ = v___x_948_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_960_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
v_a_967_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_945_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_945_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
else
{
lean_object* v___x_975_; 
lean_dec_ref(v___x_620_);
lean_del_object(v___x_613_);
lean_dec_ref(v_e_599_);
v___x_975_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_619_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_996_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_996_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_996_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_996_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
if (lean_obj_tag(v_a_976_) == 0)
{
lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_980_ = lean_box(0);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_980_);
v___x_982_ = v___x_978_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
else
{
lean_object* v_val_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_995_; 
v_val_984_ = lean_ctor_get(v_a_976_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v_a_976_);
if (v_isSharedCheck_995_ == 0)
{
v___x_986_ = v_a_976_;
v_isShared_987_ = v_isSharedCheck_995_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_val_984_);
lean_dec(v_a_976_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_995_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_988_ = lean_nat_abs(v_val_984_);
lean_dec(v_val_984_);
if (v_isShared_987_ == 0)
{
lean_ctor_set(v___x_986_, 0, v___x_988_);
v___x_990_ = v___x_986_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_994_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_992_; 
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_990_);
v___x_992_ = v___x_978_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
v_a_997_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_975_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_975_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
}
}
else
{
lean_object* v___x_1005_; lean_object* v___x_1007_; 
lean_dec_ref(v___x_615_);
lean_dec_ref(v_e_599_);
v___x_1005_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__31));
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_1005_);
v___x_1007_ = v___x_613_;
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
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_dec_ref(v_e_599_);
v_a_1010_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_610_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_610_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
v___jp_607_:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = lean_box(0);
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___boxed(lean_object* v_e_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_e_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___boxed(lean_object* v_e_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_e_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore_spec__1(lean_object* v_a_1036_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_nat_to_int(v_a_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_evalNat_x3f(lean_object* v_e_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_e_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_evalNat_x3f___boxed(lean_object* v_e_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_Meta_Sym_Arith_evalNat_x3f(v_e_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_evalInt_x3f(lean_object* v_e_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_e_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_evalInt_x3f___boxed(lean_object* v_e_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_Meta_Sym_Arith_evalInt_x3f(v_e_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isOffset_x3f(lean_object* v_e_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1074_, v_a_1078_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v___x_1085_, 1);
v___x_1087_ = l_Lean_Expr_cleanupAnnotations(v_a_1086_);
v___x_1088_ = l_Lean_Expr_isApp(v___x_1087_);
if (v___x_1088_ == 0)
{
lean_dec_ref(v___x_1087_);
goto v___jp_1082_;
}
else
{
lean_object* v_arg_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; 
v_arg_1089_ = lean_ctor_get(v___x_1087_, 1);
lean_inc_ref(v_arg_1089_);
v___x_1090_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1087_);
v___x_1091_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__9));
v___x_1092_ = l_Lean_Expr_isConstOf(v___x_1090_, v___x_1091_);
if (v___x_1092_ == 0)
{
uint8_t v___x_1093_; 
v___x_1093_ = l_Lean_Expr_isApp(v___x_1090_);
if (v___x_1093_ == 0)
{
lean_dec_ref(v___x_1090_);
lean_dec_ref(v_arg_1089_);
goto v___jp_1082_;
}
else
{
lean_object* v_arg_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v_arg_1094_ = lean_ctor_get(v___x_1090_, 1);
lean_inc_ref(v_arg_1094_);
v___x_1095_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1090_);
v___x_1096_ = l_Lean_Expr_isApp(v___x_1095_);
if (v___x_1096_ == 0)
{
lean_dec_ref(v___x_1095_);
lean_dec_ref(v_arg_1094_);
lean_dec_ref(v_arg_1089_);
goto v___jp_1082_;
}
else
{
lean_object* v_arg_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v_arg_1097_ = lean_ctor_get(v___x_1095_, 1);
lean_inc_ref(v_arg_1097_);
v___x_1098_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1095_);
v___x_1099_ = l_Lean_Expr_isApp(v___x_1098_);
if (v___x_1099_ == 0)
{
lean_dec_ref(v___x_1098_);
lean_dec_ref(v_arg_1097_);
lean_dec_ref(v_arg_1094_);
lean_dec_ref(v_arg_1089_);
goto v___jp_1082_;
}
else
{
lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1098_);
v___x_1101_ = l_Lean_Expr_isApp(v___x_1100_);
if (v___x_1101_ == 0)
{
lean_dec_ref(v___x_1100_);
lean_dec_ref(v_arg_1097_);
lean_dec_ref(v_arg_1094_);
lean_dec_ref(v_arg_1089_);
goto v___jp_1082_;
}
else
{
lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_1102_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1100_);
v___x_1103_ = l_Lean_Expr_isApp(v___x_1102_);
if (v___x_1103_ == 0)
{
lean_dec_ref(v___x_1102_);
lean_dec_ref(v_arg_1097_);
lean_dec_ref(v_arg_1094_);
lean_dec_ref(v_arg_1089_);
goto v___jp_1082_;
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1104_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1102_);
v___x_1105_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__30));
v___x_1106_ = l_Lean_Expr_isConstOf(v___x_1104_, v___x_1105_);
lean_dec_ref(v___x_1104_);
if (v___x_1106_ == 0)
{
lean_dec_ref(v_arg_1097_);
lean_dec_ref(v_arg_1094_);
lean_dec_ref(v_arg_1089_);
goto v___jp_1082_;
}
else
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_1097_, v_a_1078_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1170_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1170_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1170_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
uint8_t v___x_1112_; 
v___x_1112_ = lean_unbox(v_a_1108_);
lean_dec(v_a_1108_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; lean_object* v___x_1115_; 
lean_dec_ref(v_arg_1094_);
lean_dec_ref(v_arg_1089_);
v___x_1113_ = lean_box(0);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1113_);
v___x_1115_ = v___x_1110_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
else
{
lean_object* v___x_1117_; 
lean_del_object(v___x_1110_);
v___x_1117_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_1089_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1161_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1161_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1161_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
if (lean_obj_tag(v_a_1118_) == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1124_; 
lean_dec_ref(v_arg_1094_);
v___x_1122_ = lean_box(0);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1122_);
v___x_1124_ = v___x_1120_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
else
{
lean_object* v_val_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1160_; 
lean_del_object(v___x_1120_);
v_val_1126_ = lean_ctor_get(v_a_1118_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_a_1118_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1128_ = v_a_1118_;
v_isShared_1129_ = v_isSharedCheck_1160_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_val_1126_);
lean_dec(v_a_1118_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1160_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; 
v___x_1130_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_getOffset(v_arg_1094_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1151_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1151_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1151_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v_fst_1135_; lean_object* v_snd_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1150_; 
v_fst_1135_ = lean_ctor_get(v_a_1131_, 0);
v_snd_1136_ = lean_ctor_get(v_a_1131_, 1);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_a_1131_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1138_ = v_a_1131_;
v_isShared_1139_ = v_isSharedCheck_1150_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_snd_1136_);
lean_inc(v_fst_1135_);
lean_dec(v_a_1131_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1150_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1140_ = lean_nat_add(v_snd_1136_, v_val_1126_);
lean_dec(v_val_1126_);
lean_dec(v_snd_1136_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v___x_1140_);
v___x_1142_ = v___x_1138_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_fst_1135_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1144_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v___x_1142_);
v___x_1144_ = v___x_1128_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1146_; 
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1144_);
v___x_1146_ = v___x_1133_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1144_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_del_object(v___x_1128_);
lean_dec(v_val_1126_);
v_a_1152_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1130_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1130_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
lean_dec_ref(v_arg_1094_);
v_a_1162_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1117_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1117_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
}
}
}
}
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec_ref(v_arg_1094_);
lean_dec_ref(v_arg_1089_);
v_a_1171_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1107_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1107_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
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
lean_object* v___x_1179_; 
lean_dec_ref(v___x_1090_);
v___x_1179_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_getOffset(v_arg_1089_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1199_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1182_ = v___x_1179_;
v_isShared_1183_ = v_isSharedCheck_1199_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1179_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1199_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v_fst_1184_; lean_object* v_snd_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1198_; 
v_fst_1184_ = lean_ctor_get(v_a_1180_, 0);
v_snd_1185_ = lean_ctor_get(v_a_1180_, 1);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_a_1180_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1187_ = v_a_1180_;
v_isShared_1188_ = v_isSharedCheck_1198_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_snd_1185_);
lean_inc(v_fst_1184_);
lean_dec(v_a_1180_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1198_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1189_ = lean_unsigned_to_nat(1u);
v___x_1190_ = lean_nat_add(v_snd_1185_, v___x_1189_);
lean_dec(v_snd_1185_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 1, v___x_1190_);
v___x_1192_ = v___x_1187_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_fst_1184_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1193_);
v___x_1195_ = v___x_1182_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
v_a_1200_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1179_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1179_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
v_a_1208_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1085_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1085_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
v___jp_1082_:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_getOffset(lean_object* v_e_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v___x_1224_; 
lean_inc_ref(v_e_1216_);
v___x_1224_ = l_Lean_Meta_Sym_Arith_isOffset_x3f(v_e_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1238_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1238_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1238_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
if (lean_obj_tag(v_a_1225_) == 0)
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1232_; 
v___x_1229_ = lean_unsigned_to_nat(0u);
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v_e_1216_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1230_);
v___x_1232_ = v___x_1227_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v___x_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
else
{
lean_object* v_val_1234_; lean_object* v___x_1236_; 
lean_dec_ref(v_e_1216_);
v_val_1234_ = lean_ctor_get(v_a_1225_, 0);
lean_inc(v_val_1234_);
lean_dec_ref_known(v_a_1225_, 1);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v_val_1234_);
v___x_1236_ = v___x_1227_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_val_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_dec_ref(v_e_1216_);
v_a_1239_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1224_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1224_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_getOffset___boxed(lean_object* v_e_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_getOffset(v_e_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
lean_dec(v_a_1251_);
lean_dec_ref(v_a_1250_);
lean_dec(v_a_1249_);
lean_dec_ref(v_a_1248_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isOffset_x3f___boxed(lean_object* v_e_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_Meta_Sym_Arith_isOffset_x3f(v_e_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_);
lean_dec(v_a_1262_);
lean_dec_ref(v_a_1261_);
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
return v_res_1264_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_EvalNum(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Arith_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_EvalNum(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_EvalNum(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Arith_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_EvalNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_EvalNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_EvalNum(builtin);
}
#ifdef __cplusplus
}
#endif

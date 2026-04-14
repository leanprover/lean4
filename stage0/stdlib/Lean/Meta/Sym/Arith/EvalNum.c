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
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l_Lean_Meta_Sym_Arith_getExpThreshold___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_abs(lean_object*);
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
lean_object* v___x_33_; 
lean_del_object(v___x_26_);
v___x_33_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_13_);
if (lean_obj_tag(v___x_33_) == 0)
{
lean_object* v_a_34_; uint8_t v___x_35_; 
v_a_34_ = lean_ctor_get(v___x_33_, 0);
lean_inc(v_a_34_);
lean_dec_ref(v___x_33_);
v___x_35_ = lean_unbox(v_a_34_);
lean_dec(v_a_34_);
if (v___x_35_ == 0)
{
lean_dec(v_a_24_);
lean_dec(v_k_12_);
goto v___jp_20_;
}
else
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_36_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_checkExp___closed__2, &l_Lean_Meta_Sym_Arith_checkExp___closed__2_once, _init_l_Lean_Meta_Sym_Arith_checkExp___closed__2);
v___x_37_ = l_Nat_reprFast(v_k_12_);
v___x_38_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
v___x_39_ = l_Lean_MessageData_ofFormat(v___x_38_);
v___x_40_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_36_);
lean_ctor_set(v___x_40_, 1, v___x_39_);
v___x_41_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_checkExp___closed__4, &l_Lean_Meta_Sym_Arith_checkExp___closed__4_once, _init_l_Lean_Meta_Sym_Arith_checkExp___closed__4);
v___x_42_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_40_);
lean_ctor_set(v___x_42_, 1, v___x_41_);
v___x_43_ = l_Nat_reprFast(v_a_24_);
v___x_44_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
v___x_45_ = l_Lean_MessageData_ofFormat(v___x_44_);
v___x_46_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_42_);
lean_ctor_set(v___x_46_, 1, v___x_45_);
v___x_47_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_checkExp___closed__6, &l_Lean_Meta_Sym_Arith_checkExp___closed__6_once, _init_l_Lean_Meta_Sym_Arith_checkExp___closed__6);
v___x_48_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_46_);
lean_ctor_set(v___x_48_, 1, v___x_47_);
v___x_49_ = l_Lean_Meta_Sym_reportIssue(v___x_48_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_);
if (lean_obj_tag(v___x_49_) == 0)
{
lean_dec_ref(v___x_49_);
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
lean_dec(v_a_24_);
lean_dec(v_k_12_);
v_a_58_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_65_ == 0)
{
v___x_60_ = v___x_33_;
v_isShared_61_ = v_isSharedCheck_65_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_33_);
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
lean_object* v_i_165_; lean_object* v_a_166_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_172_; lean_object* v___x_224_; 
lean_inc_ref(v_e_156_);
v___x_224_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_156_, v_a_160_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_588_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_588_ == 0)
{
v___x_227_ = v___x_224_;
v_isShared_228_ = v_isSharedCheck_588_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_224_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_588_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_234_ = l_Lean_Expr_cleanupAnnotations(v_a_225_);
v___x_235_ = l_Lean_Expr_isApp(v___x_234_);
if (v___x_235_ == 0)
{
lean_dec_ref(v___x_234_);
lean_dec_ref(v_e_156_);
goto v___jp_229_;
}
else
{
lean_object* v_arg_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v_arg_236_ = lean_ctor_get(v___x_234_, 1);
lean_inc_ref(v_arg_236_);
v___x_237_ = l_Lean_Expr_appFnCleanup___redArg(v___x_234_);
v___x_238_ = l_Lean_Expr_isApp(v___x_237_);
if (v___x_238_ == 0)
{
lean_dec_ref(v___x_237_);
lean_dec_ref(v_arg_236_);
lean_dec_ref(v_e_156_);
goto v___jp_229_;
}
else
{
lean_object* v_arg_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v_arg_239_ = lean_ctor_get(v___x_237_, 1);
lean_inc_ref(v_arg_239_);
v___x_240_ = l_Lean_Expr_appFnCleanup___redArg(v___x_237_);
v___x_241_ = l_Lean_Expr_isApp(v___x_240_);
if (v___x_241_ == 0)
{
lean_dec_ref(v___x_240_);
lean_dec_ref(v_arg_239_);
lean_dec_ref(v_arg_236_);
lean_dec_ref(v_e_156_);
goto v___jp_229_;
}
else
{
lean_object* v_arg_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v_arg_242_ = lean_ctor_get(v___x_240_, 1);
lean_inc_ref(v_arg_242_);
v___x_243_ = l_Lean_Expr_appFnCleanup___redArg(v___x_240_);
v___x_244_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__3));
v___x_245_ = l_Lean_Expr_isConstOf(v___x_243_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_246_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__6));
v___x_247_ = l_Lean_Expr_isConstOf(v___x_243_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_248_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__12));
v___x_249_ = l_Lean_Expr_isConstOf(v___x_243_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; uint8_t v___x_251_; 
lean_dec_ref(v_e_156_);
v___x_250_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__9));
v___x_251_ = l_Lean_Expr_isConstOf(v___x_243_, v___x_250_);
if (v___x_251_ == 0)
{
uint8_t v___x_252_; 
v___x_252_ = l_Lean_Expr_isApp(v___x_243_);
if (v___x_252_ == 0)
{
lean_dec_ref(v___x_243_);
lean_dec_ref(v_arg_242_);
lean_dec_ref(v_arg_239_);
lean_dec_ref(v_arg_236_);
goto v___jp_229_;
}
else
{
lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_253_ = l_Lean_Expr_appFnCleanup___redArg(v___x_243_);
v___x_254_ = l_Lean_Expr_isApp(v___x_253_);
if (v___x_254_ == 0)
{
lean_dec_ref(v___x_253_);
lean_dec_ref(v_arg_242_);
lean_dec_ref(v_arg_239_);
lean_dec_ref(v_arg_236_);
goto v___jp_229_;
}
else
{
lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_255_ = l_Lean_Expr_appFnCleanup___redArg(v___x_253_);
v___x_256_ = l_Lean_Expr_isApp(v___x_255_);
if (v___x_256_ == 0)
{
lean_dec_ref(v___x_255_);
lean_dec_ref(v_arg_242_);
lean_dec_ref(v_arg_239_);
lean_dec_ref(v_arg_236_);
goto v___jp_229_;
}
else
{
lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_257_ = l_Lean_Expr_appFnCleanup___redArg(v___x_255_);
v___x_258_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__15));
v___x_259_ = l_Lean_Expr_isConstOf(v___x_257_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__18));
v___x_261_ = l_Lean_Expr_isConstOf(v___x_257_, v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_262_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__21));
v___x_263_ = l_Lean_Expr_isConstOf(v___x_257_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__27));
v___x_265_ = l_Lean_Expr_isConstOf(v___x_257_, v___x_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__24));
v___x_267_ = l_Lean_Expr_isConstOf(v___x_257_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__30));
v___x_269_ = l_Lean_Expr_isConstOf(v___x_257_, v___x_268_);
lean_dec_ref(v___x_257_);
if (v___x_269_ == 0)
{
lean_dec_ref(v_arg_242_);
lean_dec_ref(v_arg_239_);
lean_dec_ref(v_arg_236_);
goto v___jp_229_;
}
else
{
lean_object* v___x_270_; 
lean_del_object(v___x_227_);
v___x_270_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_242_, v_a_160_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_302_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_302_ == 0)
{
v___x_273_ = v___x_270_;
v_isShared_274_ = v_isSharedCheck_302_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_270_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_302_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
uint8_t v___x_275_; 
v___x_275_ = lean_unbox(v_a_271_);
lean_dec(v_a_271_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_278_; 
lean_dec_ref(v_arg_239_);
lean_dec_ref(v_arg_236_);
v___x_276_ = lean_box(0);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_276_);
v___x_278_ = v___x_273_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_276_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
else
{
lean_object* v___x_280_; 
lean_del_object(v___x_273_);
v___x_280_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_239_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_281_);
if (lean_obj_tag(v_a_281_) == 0)
{
lean_dec_ref(v_arg_236_);
return v___x_280_;
}
else
{
lean_object* v_val_282_; lean_object* v___x_283_; 
lean_dec_ref(v___x_280_);
v_val_282_ = lean_ctor_get(v_a_281_, 0);
lean_inc(v_val_282_);
lean_dec_ref(v_a_281_);
v___x_283_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_236_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_a_284_);
if (lean_obj_tag(v_a_284_) == 0)
{
lean_dec(v_val_282_);
return v___x_283_;
}
else
{
lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_300_; 
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; 
v_unused_301_ = lean_ctor_get(v___x_283_, 0);
lean_dec(v_unused_301_);
v___x_286_ = v___x_283_;
v_isShared_287_ = v_isSharedCheck_300_;
goto v_resetjp_285_;
}
else
{
lean_dec(v___x_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_300_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v_val_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_299_; 
v_val_288_ = lean_ctor_get(v_a_284_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v_a_284_);
if (v_isSharedCheck_299_ == 0)
{
v___x_290_ = v_a_284_;
v_isShared_291_ = v_isSharedCheck_299_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_val_288_);
lean_dec(v_a_284_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_299_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_292_ = lean_int_add(v_val_282_, v_val_288_);
lean_dec(v_val_288_);
lean_dec(v_val_282_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_292_);
v___x_294_ = v___x_290_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_298_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_296_; 
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_294_);
v___x_296_ = v___x_286_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
}
else
{
lean_dec(v_val_282_);
return v___x_283_;
}
}
}
else
{
lean_dec_ref(v_arg_236_);
return v___x_280_;
}
}
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
lean_dec_ref(v_arg_239_);
lean_dec_ref(v_arg_236_);
v_a_303_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_270_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_270_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
else
{
lean_object* v___x_311_; 
lean_dec_ref(v___x_257_);
lean_del_object(v___x_227_);
v___x_311_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_arg_242_, v_a_160_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_343_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_343_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_343_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_343_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
uint8_t v___x_316_; 
v___x_316_ = lean_unbox(v_a_312_);
lean_dec(v_a_312_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_319_; 
lean_dec_ref(v_arg_239_);
lean_dec_ref(v_arg_236_);
v___x_317_ = lean_box(0);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_317_);
v___x_319_ = v___x_314_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
else
{
lean_object* v___x_321_; 
lean_del_object(v___x_314_);
v___x_321_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_239_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
if (lean_obj_tag(v_a_322_) == 0)
{
lean_dec_ref(v_arg_236_);
return v___x_321_;
}
else
{
lean_object* v_val_323_; lean_object* v___x_324_; 
lean_dec_ref(v___x_321_);
v_val_323_ = lean_ctor_get(v_a_322_, 0);
lean_inc(v_val_323_);
lean_dec_ref(v_a_322_);
v___x_324_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_236_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
if (lean_obj_tag(v_a_325_) == 0)
{
lean_dec(v_val_323_);
return v___x_324_;
}
else
{
lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_341_; 
v_isSharedCheck_341_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_341_ == 0)
{
lean_object* v_unused_342_; 
v_unused_342_ = lean_ctor_get(v___x_324_, 0);
lean_dec(v_unused_342_);
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_341_;
goto v_resetjp_326_;
}
else
{
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_341_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v_val_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_340_; 
v_val_329_ = lean_ctor_get(v_a_325_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v_a_325_);
if (v_isSharedCheck_340_ == 0)
{
v___x_331_ = v_a_325_;
v_isShared_332_ = v_isSharedCheck_340_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_val_329_);
lean_dec(v_a_325_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_340_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_333_ = lean_int_sub(v_val_323_, v_val_329_);
lean_dec(v_val_329_);
lean_dec(v_val_323_);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_333_);
v___x_335_ = v___x_331_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_333_);
v___x_335_ = v_reuseFailAlloc_339_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_337_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_335_);
v___x_337_ = v___x_327_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_335_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
}
}
else
{
lean_dec(v_val_323_);
return v___x_324_;
}
}
}
else
{
lean_dec_ref(v_arg_236_);
return v___x_321_;
}
}
}
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec_ref(v_arg_239_);
lean_dec_ref(v_arg_236_);
v_a_344_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_311_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_311_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
else
{
lean_object* v___x_352_; 
lean_dec_ref(v___x_257_);
lean_del_object(v___x_227_);
v___x_352_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_242_, v_a_160_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_384_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_384_ == 0)
{
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_384_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_384_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
uint8_t v___x_357_; 
v___x_357_ = lean_unbox(v_a_353_);
lean_dec(v_a_353_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_360_; 
lean_dec_ref(v_arg_239_);
lean_dec_ref(v_arg_236_);
v___x_358_ = lean_box(0);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_358_);
v___x_360_ = v___x_355_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
else
{
lean_object* v___x_362_; 
lean_del_object(v___x_355_);
v___x_362_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_239_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
if (lean_obj_tag(v_a_363_) == 0)
{
lean_dec_ref(v_arg_236_);
return v___x_362_;
}
else
{
lean_object* v_val_364_; lean_object* v___x_365_; 
lean_dec_ref(v___x_362_);
v_val_364_ = lean_ctor_get(v_a_363_, 0);
lean_inc(v_val_364_);
lean_dec_ref(v_a_363_);
v___x_365_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_236_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_a_366_);
if (lean_obj_tag(v_a_366_) == 0)
{
lean_dec(v_val_364_);
return v___x_365_;
}
else
{
lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_382_; 
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_382_ == 0)
{
lean_object* v_unused_383_; 
v_unused_383_ = lean_ctor_get(v___x_365_, 0);
lean_dec(v_unused_383_);
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_382_;
goto v_resetjp_367_;
}
else
{
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_382_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v_val_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_381_; 
v_val_370_ = lean_ctor_get(v_a_366_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v_a_366_);
if (v_isSharedCheck_381_ == 0)
{
v___x_372_ = v_a_366_;
v_isShared_373_ = v_isSharedCheck_381_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_val_370_);
lean_dec(v_a_366_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_381_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = lean_int_mul(v_val_364_, v_val_370_);
lean_dec(v_val_370_);
lean_dec(v_val_364_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_374_);
v___x_376_ = v___x_372_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_380_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_378_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_376_);
v___x_378_ = v___x_368_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_376_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
}
else
{
lean_dec(v_val_364_);
return v___x_365_;
}
}
}
else
{
lean_dec_ref(v_arg_236_);
return v___x_362_;
}
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec_ref(v_arg_239_);
lean_dec_ref(v_arg_236_);
v_a_385_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_352_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_352_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
else
{
lean_object* v___x_393_; 
lean_dec_ref(v___x_257_);
lean_del_object(v___x_227_);
v___x_393_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_arg_242_, v_a_160_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_425_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_425_ == 0)
{
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_425_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_425_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
uint8_t v___x_398_; 
v___x_398_ = lean_unbox(v_a_394_);
lean_dec(v_a_394_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; lean_object* v___x_401_; 
lean_dec_ref(v_arg_239_);
lean_dec_ref(v_arg_236_);
v___x_399_ = lean_box(0);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_399_);
v___x_401_ = v___x_396_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
else
{
lean_object* v___x_403_; 
lean_del_object(v___x_396_);
v___x_403_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_239_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
if (lean_obj_tag(v_a_404_) == 0)
{
lean_dec_ref(v_arg_236_);
return v___x_403_;
}
else
{
lean_object* v_val_405_; lean_object* v___x_406_; 
lean_dec_ref(v___x_403_);
v_val_405_ = lean_ctor_get(v_a_404_, 0);
lean_inc(v_val_405_);
lean_dec_ref(v_a_404_);
v___x_406_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_236_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
if (lean_obj_tag(v_a_407_) == 0)
{
lean_dec(v_val_405_);
return v___x_406_;
}
else
{
lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_423_; 
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v___x_406_, 0);
lean_dec(v_unused_424_);
v___x_409_ = v___x_406_;
v_isShared_410_ = v_isSharedCheck_423_;
goto v_resetjp_408_;
}
else
{
lean_dec(v___x_406_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_423_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_val_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_422_; 
v_val_411_ = lean_ctor_get(v_a_407_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v_a_407_);
if (v_isSharedCheck_422_ == 0)
{
v___x_413_ = v_a_407_;
v_isShared_414_ = v_isSharedCheck_422_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_val_411_);
lean_dec(v_a_407_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_422_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_415_ = lean_int_ediv(v_val_405_, v_val_411_);
lean_dec(v_val_411_);
lean_dec(v_val_405_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_415_);
v___x_417_ = v___x_413_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_421_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_419_; 
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_417_);
v___x_419_ = v___x_409_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
}
else
{
lean_dec(v_val_405_);
return v___x_406_;
}
}
}
else
{
lean_dec_ref(v_arg_236_);
return v___x_403_;
}
}
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec_ref(v_arg_239_);
lean_dec_ref(v_arg_236_);
v_a_426_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_393_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_393_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
else
{
lean_object* v___x_434_; 
lean_dec_ref(v___x_257_);
lean_del_object(v___x_227_);
v___x_434_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_arg_242_, v_a_160_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_466_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_466_ == 0)
{
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_466_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_466_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
uint8_t v___x_439_; 
v___x_439_ = lean_unbox(v_a_435_);
lean_dec(v_a_435_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_442_; 
lean_dec_ref(v_arg_239_);
lean_dec_ref(v_arg_236_);
v___x_440_ = lean_box(0);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_440_);
v___x_442_ = v___x_437_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
else
{
lean_object* v___x_444_; 
lean_del_object(v___x_437_);
v___x_444_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_239_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
if (lean_obj_tag(v_a_445_) == 0)
{
lean_dec_ref(v_arg_236_);
return v___x_444_;
}
else
{
lean_object* v_val_446_; lean_object* v___x_447_; 
lean_dec_ref(v___x_444_);
v_val_446_ = lean_ctor_get(v_a_445_, 0);
lean_inc(v_val_446_);
lean_dec_ref(v_a_445_);
v___x_447_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_236_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
if (lean_obj_tag(v_a_448_) == 0)
{
lean_dec(v_val_446_);
return v___x_447_;
}
else
{
lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_464_; 
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v___x_447_, 0);
lean_dec(v_unused_465_);
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_464_;
goto v_resetjp_449_;
}
else
{
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_464_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v_val_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_463_; 
v_val_452_ = lean_ctor_get(v_a_448_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v_a_448_);
if (v_isSharedCheck_463_ == 0)
{
v___x_454_ = v_a_448_;
v_isShared_455_ = v_isSharedCheck_463_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_val_452_);
lean_dec(v_a_448_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_463_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_456_ = lean_int_emod(v_val_446_, v_val_452_);
lean_dec(v_val_452_);
lean_dec(v_val_446_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_456_);
v___x_458_ = v___x_454_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_456_);
v___x_458_ = v_reuseFailAlloc_462_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_460_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_458_);
v___x_460_ = v___x_450_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
}
else
{
lean_dec(v_val_446_);
return v___x_447_;
}
}
}
else
{
lean_dec_ref(v_arg_236_);
return v___x_444_;
}
}
}
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec_ref(v_arg_239_);
lean_dec_ref(v_arg_236_);
v_a_467_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_434_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_434_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
else
{
lean_object* v___x_475_; 
lean_dec_ref(v___x_257_);
lean_del_object(v___x_227_);
v___x_475_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_arg_242_, v_a_160_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_537_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_537_ == 0)
{
v___x_478_ = v___x_475_;
v_isShared_479_ = v_isSharedCheck_537_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_475_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_537_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
uint8_t v___x_480_; 
v___x_480_ = lean_unbox(v_a_476_);
lean_dec(v_a_476_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_483_; 
lean_dec_ref(v_arg_239_);
lean_dec_ref(v_arg_236_);
v___x_481_ = lean_box(0);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_481_);
v___x_483_ = v___x_478_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
else
{
lean_object* v___x_485_; 
lean_del_object(v___x_478_);
v___x_485_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_239_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_485_) == 0)
{
lean_object* v_a_486_; 
v_a_486_ = lean_ctor_get(v___x_485_, 0);
lean_inc(v_a_486_);
if (lean_obj_tag(v_a_486_) == 0)
{
lean_dec_ref(v_arg_236_);
return v___x_485_;
}
else
{
lean_object* v_val_487_; lean_object* v___x_488_; 
lean_dec_ref(v___x_485_);
v_val_487_ = lean_ctor_get(v_a_486_, 0);
lean_inc(v_val_487_);
lean_dec_ref(v_a_486_);
v___x_488_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_236_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_528_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_528_ == 0)
{
v___x_491_ = v___x_488_;
v_isShared_492_ = v_isSharedCheck_528_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_528_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
if (lean_obj_tag(v_a_489_) == 0)
{
lean_object* v___x_493_; lean_object* v___x_495_; 
lean_dec(v_val_487_);
v___x_493_ = lean_box(0);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_493_);
v___x_495_ = v___x_491_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
else
{
lean_object* v_val_497_; lean_object* v___x_498_; 
lean_del_object(v___x_491_);
v_val_497_ = lean_ctor_get(v_a_489_, 0);
lean_inc_n(v_val_497_, 2);
lean_dec_ref(v_a_489_);
v___x_498_ = l_Lean_Meta_Sym_Arith_checkExp(v_val_497_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_519_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_519_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_519_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_519_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
if (lean_obj_tag(v_a_499_) == 0)
{
lean_object* v___x_503_; lean_object* v___x_505_; 
lean_dec(v_val_497_);
lean_dec(v_val_487_);
v___x_503_ = lean_box(0);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_503_);
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
else
{
lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_517_; 
v_isSharedCheck_517_ = !lean_is_exclusive(v_a_499_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v_a_499_, 0);
lean_dec(v_unused_518_);
v___x_508_ = v_a_499_;
v_isShared_509_ = v_isSharedCheck_517_;
goto v_resetjp_507_;
}
else
{
lean_dec(v_a_499_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_517_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_512_; 
v___x_510_ = l_Int_pow(v_val_487_, v_val_497_);
lean_dec(v_val_497_);
lean_dec(v_val_487_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_510_);
v___x_512_ = v___x_508_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_510_);
v___x_512_ = v_reuseFailAlloc_516_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_514_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_512_);
v___x_514_ = v___x_501_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec(v_val_497_);
lean_dec(v_val_487_);
v_a_520_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_498_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_498_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec(v_val_487_);
v_a_529_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_488_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_488_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_236_);
return v___x_485_;
}
}
}
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec_ref(v_arg_239_);
lean_dec_ref(v_arg_236_);
v_a_538_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_475_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_475_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
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
lean_object* v___x_546_; 
lean_dec_ref(v___x_243_);
lean_dec_ref(v_arg_242_);
lean_del_object(v___x_227_);
v___x_546_ = l_Lean_Meta_Structural_isInstNegInt___redArg(v_arg_239_, v_a_160_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_575_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_575_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_575_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_575_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
uint8_t v___x_551_; 
v___x_551_ = lean_unbox(v_a_547_);
lean_dec(v_a_547_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; lean_object* v___x_554_; 
lean_dec_ref(v_arg_236_);
v___x_552_ = lean_box(0);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_552_);
v___x_554_ = v___x_549_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
else
{
lean_object* v___x_556_; 
lean_del_object(v___x_549_);
v___x_556_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_236_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
lean_inc(v_a_557_);
if (lean_obj_tag(v_a_557_) == 0)
{
return v___x_556_;
}
else
{
lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_573_; 
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v___x_556_, 0);
lean_dec(v_unused_574_);
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_573_;
goto v_resetjp_558_;
}
else
{
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_573_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v_val_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_572_; 
v_val_561_ = lean_ctor_get(v_a_557_, 0);
v_isSharedCheck_572_ = !lean_is_exclusive(v_a_557_);
if (v_isSharedCheck_572_ == 0)
{
v___x_563_ = v_a_557_;
v_isShared_564_ = v_isSharedCheck_572_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_val_561_);
lean_dec(v_a_557_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_572_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_565_; lean_object* v___x_567_; 
v___x_565_ = lean_int_neg(v_val_561_);
lean_dec(v_val_561_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_565_);
v___x_567_ = v___x_563_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_565_);
v___x_567_ = v_reuseFailAlloc_571_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_569_; 
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_567_);
v___x_569_ = v___x_559_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_567_);
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
return v___x_556_;
}
}
}
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec_ref(v_arg_236_);
v_a_576_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_546_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_546_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
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
else
{
lean_object* v___x_584_; 
lean_dec_ref(v___x_243_);
lean_dec_ref(v_arg_242_);
lean_dec_ref(v_arg_239_);
lean_dec_ref(v_arg_236_);
lean_del_object(v___x_227_);
v___x_584_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_156_);
if (lean_obj_tag(v___x_584_) == 1)
{
lean_object* v___x_585_; 
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v___x_584_);
v___x_586_ = lean_box(0);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
}
}
else
{
lean_dec_ref(v___x_243_);
lean_dec_ref(v_arg_242_);
lean_del_object(v___x_227_);
lean_dec_ref(v_e_156_);
v_i_165_ = v_arg_239_;
v_a_166_ = v_arg_236_;
v___y_167_ = v_a_157_;
v___y_168_ = v_a_158_;
v___y_169_ = v_a_159_;
v___y_170_ = v_a_160_;
v___y_171_ = v_a_161_;
v___y_172_ = v_a_162_;
goto v___jp_164_;
}
}
else
{
lean_dec_ref(v___x_243_);
lean_dec_ref(v_arg_242_);
lean_del_object(v___x_227_);
lean_dec_ref(v_e_156_);
v_i_165_ = v_arg_239_;
v_a_166_ = v_arg_236_;
v___y_167_ = v_a_157_;
v___y_168_ = v_a_158_;
v___y_169_ = v_a_159_;
v___y_170_ = v_a_160_;
v___y_171_ = v_a_161_;
v___y_172_ = v_a_162_;
goto v___jp_164_;
}
}
}
}
v___jp_229_:
{
lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_230_ = lean_box(0);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_230_);
v___x_232_ = v___x_227_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec_ref(v_e_156_);
v_a_589_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_224_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_224_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
v___jp_164_:
{
lean_object* v___x_173_; 
v___x_173_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_i_165_, v___y_170_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_215_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_215_ == 0)
{
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_215_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_215_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_178_ = l_Lean_Expr_cleanupAnnotations(v_a_174_);
v___x_179_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__1));
v___x_180_ = l_Lean_Expr_isConstOf(v___x_178_, v___x_179_);
lean_dec_ref(v___x_178_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_183_; 
lean_dec_ref(v_a_166_);
v___x_181_ = lean_box(0);
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___x_181_);
v___x_183_ = v___x_176_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
else
{
lean_object* v___x_185_; 
lean_del_object(v___x_176_);
v___x_185_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_a_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_206_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_206_ == 0)
{
v___x_188_ = v___x_185_;
v_isShared_189_ = v_isSharedCheck_206_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_185_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_206_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
if (lean_obj_tag(v_a_186_) == 0)
{
lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_190_ = lean_box(0);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_190_);
v___x_192_ = v___x_188_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
else
{
lean_object* v_val_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_205_; 
v_val_194_ = lean_ctor_get(v_a_186_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v_a_186_);
if (v_isSharedCheck_205_ == 0)
{
v___x_196_ = v_a_186_;
v_isShared_197_ = v_isSharedCheck_205_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_val_194_);
lean_dec(v_a_186_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_205_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_198_ = lean_nat_to_int(v_val_194_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_198_);
v___x_200_ = v___x_196_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_204_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_202_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v___x_200_);
v___x_202_ = v___x_188_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
v_a_207_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_185_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_185_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
}
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_dec_ref(v_a_166_);
v_a_216_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_173_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_173_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(lean_object* v_e_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
lean_object* v___x_608_; 
lean_inc_ref(v_e_597_);
v___x_608_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_597_, v_a_601_);
if (lean_obj_tag(v___x_608_) == 0)
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_1007_; 
v_a_609_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_1007_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_1007_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_613_ = l_Lean_Expr_cleanupAnnotations(v_a_609_);
v___x_614_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__2));
v___x_615_ = l_Lean_Expr_isConstOf(v___x_613_, v___x_614_);
if (v___x_615_ == 0)
{
uint8_t v___x_616_; 
v___x_616_ = l_Lean_Expr_isApp(v___x_613_);
if (v___x_616_ == 0)
{
lean_dec_ref(v___x_613_);
lean_del_object(v___x_611_);
lean_dec_ref(v_e_597_);
goto v___jp_605_;
}
else
{
lean_object* v_arg_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_arg_617_ = lean_ctor_get(v___x_613_, 1);
lean_inc_ref(v_arg_617_);
v___x_618_ = l_Lean_Expr_appFnCleanup___redArg(v___x_613_);
v___x_619_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__5));
v___x_620_ = l_Lean_Expr_isConstOf(v___x_618_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__7));
v___x_622_ = l_Lean_Expr_isConstOf(v___x_618_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_623_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__9));
v___x_624_ = l_Lean_Expr_isConstOf(v___x_618_, v___x_623_);
if (v___x_624_ == 0)
{
uint8_t v___x_625_; 
v___x_625_ = l_Lean_Expr_isApp(v___x_618_);
if (v___x_625_ == 0)
{
lean_dec_ref(v___x_618_);
lean_dec_ref(v_arg_617_);
lean_del_object(v___x_611_);
lean_dec_ref(v_e_597_);
goto v___jp_605_;
}
else
{
lean_object* v_arg_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v_arg_626_ = lean_ctor_get(v___x_618_, 1);
lean_inc_ref(v_arg_626_);
v___x_627_ = l_Lean_Expr_appFnCleanup___redArg(v___x_618_);
v___x_628_ = l_Lean_Expr_isApp(v___x_627_);
if (v___x_628_ == 0)
{
lean_dec_ref(v___x_627_);
lean_dec_ref(v_arg_626_);
lean_dec_ref(v_arg_617_);
lean_del_object(v___x_611_);
lean_dec_ref(v_e_597_);
goto v___jp_605_;
}
else
{
lean_object* v_arg_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v_arg_629_ = lean_ctor_get(v___x_627_, 1);
lean_inc_ref(v_arg_629_);
v___x_630_ = l_Lean_Expr_appFnCleanup___redArg(v___x_627_);
v___x_631_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__12));
v___x_632_ = l_Lean_Expr_isConstOf(v___x_630_, v___x_631_);
if (v___x_632_ == 0)
{
uint8_t v___x_633_; 
lean_del_object(v___x_611_);
lean_dec_ref(v_e_597_);
v___x_633_ = l_Lean_Expr_isApp(v___x_630_);
if (v___x_633_ == 0)
{
lean_dec_ref(v___x_630_);
lean_dec_ref(v_arg_629_);
lean_dec_ref(v_arg_626_);
lean_dec_ref(v_arg_617_);
goto v___jp_605_;
}
else
{
lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_634_ = l_Lean_Expr_appFnCleanup___redArg(v___x_630_);
v___x_635_ = l_Lean_Expr_isApp(v___x_634_);
if (v___x_635_ == 0)
{
lean_dec_ref(v___x_634_);
lean_dec_ref(v_arg_629_);
lean_dec_ref(v_arg_626_);
lean_dec_ref(v_arg_617_);
goto v___jp_605_;
}
else
{
lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_636_ = l_Lean_Expr_appFnCleanup___redArg(v___x_634_);
v___x_637_ = l_Lean_Expr_isApp(v___x_636_);
if (v___x_637_ == 0)
{
lean_dec_ref(v___x_636_);
lean_dec_ref(v_arg_629_);
lean_dec_ref(v_arg_626_);
lean_dec_ref(v_arg_617_);
goto v___jp_605_;
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_638_ = l_Lean_Expr_appFnCleanup___redArg(v___x_636_);
v___x_639_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__15));
v___x_640_ = l_Lean_Expr_isConstOf(v___x_638_, v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__18));
v___x_642_ = l_Lean_Expr_isConstOf(v___x_638_, v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_643_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__21));
v___x_644_ = l_Lean_Expr_isConstOf(v___x_638_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__24));
v___x_646_ = l_Lean_Expr_isConstOf(v___x_638_, v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__27));
v___x_648_ = l_Lean_Expr_isConstOf(v___x_638_, v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__30));
v___x_650_ = l_Lean_Expr_isConstOf(v___x_638_, v___x_649_);
lean_dec_ref(v___x_638_);
if (v___x_650_ == 0)
{
lean_dec_ref(v_arg_629_);
lean_dec_ref(v_arg_626_);
lean_dec_ref(v_arg_617_);
goto v___jp_605_;
}
else
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_629_, v_a_601_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_683_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_683_ == 0)
{
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_683_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_683_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
uint8_t v___x_656_; 
v___x_656_ = lean_unbox(v_a_652_);
lean_dec(v_a_652_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_659_; 
lean_dec_ref(v_arg_626_);
lean_dec_ref(v_arg_617_);
v___x_657_ = lean_box(0);
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 0, v___x_657_);
v___x_659_ = v___x_654_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
else
{
lean_object* v___x_661_; 
lean_del_object(v___x_654_);
v___x_661_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_626_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
if (lean_obj_tag(v_a_662_) == 0)
{
lean_dec_ref(v_arg_617_);
return v___x_661_;
}
else
{
lean_object* v_val_663_; lean_object* v___x_664_; 
lean_dec_ref(v___x_661_);
v_val_663_ = lean_ctor_get(v_a_662_, 0);
lean_inc(v_val_663_);
lean_dec_ref(v_a_662_);
v___x_664_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_617_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
if (lean_obj_tag(v_a_665_) == 0)
{
lean_dec(v_val_663_);
return v___x_664_;
}
else
{
lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_681_; 
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; 
v_unused_682_ = lean_ctor_get(v___x_664_, 0);
lean_dec(v_unused_682_);
v___x_667_ = v___x_664_;
v_isShared_668_ = v_isSharedCheck_681_;
goto v_resetjp_666_;
}
else
{
lean_dec(v___x_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_681_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v_val_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_680_; 
v_val_669_ = lean_ctor_get(v_a_665_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v_a_665_);
if (v_isSharedCheck_680_ == 0)
{
v___x_671_ = v_a_665_;
v_isShared_672_ = v_isSharedCheck_680_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_val_669_);
lean_dec(v_a_665_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_680_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = lean_nat_add(v_val_663_, v_val_669_);
lean_dec(v_val_669_);
lean_dec(v_val_663_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_673_);
v___x_675_ = v___x_671_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_673_);
v___x_675_ = v_reuseFailAlloc_679_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_677_; 
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_675_);
v___x_677_ = v___x_667_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
}
else
{
lean_dec(v_val_663_);
return v___x_664_;
}
}
}
else
{
lean_dec_ref(v_arg_617_);
return v___x_661_;
}
}
}
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_dec_ref(v_arg_626_);
lean_dec_ref(v_arg_617_);
v_a_684_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_651_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_651_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
}
else
{
lean_object* v___x_692_; 
lean_dec_ref(v___x_638_);
v___x_692_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_arg_629_, v_a_601_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_724_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_724_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_724_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_724_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
uint8_t v___x_697_; 
v___x_697_ = lean_unbox(v_a_693_);
lean_dec(v_a_693_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_700_; 
lean_dec_ref(v_arg_626_);
lean_dec_ref(v_arg_617_);
v___x_698_ = lean_box(0);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_698_);
v___x_700_ = v___x_695_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
else
{
lean_object* v___x_702_; 
lean_del_object(v___x_695_);
v___x_702_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_626_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
if (lean_obj_tag(v_a_703_) == 0)
{
lean_dec_ref(v_arg_617_);
return v___x_702_;
}
else
{
lean_object* v_val_704_; lean_object* v___x_705_; 
lean_dec_ref(v___x_702_);
v_val_704_ = lean_ctor_get(v_a_703_, 0);
lean_inc(v_val_704_);
lean_dec_ref(v_a_703_);
v___x_705_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_617_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
if (lean_obj_tag(v_a_706_) == 0)
{
lean_dec(v_val_704_);
return v___x_705_;
}
else
{
lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_722_; 
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; 
v_unused_723_ = lean_ctor_get(v___x_705_, 0);
lean_dec(v_unused_723_);
v___x_708_ = v___x_705_;
v_isShared_709_ = v_isSharedCheck_722_;
goto v_resetjp_707_;
}
else
{
lean_dec(v___x_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_722_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v_val_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_721_; 
v_val_710_ = lean_ctor_get(v_a_706_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v_a_706_);
if (v_isSharedCheck_721_ == 0)
{
v___x_712_ = v_a_706_;
v_isShared_713_ = v_isSharedCheck_721_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_val_710_);
lean_dec(v_a_706_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_721_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_714_ = lean_nat_mul(v_val_704_, v_val_710_);
lean_dec(v_val_710_);
lean_dec(v_val_704_);
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_714_);
v___x_716_ = v___x_712_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_714_);
v___x_716_ = v_reuseFailAlloc_720_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v___x_716_);
v___x_718_ = v___x_708_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
}
else
{
lean_dec(v_val_704_);
return v___x_705_;
}
}
}
else
{
lean_dec_ref(v_arg_617_);
return v___x_702_;
}
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec_ref(v_arg_626_);
lean_dec_ref(v_arg_617_);
v_a_725_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_692_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_692_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
else
{
lean_object* v___x_733_; 
lean_dec_ref(v___x_638_);
v___x_733_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_arg_629_, v_a_601_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_765_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_765_ == 0)
{
v___x_736_ = v___x_733_;
v_isShared_737_ = v_isSharedCheck_765_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_765_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
uint8_t v___x_738_; 
v___x_738_ = lean_unbox(v_a_734_);
lean_dec(v_a_734_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_741_; 
lean_dec_ref(v_arg_626_);
lean_dec_ref(v_arg_617_);
v___x_739_ = lean_box(0);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_739_);
v___x_741_ = v___x_736_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
else
{
lean_object* v___x_743_; 
lean_del_object(v___x_736_);
v___x_743_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_626_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
if (lean_obj_tag(v_a_744_) == 0)
{
lean_dec_ref(v_arg_617_);
return v___x_743_;
}
else
{
lean_object* v_val_745_; lean_object* v___x_746_; 
lean_dec_ref(v___x_743_);
v_val_745_ = lean_ctor_get(v_a_744_, 0);
lean_inc(v_val_745_);
lean_dec_ref(v_a_744_);
v___x_746_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_617_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
if (lean_obj_tag(v_a_747_) == 0)
{
lean_dec(v_val_745_);
return v___x_746_;
}
else
{
lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_763_; 
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; 
v_unused_764_ = lean_ctor_get(v___x_746_, 0);
lean_dec(v_unused_764_);
v___x_749_ = v___x_746_;
v_isShared_750_ = v_isSharedCheck_763_;
goto v_resetjp_748_;
}
else
{
lean_dec(v___x_746_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_763_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v_val_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_762_; 
v_val_751_ = lean_ctor_get(v_a_747_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v_a_747_);
if (v_isSharedCheck_762_ == 0)
{
v___x_753_ = v_a_747_;
v_isShared_754_ = v_isSharedCheck_762_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_val_751_);
lean_dec(v_a_747_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_762_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_755_ = lean_nat_sub(v_val_745_, v_val_751_);
lean_dec(v_val_751_);
lean_dec(v_val_745_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_755_);
v___x_757_ = v___x_753_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_761_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_759_; 
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_757_);
v___x_759_ = v___x_749_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
}
else
{
lean_dec(v_val_745_);
return v___x_746_;
}
}
}
else
{
lean_dec_ref(v_arg_617_);
return v___x_743_;
}
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec_ref(v_arg_626_);
lean_dec_ref(v_arg_617_);
v_a_766_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_733_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_733_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
else
{
lean_object* v___x_774_; 
lean_dec_ref(v___x_638_);
v___x_774_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_arg_629_, v_a_601_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_806_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_806_ == 0)
{
v___x_777_ = v___x_774_;
v_isShared_778_ = v_isSharedCheck_806_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_806_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
uint8_t v___x_779_; 
v___x_779_ = lean_unbox(v_a_775_);
lean_dec(v_a_775_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_782_; 
lean_dec_ref(v_arg_626_);
lean_dec_ref(v_arg_617_);
v___x_780_ = lean_box(0);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_780_);
v___x_782_ = v___x_777_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
else
{
lean_object* v___x_784_; 
lean_del_object(v___x_777_);
v___x_784_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_626_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
if (lean_obj_tag(v_a_785_) == 0)
{
lean_dec_ref(v_arg_617_);
return v___x_784_;
}
else
{
lean_object* v_val_786_; lean_object* v___x_787_; 
lean_dec_ref(v___x_784_);
v_val_786_ = lean_ctor_get(v_a_785_, 0);
lean_inc(v_val_786_);
lean_dec_ref(v_a_785_);
v___x_787_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_617_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
if (lean_obj_tag(v_a_788_) == 0)
{
lean_dec(v_val_786_);
return v___x_787_;
}
else
{
lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_804_; 
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_804_ == 0)
{
lean_object* v_unused_805_; 
v_unused_805_ = lean_ctor_get(v___x_787_, 0);
lean_dec(v_unused_805_);
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_804_;
goto v_resetjp_789_;
}
else
{
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_804_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v_val_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_803_; 
v_val_792_ = lean_ctor_get(v_a_788_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v_a_788_);
if (v_isSharedCheck_803_ == 0)
{
v___x_794_ = v_a_788_;
v_isShared_795_ = v_isSharedCheck_803_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_val_792_);
lean_dec(v_a_788_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_803_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v___x_798_; 
v___x_796_ = lean_nat_div(v_val_786_, v_val_792_);
lean_dec(v_val_792_);
lean_dec(v_val_786_);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_796_);
v___x_798_ = v___x_794_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_796_);
v___x_798_ = v_reuseFailAlloc_802_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
lean_object* v___x_800_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_798_);
v___x_800_ = v___x_790_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
}
else
{
lean_dec(v_val_786_);
return v___x_787_;
}
}
}
else
{
lean_dec_ref(v_arg_617_);
return v___x_784_;
}
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec_ref(v_arg_626_);
lean_dec_ref(v_arg_617_);
v_a_807_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_774_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_774_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
else
{
lean_object* v___x_815_; 
lean_dec_ref(v___x_638_);
v___x_815_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_arg_629_, v_a_601_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_847_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_847_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_847_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_847_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
uint8_t v___x_820_; 
v___x_820_ = lean_unbox(v_a_816_);
lean_dec(v_a_816_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_823_; 
lean_dec_ref(v_arg_626_);
lean_dec_ref(v_arg_617_);
v___x_821_ = lean_box(0);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_821_);
v___x_823_ = v___x_818_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
else
{
lean_object* v___x_825_; 
lean_del_object(v___x_818_);
v___x_825_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_626_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
if (lean_obj_tag(v_a_826_) == 0)
{
lean_dec_ref(v_arg_617_);
return v___x_825_;
}
else
{
lean_object* v_val_827_; lean_object* v___x_828_; 
lean_dec_ref(v___x_825_);
v_val_827_ = lean_ctor_get(v_a_826_, 0);
lean_inc(v_val_827_);
lean_dec_ref(v_a_826_);
v___x_828_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_617_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_a_829_);
if (lean_obj_tag(v_a_829_) == 0)
{
lean_dec(v_val_827_);
return v___x_828_;
}
else
{
lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_845_; 
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_845_ == 0)
{
lean_object* v_unused_846_; 
v_unused_846_ = lean_ctor_get(v___x_828_, 0);
lean_dec(v_unused_846_);
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_845_;
goto v_resetjp_830_;
}
else
{
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_845_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v_val_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_844_; 
v_val_833_ = lean_ctor_get(v_a_829_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v_a_829_);
if (v_isSharedCheck_844_ == 0)
{
v___x_835_ = v_a_829_;
v_isShared_836_ = v_isSharedCheck_844_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_val_833_);
lean_dec(v_a_829_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_844_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_837_ = lean_nat_mod(v_val_827_, v_val_833_);
lean_dec(v_val_833_);
lean_dec(v_val_827_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v___x_837_);
v___x_839_ = v___x_835_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_843_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_841_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_839_);
v___x_841_ = v___x_831_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
}
else
{
lean_dec(v_val_827_);
return v___x_828_;
}
}
}
else
{
lean_dec_ref(v_arg_617_);
return v___x_825_;
}
}
}
}
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec_ref(v_arg_626_);
lean_dec_ref(v_arg_617_);
v_a_848_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_815_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_815_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_853_; 
if (v_isShared_851_ == 0)
{
v___x_853_ = v___x_850_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_a_848_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
}
else
{
lean_object* v___x_856_; 
lean_dec_ref(v___x_638_);
v___x_856_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_arg_629_, v_a_601_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_906_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_906_ == 0)
{
v___x_859_ = v___x_856_;
v_isShared_860_ = v_isSharedCheck_906_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_906_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
uint8_t v___x_861_; 
v___x_861_ = lean_unbox(v_a_857_);
lean_dec(v_a_857_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_864_; 
lean_dec_ref(v_arg_626_);
lean_dec_ref(v_arg_617_);
v___x_862_ = lean_box(0);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_862_);
v___x_864_ = v___x_859_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
else
{
lean_object* v___x_866_; 
lean_del_object(v___x_859_);
v___x_866_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_617_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
if (lean_obj_tag(v_a_867_) == 0)
{
lean_dec_ref(v_arg_626_);
return v___x_866_;
}
else
{
lean_object* v_val_868_; lean_object* v___x_869_; 
lean_dec_ref(v___x_866_);
v_val_868_ = lean_ctor_get(v_a_867_, 0);
lean_inc_n(v_val_868_, 2);
lean_dec_ref(v_a_867_);
v___x_869_ = l_Lean_Meta_Sym_Arith_checkExp(v_val_868_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_897_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_897_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_897_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_897_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
if (lean_obj_tag(v_a_870_) == 0)
{
lean_object* v___x_874_; lean_object* v___x_876_; 
lean_dec(v_val_868_);
lean_dec_ref(v_arg_626_);
v___x_874_ = lean_box(0);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_874_);
v___x_876_ = v___x_872_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
else
{
lean_object* v___x_878_; 
lean_dec_ref(v_a_870_);
lean_del_object(v___x_872_);
v___x_878_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_626_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
if (lean_obj_tag(v_a_879_) == 0)
{
lean_dec(v_val_868_);
return v___x_878_;
}
else
{
lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_895_; 
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; 
v_unused_896_ = lean_ctor_get(v___x_878_, 0);
lean_dec(v_unused_896_);
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_895_;
goto v_resetjp_880_;
}
else
{
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_895_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v_val_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_894_; 
v_val_883_ = lean_ctor_get(v_a_879_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v_a_879_);
if (v_isSharedCheck_894_ == 0)
{
v___x_885_ = v_a_879_;
v_isShared_886_ = v_isSharedCheck_894_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_val_883_);
lean_dec(v_a_879_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_894_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_887_ = lean_nat_pow(v_val_883_, v_val_868_);
lean_dec(v_val_868_);
lean_dec(v_val_883_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_887_);
v___x_889_ = v___x_885_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_893_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_891_; 
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_889_);
v___x_891_ = v___x_881_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_889_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
}
else
{
lean_dec(v_val_868_);
return v___x_878_;
}
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_dec(v_val_868_);
lean_dec_ref(v_arg_626_);
v_a_898_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_869_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_869_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_626_);
return v___x_866_;
}
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec_ref(v_arg_626_);
lean_dec_ref(v_arg_617_);
v_a_907_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_856_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_856_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
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
lean_object* v___x_915_; 
lean_dec_ref(v___x_630_);
lean_dec_ref(v_arg_629_);
lean_dec_ref(v_arg_626_);
lean_dec_ref(v_arg_617_);
v___x_915_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_597_);
if (lean_obj_tag(v___x_915_) == 1)
{
lean_object* v___x_917_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_915_);
v___x_917_ = v___x_611_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_915_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
else
{
lean_object* v___x_919_; lean_object* v___x_921_; 
lean_dec(v___x_915_);
v___x_919_ = lean_box(0);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_919_);
v___x_921_ = v___x_611_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
}
else
{
lean_object* v___x_923_; 
lean_dec_ref(v___x_618_);
lean_del_object(v___x_611_);
lean_dec_ref(v_e_597_);
v___x_923_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_617_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
if (lean_obj_tag(v_a_924_) == 0)
{
return v___x_923_;
}
else
{
lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_941_; 
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; 
v_unused_942_ = lean_ctor_get(v___x_923_, 0);
lean_dec(v_unused_942_);
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_941_;
goto v_resetjp_925_;
}
else
{
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_941_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_val_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_940_; 
v_val_928_ = lean_ctor_get(v_a_924_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v_a_924_);
if (v_isSharedCheck_940_ == 0)
{
v___x_930_ = v_a_924_;
v_isShared_931_ = v_isSharedCheck_940_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_val_928_);
lean_dec(v_a_924_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_940_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_932_ = lean_unsigned_to_nat(1u);
v___x_933_ = lean_nat_add(v_val_928_, v___x_932_);
lean_dec(v_val_928_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_933_);
v___x_935_ = v___x_930_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_939_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_937_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_935_);
v___x_937_ = v___x_926_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
}
else
{
return v___x_923_;
}
}
}
else
{
lean_object* v___x_943_; 
lean_dec_ref(v___x_618_);
lean_del_object(v___x_611_);
lean_dec_ref(v_e_597_);
v___x_943_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_617_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_964_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_964_ == 0)
{
v___x_946_ = v___x_943_;
v_isShared_947_ = v_isSharedCheck_964_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_964_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
if (lean_obj_tag(v_a_944_) == 0)
{
lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_948_ = lean_box(0);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_948_);
v___x_950_ = v___x_946_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
else
{
lean_object* v_val_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_963_; 
v_val_952_ = lean_ctor_get(v_a_944_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v_a_944_);
if (v_isSharedCheck_963_ == 0)
{
v___x_954_ = v_a_944_;
v_isShared_955_ = v_isSharedCheck_963_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_val_952_);
lean_dec(v_a_944_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_963_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_956_ = l_Int_toNat(v_val_952_);
lean_dec(v_val_952_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_956_);
v___x_958_ = v___x_954_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_956_);
v___x_958_ = v_reuseFailAlloc_962_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
lean_object* v___x_960_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v___x_958_);
v___x_960_ = v___x_946_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v___x_958_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
v_a_965_ = lean_ctor_get(v___x_943_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_943_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_943_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_943_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
else
{
lean_object* v___x_973_; 
lean_dec_ref(v___x_618_);
lean_del_object(v___x_611_);
lean_dec_ref(v_e_597_);
v___x_973_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_617_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_994_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_994_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_994_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_994_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
if (lean_obj_tag(v_a_974_) == 0)
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = lean_box(0);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_978_);
v___x_980_ = v___x_976_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
else
{
lean_object* v_val_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_993_; 
v_val_982_ = lean_ctor_get(v_a_974_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v_a_974_);
if (v_isSharedCheck_993_ == 0)
{
v___x_984_ = v_a_974_;
v_isShared_985_ = v_isSharedCheck_993_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_val_982_);
lean_dec(v_a_974_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_993_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_986_ = lean_nat_abs(v_val_982_);
lean_dec(v_val_982_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 0, v___x_986_);
v___x_988_ = v___x_984_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_986_);
v___x_988_ = v_reuseFailAlloc_992_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_990_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_988_);
v___x_990_ = v___x_976_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
v_a_995_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_973_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_973_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
lean_dec_ref(v___x_613_);
lean_dec_ref(v_e_597_);
v___x_1003_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__31));
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v___x_1003_);
v___x_1005_ = v___x_611_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec_ref(v_e_597_);
v_a_1008_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_608_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_608_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
v___jp_605_:
{
lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_606_ = lean_box(0);
v___x_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___boxed(lean_object* v_e_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_e_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___boxed(lean_object* v_e_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_e_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore_spec__1(lean_object* v_a_1034_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = lean_nat_to_int(v_a_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_evalNat_x3f(lean_object* v_e_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_e_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_evalNat_x3f___boxed(lean_object* v_e_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_Meta_Sym_Arith_evalNat_x3f(v_e_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_a_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_evalInt_x3f(lean_object* v_e_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_e_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_evalInt_x3f___boxed(lean_object* v_e_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_Meta_Sym_Arith_evalInt_x3f(v_e_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
return v_res_1071_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_EvalNum(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

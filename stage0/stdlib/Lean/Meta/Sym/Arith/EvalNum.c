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
lean_object* l_Lean_Meta_Sym_Arith_checkExp(lean_object* v_k_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_){
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
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_checkExp_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_12_ = stack[0].m_obj;
lean_object* v_a_13_ = stack[1].m_obj;
lean_object* v_a_14_ = stack[2].m_obj;
lean_object* v_a_15_ = stack[3].m_obj;
lean_object* v_a_16_ = stack[4].m_obj;
lean_object* v_a_17_ = stack[5].m_obj;
lean_object* v_a_18_ = stack[6].m_obj;
lean_object* v_res_75_;
v_res_75_ = l_Lean_Meta_Sym_Arith_checkExp(v_k_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_, v_a_18_);
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_checkExp___boxed(lean_object* v_k_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Meta_Sym_Arith_checkExp(v_k_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
lean_dec_ref(v_a_79_);
lean_dec(v_a_78_);
lean_dec_ref(v_a_77_);
return v_res_84_;
}
}
lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(lean_object* v_e_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_i_169_; lean_object* v_a_170_; lean_object* v___y_171_; lean_object* v___y_172_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v___x_228_; 
lean_inc_ref(v_e_157_);
v___x_228_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_157_, v_a_161_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_591_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_591_ == 0)
{
v___x_231_ = v___x_228_;
v_isShared_232_ = v_isSharedCheck_591_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_591_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_233_ = l_Lean_Expr_cleanupAnnotations(v_a_229_);
v___x_234_ = l_Lean_Expr_isApp(v___x_233_);
if (v___x_234_ == 0)
{
lean_dec_ref(v___x_233_);
lean_del_object(v___x_231_);
lean_dec_ref(v_e_157_);
goto v___jp_165_;
}
else
{
lean_object* v_arg_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v_arg_235_ = lean_ctor_get(v___x_233_, 1);
lean_inc_ref(v_arg_235_);
v___x_236_ = l_Lean_Expr_appFnCleanup___redArg(v___x_233_);
v___x_237_ = l_Lean_Expr_isApp(v___x_236_);
if (v___x_237_ == 0)
{
lean_dec_ref(v___x_236_);
lean_dec_ref(v_arg_235_);
lean_del_object(v___x_231_);
lean_dec_ref(v_e_157_);
goto v___jp_165_;
}
else
{
lean_object* v_arg_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v_arg_238_ = lean_ctor_get(v___x_236_, 1);
lean_inc_ref(v_arg_238_);
v___x_239_ = l_Lean_Expr_appFnCleanup___redArg(v___x_236_);
v___x_240_ = l_Lean_Expr_isApp(v___x_239_);
if (v___x_240_ == 0)
{
lean_dec_ref(v___x_239_);
lean_dec_ref(v_arg_238_);
lean_dec_ref(v_arg_235_);
lean_del_object(v___x_231_);
lean_dec_ref(v_e_157_);
goto v___jp_165_;
}
else
{
lean_object* v_arg_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v_arg_241_ = lean_ctor_get(v___x_239_, 1);
lean_inc_ref(v_arg_241_);
v___x_242_ = l_Lean_Expr_appFnCleanup___redArg(v___x_239_);
v___x_243_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__3));
v___x_244_ = l_Lean_Expr_isConstOf(v___x_242_, v___x_243_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_245_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__6));
v___x_246_ = l_Lean_Expr_isConstOf(v___x_242_, v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; uint8_t v___x_248_; 
v___x_247_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__12));
v___x_248_ = l_Lean_Expr_isConstOf(v___x_242_, v___x_247_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; uint8_t v___x_250_; 
lean_del_object(v___x_231_);
lean_dec_ref(v_e_157_);
v___x_249_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__9));
v___x_250_ = l_Lean_Expr_isConstOf(v___x_242_, v___x_249_);
if (v___x_250_ == 0)
{
uint8_t v___x_251_; 
v___x_251_ = l_Lean_Expr_isApp(v___x_242_);
if (v___x_251_ == 0)
{
lean_dec_ref(v___x_242_);
lean_dec_ref(v_arg_241_);
lean_dec_ref(v_arg_238_);
lean_dec_ref(v_arg_235_);
goto v___jp_165_;
}
else
{
lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_252_ = l_Lean_Expr_appFnCleanup___redArg(v___x_242_);
v___x_253_ = l_Lean_Expr_isApp(v___x_252_);
if (v___x_253_ == 0)
{
lean_dec_ref(v___x_252_);
lean_dec_ref(v_arg_241_);
lean_dec_ref(v_arg_238_);
lean_dec_ref(v_arg_235_);
goto v___jp_165_;
}
else
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = l_Lean_Expr_appFnCleanup___redArg(v___x_252_);
v___x_255_ = l_Lean_Expr_isApp(v___x_254_);
if (v___x_255_ == 0)
{
lean_dec_ref(v___x_254_);
lean_dec_ref(v_arg_241_);
lean_dec_ref(v_arg_238_);
lean_dec_ref(v_arg_235_);
goto v___jp_165_;
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_256_ = l_Lean_Expr_appFnCleanup___redArg(v___x_254_);
v___x_257_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__15));
v___x_258_ = l_Lean_Expr_isConstOf(v___x_256_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__18));
v___x_260_ = l_Lean_Expr_isConstOf(v___x_256_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__21));
v___x_262_ = l_Lean_Expr_isConstOf(v___x_256_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_263_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__27));
v___x_264_ = l_Lean_Expr_isConstOf(v___x_256_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_265_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__24));
v___x_266_ = l_Lean_Expr_isConstOf(v___x_256_, v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__30));
v___x_268_ = l_Lean_Expr_isConstOf(v___x_256_, v___x_267_);
lean_dec_ref(v___x_256_);
if (v___x_268_ == 0)
{
lean_dec_ref(v_arg_241_);
lean_dec_ref(v_arg_238_);
lean_dec_ref(v_arg_235_);
goto v___jp_165_;
}
else
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_241_, v_a_161_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_301_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_301_ == 0)
{
v___x_272_ = v___x_269_;
v_isShared_273_ = v_isSharedCheck_301_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_269_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_301_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
uint8_t v___x_274_; 
v___x_274_ = lean_unbox(v_a_270_);
lean_dec(v_a_270_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_277_; 
lean_dec_ref(v_arg_238_);
lean_dec_ref(v_arg_235_);
v___x_275_ = lean_box(0);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_275_);
v___x_277_ = v___x_272_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
else
{
lean_object* v___x_279_; 
lean_del_object(v___x_272_);
v___x_279_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_238_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
if (lean_obj_tag(v_a_280_) == 0)
{
lean_dec_ref(v_arg_235_);
return v___x_279_;
}
else
{
lean_object* v_val_281_; lean_object* v___x_282_; 
lean_inc_ref(v_a_280_);
lean_dec_ref_known(v___x_279_, 1);
v_val_281_ = lean_ctor_get(v_a_280_, 0);
lean_inc(v_val_281_);
lean_dec_ref_known(v_a_280_, 1);
v___x_282_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_235_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_a_283_);
if (lean_obj_tag(v_a_283_) == 0)
{
lean_dec(v_val_281_);
return v___x_282_;
}
else
{
lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_299_; 
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_299_ == 0)
{
lean_object* v_unused_300_; 
v_unused_300_ = lean_ctor_get(v___x_282_, 0);
lean_dec(v_unused_300_);
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_299_;
goto v_resetjp_284_;
}
else
{
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_299_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v_val_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_298_; 
v_val_287_ = lean_ctor_get(v_a_283_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v_a_283_);
if (v_isSharedCheck_298_ == 0)
{
v___x_289_ = v_a_283_;
v_isShared_290_ = v_isSharedCheck_298_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_val_287_);
lean_dec(v_a_283_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_298_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_291_ = lean_int_add(v_val_281_, v_val_287_);
lean_dec(v_val_287_);
lean_dec(v_val_281_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_291_);
v___x_293_ = v___x_289_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_291_);
v___x_293_ = v_reuseFailAlloc_297_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_295_; 
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_293_);
v___x_295_ = v___x_285_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
}
else
{
lean_dec(v_val_281_);
return v___x_282_;
}
}
}
else
{
lean_dec_ref(v_arg_235_);
return v___x_279_;
}
}
}
}
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec_ref(v_arg_238_);
lean_dec_ref(v_arg_235_);
v_a_302_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_269_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_269_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
}
}
else
{
lean_object* v___x_310_; 
lean_dec_ref(v___x_256_);
v___x_310_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_arg_241_, v_a_161_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_342_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_342_ == 0)
{
v___x_313_ = v___x_310_;
v_isShared_314_ = v_isSharedCheck_342_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_310_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_342_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
uint8_t v___x_315_; 
v___x_315_ = lean_unbox(v_a_311_);
lean_dec(v_a_311_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_318_; 
lean_dec_ref(v_arg_238_);
lean_dec_ref(v_arg_235_);
v___x_316_ = lean_box(0);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v___x_316_);
v___x_318_ = v___x_313_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
else
{
lean_object* v___x_320_; 
lean_del_object(v___x_313_);
v___x_320_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_238_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
if (lean_obj_tag(v_a_321_) == 0)
{
lean_dec_ref(v_arg_235_);
return v___x_320_;
}
else
{
lean_object* v_val_322_; lean_object* v___x_323_; 
lean_inc_ref(v_a_321_);
lean_dec_ref_known(v___x_320_, 1);
v_val_322_ = lean_ctor_get(v_a_321_, 0);
lean_inc(v_val_322_);
lean_dec_ref_known(v_a_321_, 1);
v___x_323_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_235_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_324_);
if (lean_obj_tag(v_a_324_) == 0)
{
lean_dec(v_val_322_);
return v___x_323_;
}
else
{
lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_340_; 
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_340_ == 0)
{
lean_object* v_unused_341_; 
v_unused_341_ = lean_ctor_get(v___x_323_, 0);
lean_dec(v_unused_341_);
v___x_326_ = v___x_323_;
v_isShared_327_ = v_isSharedCheck_340_;
goto v_resetjp_325_;
}
else
{
lean_dec(v___x_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_340_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v_val_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_339_; 
v_val_328_ = lean_ctor_get(v_a_324_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v_a_324_);
if (v_isSharedCheck_339_ == 0)
{
v___x_330_ = v_a_324_;
v_isShared_331_ = v_isSharedCheck_339_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_val_328_);
lean_dec(v_a_324_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_339_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_332_ = lean_int_sub(v_val_322_, v_val_328_);
lean_dec(v_val_328_);
lean_dec(v_val_322_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_332_);
v___x_334_ = v___x_330_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_332_);
v___x_334_ = v_reuseFailAlloc_338_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_336_; 
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v___x_334_);
v___x_336_ = v___x_326_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
return v___x_336_;
}
}
}
}
}
}
else
{
lean_dec(v_val_322_);
return v___x_323_;
}
}
}
else
{
lean_dec_ref(v_arg_235_);
return v___x_320_;
}
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec_ref(v_arg_238_);
lean_dec_ref(v_arg_235_);
v_a_343_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_310_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_310_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
else
{
lean_object* v___x_351_; 
lean_dec_ref(v___x_256_);
v___x_351_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_241_, v_a_161_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_383_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_383_ == 0)
{
v___x_354_ = v___x_351_;
v_isShared_355_ = v_isSharedCheck_383_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_383_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
uint8_t v___x_356_; 
v___x_356_ = lean_unbox(v_a_352_);
lean_dec(v_a_352_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_359_; 
lean_dec_ref(v_arg_238_);
lean_dec_ref(v_arg_235_);
v___x_357_ = lean_box(0);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_357_);
v___x_359_ = v___x_354_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
else
{
lean_object* v___x_361_; 
lean_del_object(v___x_354_);
v___x_361_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_238_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
if (lean_obj_tag(v_a_362_) == 0)
{
lean_dec_ref(v_arg_235_);
return v___x_361_;
}
else
{
lean_object* v_val_363_; lean_object* v___x_364_; 
lean_inc_ref(v_a_362_);
lean_dec_ref_known(v___x_361_, 1);
v_val_363_ = lean_ctor_get(v_a_362_, 0);
lean_inc(v_val_363_);
lean_dec_ref_known(v_a_362_, 1);
v___x_364_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_235_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_a_365_);
if (lean_obj_tag(v_a_365_) == 0)
{
lean_dec(v_val_363_);
return v___x_364_;
}
else
{
lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_381_; 
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; 
v_unused_382_ = lean_ctor_get(v___x_364_, 0);
lean_dec(v_unused_382_);
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_381_;
goto v_resetjp_366_;
}
else
{
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_381_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v_val_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_380_; 
v_val_369_ = lean_ctor_get(v_a_365_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v_a_365_);
if (v_isSharedCheck_380_ == 0)
{
v___x_371_ = v_a_365_;
v_isShared_372_ = v_isSharedCheck_380_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_val_369_);
lean_dec(v_a_365_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_380_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = lean_int_mul(v_val_363_, v_val_369_);
lean_dec(v_val_369_);
lean_dec(v_val_363_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 0, v___x_373_);
v___x_375_ = v___x_371_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_379_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_377_; 
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_375_);
v___x_377_ = v___x_367_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
}
else
{
lean_dec(v_val_363_);
return v___x_364_;
}
}
}
else
{
lean_dec_ref(v_arg_235_);
return v___x_361_;
}
}
}
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec_ref(v_arg_238_);
lean_dec_ref(v_arg_235_);
v_a_384_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_351_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_351_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
else
{
lean_object* v___x_392_; 
lean_dec_ref(v___x_256_);
v___x_392_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_arg_241_, v_a_161_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_424_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_424_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_424_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_424_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
uint8_t v___x_397_; 
v___x_397_ = lean_unbox(v_a_393_);
lean_dec(v_a_393_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; lean_object* v___x_400_; 
lean_dec_ref(v_arg_238_);
lean_dec_ref(v_arg_235_);
v___x_398_ = lean_box(0);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_398_);
v___x_400_ = v___x_395_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
else
{
lean_object* v___x_402_; 
lean_del_object(v___x_395_);
v___x_402_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_238_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
if (lean_obj_tag(v_a_403_) == 0)
{
lean_dec_ref(v_arg_235_);
return v___x_402_;
}
else
{
lean_object* v_val_404_; lean_object* v___x_405_; 
lean_inc_ref(v_a_403_);
lean_dec_ref_known(v___x_402_, 1);
v_val_404_ = lean_ctor_get(v_a_403_, 0);
lean_inc(v_val_404_);
lean_dec_ref_known(v_a_403_, 1);
v___x_405_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_235_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
if (lean_obj_tag(v_a_406_) == 0)
{
lean_dec(v_val_404_);
return v___x_405_;
}
else
{
lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_422_; 
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_422_ == 0)
{
lean_object* v_unused_423_; 
v_unused_423_ = lean_ctor_get(v___x_405_, 0);
lean_dec(v_unused_423_);
v___x_408_ = v___x_405_;
v_isShared_409_ = v_isSharedCheck_422_;
goto v_resetjp_407_;
}
else
{
lean_dec(v___x_405_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_422_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_val_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_421_; 
v_val_410_ = lean_ctor_get(v_a_406_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v_a_406_);
if (v_isSharedCheck_421_ == 0)
{
v___x_412_ = v_a_406_;
v_isShared_413_ = v_isSharedCheck_421_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_val_410_);
lean_dec(v_a_406_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_421_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = lean_int_ediv(v_val_404_, v_val_410_);
lean_dec(v_val_410_);
lean_dec(v_val_404_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_414_);
v___x_416_ = v___x_412_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_420_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_418_; 
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v___x_416_);
v___x_418_ = v___x_408_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
}
else
{
lean_dec(v_val_404_);
return v___x_405_;
}
}
}
else
{
lean_dec_ref(v_arg_235_);
return v___x_402_;
}
}
}
}
else
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
lean_dec_ref(v_arg_238_);
lean_dec_ref(v_arg_235_);
v_a_425_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_432_ == 0)
{
v___x_427_ = v___x_392_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_392_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_425_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
}
else
{
lean_object* v___x_433_; 
lean_dec_ref(v___x_256_);
v___x_433_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_arg_241_, v_a_161_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_465_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_465_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_465_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_465_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
uint8_t v___x_438_; 
v___x_438_ = lean_unbox(v_a_434_);
lean_dec(v_a_434_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; lean_object* v___x_441_; 
lean_dec_ref(v_arg_238_);
lean_dec_ref(v_arg_235_);
v___x_439_ = lean_box(0);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_439_);
v___x_441_ = v___x_436_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
else
{
lean_object* v___x_443_; 
lean_del_object(v___x_436_);
v___x_443_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_238_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_443_) == 0)
{
lean_object* v_a_444_; 
v_a_444_ = lean_ctor_get(v___x_443_, 0);
if (lean_obj_tag(v_a_444_) == 0)
{
lean_dec_ref(v_arg_235_);
return v___x_443_;
}
else
{
lean_object* v_val_445_; lean_object* v___x_446_; 
lean_inc_ref(v_a_444_);
lean_dec_ref_known(v___x_443_, 1);
v_val_445_ = lean_ctor_get(v_a_444_, 0);
lean_inc(v_val_445_);
lean_dec_ref_known(v_a_444_, 1);
v___x_446_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_235_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; 
v_a_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_a_447_);
if (lean_obj_tag(v_a_447_) == 0)
{
lean_dec(v_val_445_);
return v___x_446_;
}
else
{
lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_463_; 
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_463_ == 0)
{
lean_object* v_unused_464_; 
v_unused_464_ = lean_ctor_get(v___x_446_, 0);
lean_dec(v_unused_464_);
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_463_;
goto v_resetjp_448_;
}
else
{
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_463_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v_val_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_462_; 
v_val_451_ = lean_ctor_get(v_a_447_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v_a_447_);
if (v_isSharedCheck_462_ == 0)
{
v___x_453_ = v_a_447_;
v_isShared_454_ = v_isSharedCheck_462_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_val_451_);
lean_dec(v_a_447_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_462_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v___x_457_; 
v___x_455_ = lean_int_emod(v_val_445_, v_val_451_);
lean_dec(v_val_451_);
lean_dec(v_val_445_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 0, v___x_455_);
v___x_457_ = v___x_453_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_461_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_459_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_457_);
v___x_459_ = v___x_449_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
}
else
{
lean_dec(v_val_445_);
return v___x_446_;
}
}
}
else
{
lean_dec_ref(v_arg_235_);
return v___x_443_;
}
}
}
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_dec_ref(v_arg_238_);
lean_dec_ref(v_arg_235_);
v_a_466_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_433_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_433_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
else
{
lean_object* v___x_474_; 
lean_dec_ref(v___x_256_);
v___x_474_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_arg_241_, v_a_161_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_536_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_536_ == 0)
{
v___x_477_ = v___x_474_;
v_isShared_478_ = v_isSharedCheck_536_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_536_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
uint8_t v___x_479_; 
v___x_479_ = lean_unbox(v_a_475_);
lean_dec(v_a_475_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_482_; 
lean_dec_ref(v_arg_238_);
lean_dec_ref(v_arg_235_);
v___x_480_ = lean_box(0);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_480_);
v___x_482_ = v___x_477_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
else
{
lean_object* v___x_484_; 
lean_del_object(v___x_477_);
v___x_484_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_238_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
if (lean_obj_tag(v_a_485_) == 0)
{
lean_dec_ref(v_arg_235_);
return v___x_484_;
}
else
{
lean_object* v_val_486_; lean_object* v___x_487_; 
lean_inc_ref(v_a_485_);
lean_dec_ref_known(v___x_484_, 1);
v_val_486_ = lean_ctor_get(v_a_485_, 0);
lean_inc(v_val_486_);
lean_dec_ref_known(v_a_485_, 1);
v___x_487_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_235_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_527_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_527_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_527_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_527_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
if (lean_obj_tag(v_a_488_) == 0)
{
lean_object* v___x_492_; lean_object* v___x_494_; 
lean_dec(v_val_486_);
v___x_492_ = lean_box(0);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_492_);
v___x_494_ = v___x_490_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
else
{
lean_object* v_val_496_; lean_object* v___x_497_; 
lean_del_object(v___x_490_);
v_val_496_ = lean_ctor_get(v_a_488_, 0);
lean_inc_n(v_val_496_, 2);
lean_dec_ref_known(v_a_488_, 1);
v___x_497_ = l_Lean_Meta_Sym_Arith_checkExp(v_val_496_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_518_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_518_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_518_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_518_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
if (lean_obj_tag(v_a_498_) == 0)
{
lean_object* v___x_502_; lean_object* v___x_504_; 
lean_dec(v_val_496_);
lean_dec(v_val_486_);
v___x_502_ = lean_box(0);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_502_);
v___x_504_ = v___x_500_;
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
else
{
lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_516_; 
v_isSharedCheck_516_ = !lean_is_exclusive(v_a_498_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; 
v_unused_517_ = lean_ctor_get(v_a_498_, 0);
lean_dec(v_unused_517_);
v___x_507_ = v_a_498_;
v_isShared_508_ = v_isSharedCheck_516_;
goto v_resetjp_506_;
}
else
{
lean_dec(v_a_498_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_516_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_509_ = l_Int_pow(v_val_486_, v_val_496_);
lean_dec(v_val_496_);
lean_dec(v_val_486_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_509_);
v___x_511_ = v___x_507_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_515_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_513_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_511_);
v___x_513_ = v___x_500_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_dec(v_val_496_);
lean_dec(v_val_486_);
v_a_519_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_497_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_497_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_dec(v_val_486_);
v_a_528_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_487_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_487_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
else
{
lean_dec_ref(v_arg_235_);
return v___x_484_;
}
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec_ref(v_arg_238_);
lean_dec_ref(v_arg_235_);
v_a_537_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_474_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_474_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
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
lean_object* v___x_545_; 
lean_dec_ref(v___x_242_);
lean_dec_ref(v_arg_241_);
v___x_545_ = l_Lean_Meta_Structural_isInstNegInt___redArg(v_arg_238_, v_a_161_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_574_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_574_ == 0)
{
v___x_548_ = v___x_545_;
v_isShared_549_ = v_isSharedCheck_574_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_545_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_574_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
uint8_t v___x_550_; 
v___x_550_ = lean_unbox(v_a_546_);
lean_dec(v_a_546_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_553_; 
lean_dec_ref(v_arg_235_);
v___x_551_ = lean_box(0);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 0, v___x_551_);
v___x_553_ = v___x_548_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
else
{
lean_object* v___x_555_; 
lean_del_object(v___x_548_);
v___x_555_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_235_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v_a_556_; 
v_a_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc(v_a_556_);
if (lean_obj_tag(v_a_556_) == 0)
{
return v___x_555_;
}
else
{
lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_572_; 
v_isSharedCheck_572_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_572_ == 0)
{
lean_object* v_unused_573_; 
v_unused_573_ = lean_ctor_get(v___x_555_, 0);
lean_dec(v_unused_573_);
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_572_;
goto v_resetjp_557_;
}
else
{
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_572_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v_val_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_571_; 
v_val_560_ = lean_ctor_get(v_a_556_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v_a_556_);
if (v_isSharedCheck_571_ == 0)
{
v___x_562_ = v_a_556_;
v_isShared_563_ = v_isSharedCheck_571_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_val_560_);
lean_dec(v_a_556_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_571_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v___x_566_; 
v___x_564_ = lean_int_neg(v_val_560_);
lean_dec(v_val_560_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_564_);
v___x_566_ = v___x_562_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_564_);
v___x_566_ = v_reuseFailAlloc_570_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_568_; 
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_566_);
v___x_568_ = v___x_558_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
}
else
{
return v___x_555_;
}
}
}
}
else
{
lean_object* v_a_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_582_; 
lean_dec_ref(v_arg_235_);
v_a_575_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_582_ == 0)
{
v___x_577_ = v___x_545_;
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_a_575_);
lean_dec(v___x_545_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_582_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_580_; 
if (v_isShared_578_ == 0)
{
v___x_580_ = v___x_577_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_a_575_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
}
else
{
lean_object* v___x_583_; 
lean_dec_ref(v___x_242_);
lean_dec_ref(v_arg_241_);
lean_dec_ref(v_arg_238_);
lean_dec_ref(v_arg_235_);
v___x_583_ = l_Lean_Meta_Sym_getIntValue_x3f(v_e_157_);
if (lean_obj_tag(v___x_583_) == 1)
{
lean_object* v___x_585_; 
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_583_);
v___x_585_ = v___x_231_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
else
{
lean_object* v___x_587_; lean_object* v___x_589_; 
lean_dec(v___x_583_);
v___x_587_ = lean_box(0);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_587_);
v___x_589_ = v___x_231_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
else
{
lean_dec_ref(v___x_242_);
lean_dec_ref(v_arg_241_);
lean_del_object(v___x_231_);
lean_dec_ref(v_e_157_);
v_i_169_ = v_arg_238_;
v_a_170_ = v_arg_235_;
v___y_171_ = v_a_158_;
v___y_172_ = v_a_159_;
v___y_173_ = v_a_160_;
v___y_174_ = v_a_161_;
v___y_175_ = v_a_162_;
v___y_176_ = v_a_163_;
goto v___jp_168_;
}
}
else
{
lean_dec_ref(v___x_242_);
lean_dec_ref(v_arg_241_);
lean_del_object(v___x_231_);
lean_dec_ref(v_e_157_);
v_i_169_ = v_arg_238_;
v_a_170_ = v_arg_235_;
v___y_171_ = v_a_158_;
v___y_172_ = v_a_159_;
v___y_173_ = v_a_160_;
v___y_174_ = v_a_161_;
v___y_175_ = v_a_162_;
v___y_176_ = v_a_163_;
goto v___jp_168_;
}
}
}
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec_ref(v_e_157_);
v_a_592_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_228_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_228_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
v___jp_165_:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_box(0);
v___x_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
v___jp_168_:
{
lean_object* v___x_177_; 
v___x_177_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_i_169_, v___y_174_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_219_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_219_ == 0)
{
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_219_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_219_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_182_ = l_Lean_Expr_cleanupAnnotations(v_a_178_);
v___x_183_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___closed__1));
v___x_184_ = l_Lean_Expr_isConstOf(v___x_182_, v___x_183_);
lean_dec_ref(v___x_182_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; lean_object* v___x_187_; 
lean_dec_ref(v_a_170_);
v___x_185_ = lean_box(0);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_185_);
v___x_187_ = v___x_180_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
else
{
lean_object* v___x_189_; 
lean_del_object(v___x_180_);
v___x_189_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_a_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_210_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_210_ == 0)
{
v___x_192_ = v___x_189_;
v_isShared_193_ = v_isSharedCheck_210_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_189_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_210_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
if (lean_obj_tag(v_a_190_) == 0)
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = lean_box(0);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_194_);
v___x_196_ = v___x_192_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
else
{
lean_object* v_val_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_209_; 
v_val_198_ = lean_ctor_get(v_a_190_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v_a_190_);
if (v_isSharedCheck_209_ == 0)
{
v___x_200_ = v_a_190_;
v_isShared_201_ = v_isSharedCheck_209_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_val_198_);
lean_dec(v_a_190_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_209_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_202_ = lean_nat_to_int(v_val_198_);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v___x_202_);
v___x_204_ = v___x_200_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_208_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
lean_object* v___x_206_; 
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 0, v___x_204_);
v___x_206_ = v___x_192_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_204_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
}
else
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
v_a_211_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_218_ == 0)
{
v___x_213_ = v___x_189_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_189_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_211_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
}
else
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
lean_dec_ref(v_a_170_);
v_a_220_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_177_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_177_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_157_ = stack[0].m_obj;
lean_object* v_a_158_ = stack[1].m_obj;
lean_object* v_a_159_ = stack[2].m_obj;
lean_object* v_a_160_ = stack[3].m_obj;
lean_object* v_a_161_ = stack[4].m_obj;
lean_object* v_a_162_ = stack[5].m_obj;
lean_object* v_a_163_ = stack[6].m_obj;
lean_object* v_res_600_;
v_res_600_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_e_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
stack->m_obj
 = v_res_600_;
}
lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(lean_object* v_e_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
lean_object* v___x_612_; 
lean_inc_ref(v_e_601_);
v___x_612_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_601_, v_a_605_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_1011_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_615_ = v___x_612_;
v_isShared_616_ = v_isSharedCheck_1011_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_1011_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_617_ = l_Lean_Expr_cleanupAnnotations(v_a_613_);
v___x_618_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__2));
v___x_619_ = l_Lean_Expr_isConstOf(v___x_617_, v___x_618_);
if (v___x_619_ == 0)
{
uint8_t v___x_620_; 
v___x_620_ = l_Lean_Expr_isApp(v___x_617_);
if (v___x_620_ == 0)
{
lean_dec_ref(v___x_617_);
lean_del_object(v___x_615_);
lean_dec_ref(v_e_601_);
goto v___jp_609_;
}
else
{
lean_object* v_arg_621_; lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v_arg_621_ = lean_ctor_get(v___x_617_, 1);
lean_inc_ref(v_arg_621_);
v___x_622_ = l_Lean_Expr_appFnCleanup___redArg(v___x_617_);
v___x_623_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__5));
v___x_624_ = l_Lean_Expr_isConstOf(v___x_622_, v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_625_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__7));
v___x_626_ = l_Lean_Expr_isConstOf(v___x_622_, v___x_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__9));
v___x_628_ = l_Lean_Expr_isConstOf(v___x_622_, v___x_627_);
if (v___x_628_ == 0)
{
uint8_t v___x_629_; 
v___x_629_ = l_Lean_Expr_isApp(v___x_622_);
if (v___x_629_ == 0)
{
lean_dec_ref(v___x_622_);
lean_dec_ref(v_arg_621_);
lean_del_object(v___x_615_);
lean_dec_ref(v_e_601_);
goto v___jp_609_;
}
else
{
lean_object* v_arg_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v_arg_630_ = lean_ctor_get(v___x_622_, 1);
lean_inc_ref(v_arg_630_);
v___x_631_ = l_Lean_Expr_appFnCleanup___redArg(v___x_622_);
v___x_632_ = l_Lean_Expr_isApp(v___x_631_);
if (v___x_632_ == 0)
{
lean_dec_ref(v___x_631_);
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_621_);
lean_del_object(v___x_615_);
lean_dec_ref(v_e_601_);
goto v___jp_609_;
}
else
{
lean_object* v_arg_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v_arg_633_ = lean_ctor_get(v___x_631_, 1);
lean_inc_ref(v_arg_633_);
v___x_634_ = l_Lean_Expr_appFnCleanup___redArg(v___x_631_);
v___x_635_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__12));
v___x_636_ = l_Lean_Expr_isConstOf(v___x_634_, v___x_635_);
if (v___x_636_ == 0)
{
uint8_t v___x_637_; 
lean_del_object(v___x_615_);
lean_dec_ref(v_e_601_);
v___x_637_ = l_Lean_Expr_isApp(v___x_634_);
if (v___x_637_ == 0)
{
lean_dec_ref(v___x_634_);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_621_);
goto v___jp_609_;
}
else
{
lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_638_ = l_Lean_Expr_appFnCleanup___redArg(v___x_634_);
v___x_639_ = l_Lean_Expr_isApp(v___x_638_);
if (v___x_639_ == 0)
{
lean_dec_ref(v___x_638_);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_621_);
goto v___jp_609_;
}
else
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = l_Lean_Expr_appFnCleanup___redArg(v___x_638_);
v___x_641_ = l_Lean_Expr_isApp(v___x_640_);
if (v___x_641_ == 0)
{
lean_dec_ref(v___x_640_);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_621_);
goto v___jp_609_;
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_642_ = l_Lean_Expr_appFnCleanup___redArg(v___x_640_);
v___x_643_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__15));
v___x_644_ = l_Lean_Expr_isConstOf(v___x_642_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__18));
v___x_646_ = l_Lean_Expr_isConstOf(v___x_642_, v___x_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__21));
v___x_648_ = l_Lean_Expr_isConstOf(v___x_642_, v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__24));
v___x_650_ = l_Lean_Expr_isConstOf(v___x_642_, v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_651_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__27));
v___x_652_ = l_Lean_Expr_isConstOf(v___x_642_, v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_653_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__30));
v___x_654_ = l_Lean_Expr_isConstOf(v___x_642_, v___x_653_);
lean_dec_ref(v___x_642_);
if (v___x_654_ == 0)
{
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_621_);
goto v___jp_609_;
}
else
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_633_, v_a_605_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_687_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_687_ == 0)
{
v___x_658_ = v___x_655_;
v_isShared_659_ = v_isSharedCheck_687_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_655_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_687_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
uint8_t v___x_660_; 
v___x_660_ = lean_unbox(v_a_656_);
lean_dec(v_a_656_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; lean_object* v___x_663_; 
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_621_);
v___x_661_ = lean_box(0);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v___x_661_);
v___x_663_ = v___x_658_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
else
{
lean_object* v___x_665_; 
lean_del_object(v___x_658_);
v___x_665_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_630_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
if (lean_obj_tag(v_a_666_) == 0)
{
lean_dec_ref(v_arg_621_);
return v___x_665_;
}
else
{
lean_object* v_val_667_; lean_object* v___x_668_; 
lean_inc_ref(v_a_666_);
lean_dec_ref_known(v___x_665_, 1);
v_val_667_ = lean_ctor_get(v_a_666_, 0);
lean_inc(v_val_667_);
lean_dec_ref_known(v_a_666_, 1);
v___x_668_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_621_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
if (lean_obj_tag(v_a_669_) == 0)
{
lean_dec(v_val_667_);
return v___x_668_;
}
else
{
lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_685_; 
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_685_ == 0)
{
lean_object* v_unused_686_; 
v_unused_686_ = lean_ctor_get(v___x_668_, 0);
lean_dec(v_unused_686_);
v___x_671_ = v___x_668_;
v_isShared_672_ = v_isSharedCheck_685_;
goto v_resetjp_670_;
}
else
{
lean_dec(v___x_668_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_685_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v_val_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_684_; 
v_val_673_ = lean_ctor_get(v_a_669_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v_a_669_);
if (v_isSharedCheck_684_ == 0)
{
v___x_675_ = v_a_669_;
v_isShared_676_ = v_isSharedCheck_684_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_val_673_);
lean_dec(v_a_669_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_684_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_677_ = lean_nat_add(v_val_667_, v_val_673_);
lean_dec(v_val_673_);
lean_dec(v_val_667_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_677_);
v___x_679_ = v___x_675_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_683_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_681_; 
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 0, v___x_679_);
v___x_681_ = v___x_671_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
}
else
{
lean_dec(v_val_667_);
return v___x_668_;
}
}
}
else
{
lean_dec_ref(v_arg_621_);
return v___x_665_;
}
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_621_);
v_a_688_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_655_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_655_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
}
else
{
lean_object* v___x_696_; 
lean_dec_ref(v___x_642_);
v___x_696_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_arg_633_, v_a_605_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_728_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_728_ == 0)
{
v___x_699_ = v___x_696_;
v_isShared_700_ = v_isSharedCheck_728_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_696_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_728_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
uint8_t v___x_701_; 
v___x_701_ = lean_unbox(v_a_697_);
lean_dec(v_a_697_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_704_; 
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_621_);
v___x_702_ = lean_box(0);
if (v_isShared_700_ == 0)
{
lean_ctor_set(v___x_699_, 0, v___x_702_);
v___x_704_ = v___x_699_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
else
{
lean_object* v___x_706_; 
lean_del_object(v___x_699_);
v___x_706_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_630_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
if (lean_obj_tag(v_a_707_) == 0)
{
lean_dec_ref(v_arg_621_);
return v___x_706_;
}
else
{
lean_object* v_val_708_; lean_object* v___x_709_; 
lean_inc_ref(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v_val_708_ = lean_ctor_get(v_a_707_, 0);
lean_inc(v_val_708_);
lean_dec_ref_known(v_a_707_, 1);
v___x_709_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_621_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
if (lean_obj_tag(v_a_710_) == 0)
{
lean_dec(v_val_708_);
return v___x_709_;
}
else
{
lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_726_; 
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v___x_709_, 0);
lean_dec(v_unused_727_);
v___x_712_ = v___x_709_;
v_isShared_713_ = v_isSharedCheck_726_;
goto v_resetjp_711_;
}
else
{
lean_dec(v___x_709_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_726_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v_val_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_725_; 
v_val_714_ = lean_ctor_get(v_a_710_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v_a_710_);
if (v_isSharedCheck_725_ == 0)
{
v___x_716_ = v_a_710_;
v_isShared_717_ = v_isSharedCheck_725_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_val_714_);
lean_dec(v_a_710_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_725_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_718_ = lean_nat_mul(v_val_708_, v_val_714_);
lean_dec(v_val_714_);
lean_dec(v_val_708_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_718_);
v___x_720_ = v___x_716_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_718_);
v___x_720_ = v_reuseFailAlloc_724_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_722_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v___x_720_);
v___x_722_ = v___x_712_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
}
else
{
lean_dec(v_val_708_);
return v___x_709_;
}
}
}
else
{
lean_dec_ref(v_arg_621_);
return v___x_706_;
}
}
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_621_);
v_a_729_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_696_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_696_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
}
else
{
lean_object* v___x_737_; 
lean_dec_ref(v___x_642_);
v___x_737_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_arg_633_, v_a_605_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_769_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_769_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_769_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_769_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
uint8_t v___x_742_; 
v___x_742_ = lean_unbox(v_a_738_);
lean_dec(v_a_738_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v___x_745_; 
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_621_);
v___x_743_ = lean_box(0);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_743_);
v___x_745_ = v___x_740_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
else
{
lean_object* v___x_747_; 
lean_del_object(v___x_740_);
v___x_747_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_630_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
if (lean_obj_tag(v_a_748_) == 0)
{
lean_dec_ref(v_arg_621_);
return v___x_747_;
}
else
{
lean_object* v_val_749_; lean_object* v___x_750_; 
lean_inc_ref(v_a_748_);
lean_dec_ref_known(v___x_747_, 1);
v_val_749_ = lean_ctor_get(v_a_748_, 0);
lean_inc(v_val_749_);
lean_dec_ref_known(v_a_748_, 1);
v___x_750_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_621_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
if (lean_obj_tag(v_a_751_) == 0)
{
lean_dec(v_val_749_);
return v___x_750_;
}
else
{
lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_767_; 
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_767_ == 0)
{
lean_object* v_unused_768_; 
v_unused_768_ = lean_ctor_get(v___x_750_, 0);
lean_dec(v_unused_768_);
v___x_753_ = v___x_750_;
v_isShared_754_ = v_isSharedCheck_767_;
goto v_resetjp_752_;
}
else
{
lean_dec(v___x_750_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_767_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v_val_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_766_; 
v_val_755_ = lean_ctor_get(v_a_751_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v_a_751_);
if (v_isSharedCheck_766_ == 0)
{
v___x_757_ = v_a_751_;
v_isShared_758_ = v_isSharedCheck_766_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_val_755_);
lean_dec(v_a_751_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_766_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_759_ = lean_nat_sub(v_val_749_, v_val_755_);
lean_dec(v_val_755_);
lean_dec(v_val_749_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v___x_759_);
v___x_761_ = v___x_757_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_759_);
v___x_761_ = v_reuseFailAlloc_765_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_763_; 
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_761_);
v___x_763_ = v___x_753_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
}
else
{
lean_dec(v_val_749_);
return v___x_750_;
}
}
}
else
{
lean_dec_ref(v_arg_621_);
return v___x_747_;
}
}
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_621_);
v_a_770_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_737_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_737_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
else
{
lean_object* v___x_778_; 
lean_dec_ref(v___x_642_);
v___x_778_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_arg_633_, v_a_605_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_810_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_810_ == 0)
{
v___x_781_ = v___x_778_;
v_isShared_782_ = v_isSharedCheck_810_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_810_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
uint8_t v___x_783_; 
v___x_783_ = lean_unbox(v_a_779_);
lean_dec(v_a_779_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; lean_object* v___x_786_; 
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_621_);
v___x_784_ = lean_box(0);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_784_);
v___x_786_ = v___x_781_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
else
{
lean_object* v___x_788_; 
lean_del_object(v___x_781_);
v___x_788_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_630_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
if (lean_obj_tag(v_a_789_) == 0)
{
lean_dec_ref(v_arg_621_);
return v___x_788_;
}
else
{
lean_object* v_val_790_; lean_object* v___x_791_; 
lean_inc_ref(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
v_val_790_ = lean_ctor_get(v_a_789_, 0);
lean_inc(v_val_790_);
lean_dec_ref_known(v_a_789_, 1);
v___x_791_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_621_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
if (lean_obj_tag(v_a_792_) == 0)
{
lean_dec(v_val_790_);
return v___x_791_;
}
else
{
lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_808_; 
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_808_ == 0)
{
lean_object* v_unused_809_; 
v_unused_809_ = lean_ctor_get(v___x_791_, 0);
lean_dec(v_unused_809_);
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_808_;
goto v_resetjp_793_;
}
else
{
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_808_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v_val_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_807_; 
v_val_796_ = lean_ctor_get(v_a_792_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v_a_792_);
if (v_isSharedCheck_807_ == 0)
{
v___x_798_ = v_a_792_;
v_isShared_799_ = v_isSharedCheck_807_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_val_796_);
lean_dec(v_a_792_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_807_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___x_802_; 
v___x_800_ = lean_nat_div(v_val_790_, v_val_796_);
lean_dec(v_val_796_);
lean_dec(v_val_790_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_800_);
v___x_802_ = v___x_798_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_800_);
v___x_802_ = v_reuseFailAlloc_806_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_804_; 
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_802_);
v___x_804_ = v___x_794_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
}
else
{
lean_dec(v_val_790_);
return v___x_791_;
}
}
}
else
{
lean_dec_ref(v_arg_621_);
return v___x_788_;
}
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_621_);
v_a_811_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_778_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_778_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
else
{
lean_object* v___x_819_; 
lean_dec_ref(v___x_642_);
v___x_819_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_arg_633_, v_a_605_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_851_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_851_ == 0)
{
v___x_822_ = v___x_819_;
v_isShared_823_ = v_isSharedCheck_851_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_851_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
uint8_t v___x_824_; 
v___x_824_ = lean_unbox(v_a_820_);
lean_dec(v_a_820_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; lean_object* v___x_827_; 
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_621_);
v___x_825_ = lean_box(0);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_825_);
v___x_827_ = v___x_822_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_825_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
else
{
lean_object* v___x_829_; 
lean_del_object(v___x_822_);
v___x_829_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_630_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
if (lean_obj_tag(v_a_830_) == 0)
{
lean_dec_ref(v_arg_621_);
return v___x_829_;
}
else
{
lean_object* v_val_831_; lean_object* v___x_832_; 
lean_inc_ref(v_a_830_);
lean_dec_ref_known(v___x_829_, 1);
v_val_831_ = lean_ctor_get(v_a_830_, 0);
lean_inc(v_val_831_);
lean_dec_ref_known(v_a_830_, 1);
v___x_832_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_621_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
if (lean_obj_tag(v_a_833_) == 0)
{
lean_dec(v_val_831_);
return v___x_832_;
}
else
{
lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_849_; 
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; 
v_unused_850_ = lean_ctor_get(v___x_832_, 0);
lean_dec(v_unused_850_);
v___x_835_ = v___x_832_;
v_isShared_836_ = v_isSharedCheck_849_;
goto v_resetjp_834_;
}
else
{
lean_dec(v___x_832_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_849_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v_val_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_848_; 
v_val_837_ = lean_ctor_get(v_a_833_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v_a_833_);
if (v_isSharedCheck_848_ == 0)
{
v___x_839_ = v_a_833_;
v_isShared_840_ = v_isSharedCheck_848_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_val_837_);
lean_dec(v_a_833_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_848_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_841_ = lean_nat_mod(v_val_831_, v_val_837_);
lean_dec(v_val_837_);
lean_dec(v_val_831_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_841_);
v___x_843_ = v___x_839_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_847_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_845_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v___x_843_);
v___x_845_ = v___x_835_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
}
else
{
lean_dec(v_val_831_);
return v___x_832_;
}
}
}
else
{
lean_dec_ref(v_arg_621_);
return v___x_829_;
}
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_621_);
v_a_852_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_819_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_819_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
else
{
lean_object* v___x_860_; 
lean_dec_ref(v___x_642_);
v___x_860_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_arg_633_, v_a_605_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_910_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_910_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_910_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_910_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
uint8_t v___x_865_; 
v___x_865_ = lean_unbox(v_a_861_);
lean_dec(v_a_861_);
if (v___x_865_ == 0)
{
lean_object* v___x_866_; lean_object* v___x_868_; 
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_621_);
v___x_866_ = lean_box(0);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_866_);
v___x_868_ = v___x_863_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
else
{
lean_object* v___x_870_; 
lean_del_object(v___x_863_);
v___x_870_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_621_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
if (lean_obj_tag(v_a_871_) == 0)
{
lean_dec_ref(v_arg_630_);
return v___x_870_;
}
else
{
lean_object* v_val_872_; lean_object* v___x_873_; 
lean_inc_ref(v_a_871_);
lean_dec_ref_known(v___x_870_, 1);
v_val_872_ = lean_ctor_get(v_a_871_, 0);
lean_inc_n(v_val_872_, 2);
lean_dec_ref_known(v_a_871_, 1);
v___x_873_ = l_Lean_Meta_Sym_Arith_checkExp(v_val_872_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_901_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_901_ == 0)
{
v___x_876_ = v___x_873_;
v_isShared_877_ = v_isSharedCheck_901_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_901_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
if (lean_obj_tag(v_a_874_) == 0)
{
lean_object* v___x_878_; lean_object* v___x_880_; 
lean_dec(v_val_872_);
lean_dec_ref(v_arg_630_);
v___x_878_ = lean_box(0);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_878_);
v___x_880_ = v___x_876_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
else
{
lean_object* v___x_882_; 
lean_dec_ref_known(v_a_874_, 1);
lean_del_object(v___x_876_);
v___x_882_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_630_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
if (lean_obj_tag(v_a_883_) == 0)
{
lean_dec(v_val_872_);
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
v___x_891_ = lean_nat_pow(v_val_887_, v_val_872_);
lean_dec(v_val_872_);
lean_dec(v_val_887_);
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
lean_dec(v_val_872_);
return v___x_882_;
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec(v_val_872_);
lean_dec_ref(v_arg_630_);
v_a_902_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_873_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_873_);
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
lean_dec_ref(v_arg_630_);
return v___x_870_;
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_621_);
v_a_911_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_860_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_860_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
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
lean_object* v___x_919_; 
lean_dec_ref(v___x_634_);
lean_dec_ref(v_arg_633_);
lean_dec_ref(v_arg_630_);
lean_dec_ref(v_arg_621_);
v___x_919_ = l_Lean_Meta_Sym_getNatValue_x3f(v_e_601_);
if (lean_obj_tag(v___x_919_) == 1)
{
lean_object* v___x_921_; 
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_919_);
v___x_921_ = v___x_615_;
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
else
{
lean_object* v___x_923_; lean_object* v___x_925_; 
lean_dec(v___x_919_);
v___x_923_ = lean_box(0);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_923_);
v___x_925_ = v___x_615_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
}
else
{
lean_object* v___x_927_; 
lean_dec_ref(v___x_622_);
lean_del_object(v___x_615_);
lean_dec_ref(v_e_601_);
v___x_927_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_621_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; 
v_a_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc(v_a_928_);
if (lean_obj_tag(v_a_928_) == 0)
{
return v___x_927_;
}
else
{
lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_945_; 
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; 
v_unused_946_ = lean_ctor_get(v___x_927_, 0);
lean_dec(v_unused_946_);
v___x_930_ = v___x_927_;
v_isShared_931_ = v_isSharedCheck_945_;
goto v_resetjp_929_;
}
else
{
lean_dec(v___x_927_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_945_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v_val_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_944_; 
v_val_932_ = lean_ctor_get(v_a_928_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v_a_928_);
if (v_isSharedCheck_944_ == 0)
{
v___x_934_ = v_a_928_;
v_isShared_935_ = v_isSharedCheck_944_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_val_932_);
lean_dec(v_a_928_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_944_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_936_ = lean_unsigned_to_nat(1u);
v___x_937_ = lean_nat_add(v_val_932_, v___x_936_);
lean_dec(v_val_932_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_937_);
v___x_939_ = v___x_934_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_937_);
v___x_939_ = v_reuseFailAlloc_943_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_941_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_939_);
v___x_941_ = v___x_930_;
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
}
}
}
}
else
{
return v___x_927_;
}
}
}
else
{
lean_object* v___x_947_; 
lean_dec_ref(v___x_622_);
lean_del_object(v___x_615_);
lean_dec_ref(v_e_601_);
v___x_947_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_621_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_968_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_968_ == 0)
{
v___x_950_ = v___x_947_;
v_isShared_951_ = v_isSharedCheck_968_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_947_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_968_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
if (lean_obj_tag(v_a_948_) == 0)
{
lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_952_ = lean_box(0);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v___x_952_);
v___x_954_ = v___x_950_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
else
{
lean_object* v_val_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_967_; 
v_val_956_ = lean_ctor_get(v_a_948_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v_a_948_);
if (v_isSharedCheck_967_ == 0)
{
v___x_958_ = v_a_948_;
v_isShared_959_ = v_isSharedCheck_967_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_val_956_);
lean_dec(v_a_948_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_967_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_960_ = l_Int_toNat(v_val_956_);
lean_dec(v_val_956_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v___x_960_);
v___x_962_ = v___x_958_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v___x_960_);
v___x_962_ = v_reuseFailAlloc_966_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_964_; 
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v___x_962_);
v___x_964_ = v___x_950_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
v_a_969_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_947_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_947_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
else
{
lean_object* v___x_977_; 
lean_dec_ref(v___x_622_);
lean_del_object(v___x_615_);
lean_dec_ref(v_e_601_);
v___x_977_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_arg_621_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_998_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_998_ == 0)
{
v___x_980_ = v___x_977_;
v_isShared_981_ = v_isSharedCheck_998_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_998_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
if (lean_obj_tag(v_a_978_) == 0)
{
lean_object* v___x_982_; lean_object* v___x_984_; 
v___x_982_ = lean_box(0);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_982_);
v___x_984_ = v___x_980_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_982_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
else
{
lean_object* v_val_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_997_; 
v_val_986_ = lean_ctor_get(v_a_978_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v_a_978_);
if (v_isSharedCheck_997_ == 0)
{
v___x_988_ = v_a_978_;
v_isShared_989_ = v_isSharedCheck_997_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_val_986_);
lean_dec(v_a_978_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_997_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_990_ = lean_nat_abs(v_val_986_);
lean_dec(v_val_986_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_990_);
v___x_992_ = v___x_988_;
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
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_992_);
v___x_994_ = v___x_980_;
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
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
v_a_999_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_977_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_977_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
}
}
else
{
lean_object* v___x_1007_; lean_object* v___x_1009_; 
lean_dec_ref(v___x_617_);
lean_dec_ref(v_e_601_);
v___x_1007_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__31));
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_1007_);
v___x_1009_ = v___x_615_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_dec_ref(v_e_601_);
v_a_1012_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_612_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_612_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
v___jp_609_:
{
lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_610_ = lean_box(0);
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
return v___x_611_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_601_ = stack[0].m_obj;
lean_object* v_a_602_ = stack[1].m_obj;
lean_object* v_a_603_ = stack[2].m_obj;
lean_object* v_a_604_ = stack[3].m_obj;
lean_object* v_a_605_ = stack[4].m_obj;
lean_object* v_a_606_ = stack[5].m_obj;
lean_object* v_a_607_ = stack[6].m_obj;
lean_object* v_res_1020_;
v_res_1020_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_e_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_);
stack->m_obj
 = v_res_1020_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___boxed(lean_object* v_e_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_e_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore___boxed(lean_object* v_e_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_e_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore_spec__1(lean_object* v_a_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_nat_to_int(v_a_1039_);
return v___x_1040_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_evalNat_x3f(lean_object* v_e_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_e_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
return v___x_1049_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_evalNat_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1041_ = stack[0].m_obj;
lean_object* v_a_1042_ = stack[1].m_obj;
lean_object* v_a_1043_ = stack[2].m_obj;
lean_object* v_a_1044_ = stack[3].m_obj;
lean_object* v_a_1045_ = stack[4].m_obj;
lean_object* v_a_1046_ = stack[5].m_obj;
lean_object* v_a_1047_ = stack[6].m_obj;
lean_object* v_res_1050_;
v_res_1050_ = l_Lean_Meta_Sym_Arith_evalNat_x3f(v_e_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
stack->m_obj
 = v_res_1050_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_evalNat_x3f___boxed(lean_object* v_e_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_Meta_Sym_Arith_evalNat_x3f(v_e_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
return v_res_1059_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_evalInt_x3f(lean_object* v_e_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalIntCore(v_e_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v___x_1068_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_evalInt_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1060_ = stack[0].m_obj;
lean_object* v_a_1061_ = stack[1].m_obj;
lean_object* v_a_1062_ = stack[2].m_obj;
lean_object* v_a_1063_ = stack[3].m_obj;
lean_object* v_a_1064_ = stack[4].m_obj;
lean_object* v_a_1065_ = stack[5].m_obj;
lean_object* v_a_1066_ = stack[6].m_obj;
lean_object* v_res_1069_;
v_res_1069_ = l_Lean_Meta_Sym_Arith_evalInt_x3f(v_e_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
stack->m_obj
 = v_res_1069_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_evalInt_x3f___boxed(lean_object* v_e_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_Meta_Sym_Arith_evalInt_x3f(v_e_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
return v_res_1078_;
}
}
lean_object* l_Lean_Meta_Sym_Arith_isOffset_x3f(lean_object* v_e_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1079_, v_a_1083_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
lean_dec_ref_known(v___x_1090_, 1);
v___x_1092_ = l_Lean_Expr_cleanupAnnotations(v_a_1091_);
v___x_1093_ = l_Lean_Expr_isApp(v___x_1092_);
if (v___x_1093_ == 0)
{
lean_dec_ref(v___x_1092_);
goto v___jp_1087_;
}
else
{
lean_object* v_arg_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v_arg_1094_ = lean_ctor_get(v___x_1092_, 1);
lean_inc_ref(v_arg_1094_);
v___x_1095_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1092_);
v___x_1096_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__9));
v___x_1097_ = l_Lean_Expr_isConstOf(v___x_1095_, v___x_1096_);
if (v___x_1097_ == 0)
{
uint8_t v___x_1098_; 
v___x_1098_ = l_Lean_Expr_isApp(v___x_1095_);
if (v___x_1098_ == 0)
{
lean_dec_ref(v___x_1095_);
lean_dec_ref(v_arg_1094_);
goto v___jp_1087_;
}
else
{
lean_object* v_arg_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v_arg_1099_ = lean_ctor_get(v___x_1095_, 1);
lean_inc_ref(v_arg_1099_);
v___x_1100_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1095_);
v___x_1101_ = l_Lean_Expr_isApp(v___x_1100_);
if (v___x_1101_ == 0)
{
lean_dec_ref(v___x_1100_);
lean_dec_ref(v_arg_1099_);
lean_dec_ref(v_arg_1094_);
goto v___jp_1087_;
}
else
{
lean_object* v_arg_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v_arg_1102_ = lean_ctor_get(v___x_1100_, 1);
lean_inc_ref(v_arg_1102_);
v___x_1103_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1100_);
v___x_1104_ = l_Lean_Expr_isApp(v___x_1103_);
if (v___x_1104_ == 0)
{
lean_dec_ref(v___x_1103_);
lean_dec_ref(v_arg_1102_);
lean_dec_ref(v_arg_1099_);
lean_dec_ref(v_arg_1094_);
goto v___jp_1087_;
}
else
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1103_);
v___x_1106_ = l_Lean_Expr_isApp(v___x_1105_);
if (v___x_1106_ == 0)
{
lean_dec_ref(v___x_1105_);
lean_dec_ref(v_arg_1102_);
lean_dec_ref(v_arg_1099_);
lean_dec_ref(v_arg_1094_);
goto v___jp_1087_;
}
else
{
lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1105_);
v___x_1108_ = l_Lean_Expr_isApp(v___x_1107_);
if (v___x_1108_ == 0)
{
lean_dec_ref(v___x_1107_);
lean_dec_ref(v_arg_1102_);
lean_dec_ref(v_arg_1099_);
lean_dec_ref(v_arg_1094_);
goto v___jp_1087_;
}
else
{
lean_object* v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1109_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1107_);
v___x_1110_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore___closed__30));
v___x_1111_ = l_Lean_Expr_isConstOf(v___x_1109_, v___x_1110_);
lean_dec_ref(v___x_1109_);
if (v___x_1111_ == 0)
{
lean_dec_ref(v_arg_1102_);
lean_dec_ref(v_arg_1099_);
lean_dec_ref(v_arg_1094_);
goto v___jp_1087_;
}
else
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_arg_1102_, v_a_1083_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1175_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1115_ = v___x_1112_;
v_isShared_1116_ = v_isSharedCheck_1175_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1175_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
uint8_t v___x_1117_; 
v___x_1117_ = lean_unbox(v_a_1113_);
lean_dec(v_a_1113_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1120_; 
lean_dec_ref(v_arg_1099_);
lean_dec_ref(v_arg_1094_);
v___x_1118_ = lean_box(0);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1118_);
v___x_1120_ = v___x_1115_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
else
{
lean_object* v___x_1122_; 
lean_del_object(v___x_1115_);
v___x_1122_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_evalNatCore(v_arg_1094_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1166_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1125_ = v___x_1122_;
v_isShared_1126_ = v_isSharedCheck_1166_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1122_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1166_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
if (lean_obj_tag(v_a_1123_) == 0)
{
lean_object* v___x_1127_; lean_object* v___x_1129_; 
lean_dec_ref(v_arg_1099_);
v___x_1127_ = lean_box(0);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v___x_1127_);
v___x_1129_ = v___x_1125_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v___x_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
else
{
lean_object* v_val_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1165_; 
lean_del_object(v___x_1125_);
v_val_1131_ = lean_ctor_get(v_a_1123_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_a_1123_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1133_ = v_a_1123_;
v_isShared_1134_ = v_isSharedCheck_1165_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_val_1131_);
lean_dec(v_a_1123_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1165_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; 
v___x_1135_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_getOffset(v_arg_1099_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1156_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1138_ = v___x_1135_;
v_isShared_1139_ = v_isSharedCheck_1156_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1135_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1156_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v_fst_1140_; lean_object* v_snd_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1155_; 
v_fst_1140_ = lean_ctor_get(v_a_1136_, 0);
v_snd_1141_ = lean_ctor_get(v_a_1136_, 1);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_a_1136_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1143_ = v_a_1136_;
v_isShared_1144_ = v_isSharedCheck_1155_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_snd_1141_);
lean_inc(v_fst_1140_);
lean_dec(v_a_1136_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1155_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1145_ = lean_nat_add(v_snd_1141_, v_val_1131_);
lean_dec(v_val_1131_);
lean_dec(v_snd_1141_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v___x_1145_);
v___x_1147_ = v___x_1143_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_fst_1140_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
lean_object* v___x_1149_; 
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1147_);
v___x_1149_ = v___x_1133_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1151_; 
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1149_);
v___x_1151_ = v___x_1138_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_del_object(v___x_1133_);
lean_dec(v_val_1131_);
v_a_1157_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1135_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1135_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec_ref(v_arg_1099_);
v_a_1167_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1122_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1122_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec_ref(v_arg_1099_);
lean_dec_ref(v_arg_1094_);
v_a_1176_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1112_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1112_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
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
lean_object* v___x_1184_; 
lean_dec_ref(v___x_1095_);
v___x_1184_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_getOffset(v_arg_1094_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1204_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1204_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1204_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v_fst_1189_; lean_object* v_snd_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1203_; 
v_fst_1189_ = lean_ctor_get(v_a_1185_, 0);
v_snd_1190_ = lean_ctor_get(v_a_1185_, 1);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_a_1185_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1192_ = v_a_1185_;
v_isShared_1193_ = v_isSharedCheck_1203_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_snd_1190_);
lean_inc(v_fst_1189_);
lean_dec(v_a_1185_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1203_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1194_ = lean_unsigned_to_nat(1u);
v___x_1195_ = lean_nat_add(v_snd_1190_, v___x_1194_);
lean_dec(v_snd_1190_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v___x_1195_);
v___x_1197_ = v___x_1192_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_fst_1189_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___x_1198_);
v___x_1200_ = v___x_1187_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1198_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
v_a_1205_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1184_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1184_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
v_a_1213_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1090_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1090_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
v___jp_1087_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = lean_box(0);
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
return v___x_1089_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Arith_isOffset_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1079_ = stack[0].m_obj;
lean_object* v_a_1080_ = stack[1].m_obj;
lean_object* v_a_1081_ = stack[2].m_obj;
lean_object* v_a_1082_ = stack[3].m_obj;
lean_object* v_a_1083_ = stack[4].m_obj;
lean_object* v_a_1084_ = stack[5].m_obj;
lean_object* v_a_1085_ = stack[6].m_obj;
lean_object* v_res_1221_;
v_res_1221_ = l_Lean_Meta_Sym_Arith_isOffset_x3f(v_e_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
stack->m_obj
 = v_res_1221_;
}
lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_getOffset(lean_object* v_e_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_){
_start:
{
lean_object* v___x_1230_; 
lean_inc_ref(v_e_1222_);
v___x_1230_ = l_Lean_Meta_Sym_Arith_isOffset_x3f(v_e_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1244_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1244_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1244_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
if (lean_obj_tag(v_a_1231_) == 0)
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v_e_1222_);
lean_ctor_set(v___x_1236_, 1, v___x_1235_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v___x_1236_);
v___x_1238_ = v___x_1233_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
else
{
lean_object* v_val_1240_; lean_object* v___x_1242_; 
lean_dec_ref(v_e_1222_);
v_val_1240_ = lean_ctor_get(v_a_1231_, 0);
lean_inc(v_val_1240_);
lean_dec_ref_known(v_a_1231_, 1);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 0, v_val_1240_);
v___x_1242_ = v___x_1233_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_val_1240_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec_ref(v_e_1222_);
v_a_1245_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1230_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1230_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_getOffset_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1222_ = stack[0].m_obj;
lean_object* v_a_1223_ = stack[1].m_obj;
lean_object* v_a_1224_ = stack[2].m_obj;
lean_object* v_a_1225_ = stack[3].m_obj;
lean_object* v_a_1226_ = stack[4].m_obj;
lean_object* v_a_1227_ = stack[5].m_obj;
lean_object* v_a_1228_ = stack[6].m_obj;
lean_object* v_res_1253_;
v_res_1253_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_getOffset(v_e_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
stack->m_obj
 = v_res_1253_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_getOffset___boxed(lean_object* v_e_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l___private_Lean_Meta_Sym_Arith_EvalNum_0__Lean_Meta_Sym_Arith_getOffset(v_e_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_isOffset_x3f___boxed(lean_object* v_e_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_Meta_Sym_Arith_isOffset_x3f(v_e_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
return v_res_1271_;
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

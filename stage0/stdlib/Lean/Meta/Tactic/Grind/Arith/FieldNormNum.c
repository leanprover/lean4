// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.FieldNormNum
// Imports: public import Lean.Meta.Basic import Init.Grind.FieldNormNum import Lean.Meta.Tactic.Grind.SynthInstance import Lean.Meta.AppBuilder import Lean.Meta.LitValues import Lean.Util.SafeExponentiation
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
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToExprRat_mkInt(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_isDefEqI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Rat_inv(lean_object*);
lean_object* l_Rat_neg(lean_object*);
lean_object* l_Rat_div___boxed(lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* l_Rat_mul___boxed(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_checkExponent(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Rat_zpow(lean_object*, lean_object*);
lean_object* l_Lean_mkApp9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_pow(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
lean_object* l_Lean_Meta_getDecLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkWithKernel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Field"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toCommRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(255, 76, 50, 100, 6, 21, 71, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CommRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "toRing"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(247, 129, 99, 43, 16, 237, 154, 169)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "toSemiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(155, 231, 134, 53, 190, 181, 242, 194)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IsCharP"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(193, 211, 245, 119, 67, 24, 212, 73)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Semiring"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__3_value),LEAN_SCALAR_PTR_LITERAL(7, 205, 186, 60, 7, 38, 135, 75)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__2_value),LEAN_SCALAR_PTR_LITERAL(232, 23, 103, 115, 5, 120, 143, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 225, 92, 14, 170, 61, 170, 140)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__2_value),LEAN_SCALAR_PTR_LITERAL(8, 241, 181, 204, 215, 46, 40, 252)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 70, 113, 198, 157, 211, 131, 18)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 88, 233, 125, 69, 12, 189, 21)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNeg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 233, 103, 154, 53, 22, 86, 139)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toInv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 152, 64, 108, 234, 163, 46, 107)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "npow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 91, 39, 101, 227, 157, 49, 255)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zpow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(69, 220, 161, 90, 16, 219, 47, 173)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 49, 23, 61, 125, 46, 165, 129)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 150, 10, 46, 185, 54, 59, 167)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 97, 73, 37, 143, 22, 233, 204)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNatCastInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNatCastInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "intCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 189, 244, 99, 68, 50, 19, 202)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isIntCastInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isIntCastInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IntCast"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 186, 193, 83, 149, 255, 18, 69)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 203, 124, 26, 63, 107, 241, 61)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(231, 55, 105, 214, 206, 30, 120, 51)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instDiv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(231, 55, 105, 214, 206, 30, 120, 51)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(136, 163, 206, 229, 214, 76, 207, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__13_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__14;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval_spec__0(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_inv, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_neg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__1_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_div___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_sub, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_add, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__6_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Inv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__8_value),LEAN_SCALAR_PTR_LITERAL(142, 68, 231, 210, 96, 163, 154, 19)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__9_value),LEAN_SCALAR_PTR_LITERAL(63, 31, 248, 222, 13, 64, 40, 141)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__11_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__12_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__15_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__17_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__18_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__20_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__22_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__22_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__24_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__25_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__24_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NormNum"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "add_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__27_value),LEAN_SCALAR_PTR_LITERAL(151, 14, 160, 138, 120, 252, 73, 10)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mul_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value),LEAN_SCALAR_PTR_LITERAL(136, 255, 164, 25, 71, 39, 174, 147)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "sub_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__31_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__31_value),LEAN_SCALAR_PTR_LITERAL(2, 162, 150, 24, 33, 169, 123, 203)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "div_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__33_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__33_value),LEAN_SCALAR_PTR_LITERAL(177, 1, 34, 4, 92, 31, 232, 201)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "zpow_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35_value),LEAN_SCALAR_PTR_LITERAL(252, 102, 170, 198, 226, 30, 47, 17)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__40 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__40_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__43_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__43 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__43_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "npow_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__45 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__45_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__45_value),LEAN_SCALAR_PTR_LITERAL(37, 32, 174, 21, 58, 233, 39, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "neg_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value),LEAN_SCALAR_PTR_LITERAL(3, 23, 32, 100, 239, 35, 23, 252)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "inv_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__49 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__49_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__49_value),LEAN_SCALAR_PTR_LITERAL(0, 163, 29, 198, 30, 103, 3, 4)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ofNat_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__51 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__51_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__51_value),LEAN_SCALAR_PTR_LITERAL(136, 66, 33, 38, 61, 161, 62, 214)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "natCast_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__53 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__53_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__53_value),LEAN_SCALAR_PTR_LITERAL(117, 220, 31, 33, 212, 54, 218, 117)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "intCast_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__55 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__55_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__55_value),LEAN_SCALAR_PTR_LITERAL(30, 152, 143, 43, 0, 215, 188, 72)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalFieldExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalFieldExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__0;
static const lean_string_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eq_mul_inv"};
static const lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 252, 205, 142, 101, 192, 24, 119)}};
static const lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "eq_inv"};
static const lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(123, 176, 154, 3, 27, 184, 143, 27)}};
static const lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "eq_int"};
static const lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(149, 254, 214, 162, 140, 117, 132, 155)}};
static const lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__14(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_34_ = l_Lean_mkNatLit(v___x_33_);
return v___x_34_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg(lean_object* v_type_35_, lean_object* v_x_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_){
_start:
{
lean_object* v___x_42_; 
lean_inc_ref(v_type_35_);
v___x_42_ = l_Lean_Meta_getDecLevel_x3f(v_type_35_, v_a_37_, v_a_38_, v_a_39_, v_a_40_);
if (lean_obj_tag(v___x_42_) == 0)
{
lean_object* v_a_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_119_; 
v_a_43_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_119_ == 0)
{
v___x_45_ = v___x_42_;
v_isShared_46_ = v_isSharedCheck_119_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_a_43_);
lean_dec(v___x_42_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_119_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
if (lean_obj_tag(v_a_43_) == 1)
{
lean_object* v_val_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
lean_del_object(v___x_45_);
v_val_47_ = lean_ctor_get(v_a_43_, 0);
lean_inc_n(v_val_47_, 2);
lean_dec_ref_known(v_a_43_, 1);
v___x_48_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__3));
v___x_49_ = lean_box(0);
v___x_50_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_50_, 0, v_val_47_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
lean_inc_ref(v___x_50_);
v___x_51_ = l_Lean_mkConst(v___x_48_, v___x_50_);
lean_inc_ref(v_type_35_);
v___x_52_ = l_Lean_Expr_app___override(v___x_51_, v_type_35_);
v___x_53_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_52_, v_a_37_, v_a_38_, v_a_39_, v_a_40_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_106_; 
v_a_54_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_106_ == 0)
{
v___x_56_ = v___x_53_;
v_isShared_57_ = v_isSharedCheck_106_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_53_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_106_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
if (lean_obj_tag(v_a_54_) == 1)
{
lean_object* v_val_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
lean_del_object(v___x_56_);
v_val_58_ = lean_ctor_get(v_a_54_, 0);
lean_inc_n(v_val_58_, 2);
lean_dec_ref_known(v_a_54_, 1);
v___x_59_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__5));
lean_inc_ref_n(v___x_50_, 3);
v___x_60_ = l_Lean_mkConst(v___x_59_, v___x_50_);
lean_inc_ref_n(v_type_35_, 4);
v___x_61_ = l_Lean_mkAppB(v___x_60_, v_type_35_, v_val_58_);
v___x_62_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__8));
v___x_63_ = l_Lean_mkConst(v___x_62_, v___x_50_);
v___x_64_ = l_Lean_mkAppB(v___x_63_, v_type_35_, v___x_61_);
v___x_65_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__11));
v___x_66_ = l_Lean_mkConst(v___x_65_, v___x_50_);
lean_inc_ref(v___x_64_);
v___x_67_ = l_Lean_mkAppB(v___x_66_, v_type_35_, v___x_64_);
v___x_68_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__13));
v___x_69_ = l_Lean_mkConst(v___x_68_, v___x_50_);
v___x_70_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__14, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__14);
lean_inc_ref(v___x_67_);
v___x_71_ = l_Lean_mkApp3(v___x_69_, v_type_35_, v___x_67_, v___x_70_);
lean_inc_ref(v___x_71_);
v___x_72_ = l_Lean_Meta_checkWithKernel(v___x_71_, v_a_37_, v_a_38_, v_a_39_, v_a_40_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v___x_73_; 
lean_dec_ref_known(v___x_72_, 1);
v___x_73_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v___x_71_, v_a_37_, v_a_38_, v_a_39_, v_a_40_);
if (lean_obj_tag(v___x_73_) == 0)
{
lean_object* v_a_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_85_; 
v_a_74_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_85_ == 0)
{
v___x_76_ = v___x_73_;
v_isShared_77_ = v_isSharedCheck_85_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_a_74_);
lean_dec(v___x_73_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_85_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
if (lean_obj_tag(v_a_74_) == 1)
{
lean_object* v_val_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
lean_del_object(v___x_76_);
v_val_78_ = lean_ctor_get(v_a_74_, 0);
lean_inc(v_val_78_);
lean_dec_ref_known(v_a_74_, 1);
v___x_79_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_79_, 0, v_val_47_);
lean_ctor_set(v___x_79_, 1, v_type_35_);
lean_ctor_set(v___x_79_, 2, v_val_58_);
lean_ctor_set(v___x_79_, 3, v_val_78_);
lean_ctor_set(v___x_79_, 4, v___x_64_);
lean_ctor_set(v___x_79_, 5, v___x_67_);
lean_inc(v_a_40_);
lean_inc_ref(v_a_39_);
lean_inc(v_a_38_);
lean_inc_ref(v_a_37_);
v___x_80_ = lean_apply_6(v_x_36_, v___x_79_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, lean_box(0));
return v___x_80_;
}
else
{
lean_object* v___x_81_; lean_object* v___x_83_; 
lean_dec(v_a_74_);
lean_dec_ref(v___x_67_);
lean_dec_ref(v___x_64_);
lean_dec(v_val_58_);
lean_dec(v_val_47_);
lean_dec_ref(v_x_36_);
lean_dec_ref(v_type_35_);
v___x_81_ = lean_box(0);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 0, v___x_81_);
v___x_83_ = v___x_76_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_81_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
else
{
lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_93_; 
lean_dec_ref(v___x_67_);
lean_dec_ref(v___x_64_);
lean_dec(v_val_58_);
lean_dec(v_val_47_);
lean_dec_ref(v_x_36_);
lean_dec_ref(v_type_35_);
v_a_86_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_93_ == 0)
{
v___x_88_ = v___x_73_;
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_73_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_91_; 
if (v_isShared_89_ == 0)
{
v___x_91_ = v___x_88_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_a_86_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
else
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_101_; 
lean_dec_ref(v___x_71_);
lean_dec_ref(v___x_67_);
lean_dec_ref(v___x_64_);
lean_dec(v_val_58_);
lean_dec(v_val_47_);
lean_dec_ref(v_x_36_);
lean_dec_ref(v_type_35_);
v_a_94_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_101_ == 0)
{
v___x_96_ = v___x_72_;
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_72_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_101_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_94_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
else
{
lean_object* v___x_102_; lean_object* v___x_104_; 
lean_dec(v_a_54_);
lean_dec_ref_known(v___x_50_, 2);
lean_dec(v_val_47_);
lean_dec_ref(v_x_36_);
lean_dec_ref(v_type_35_);
v___x_102_ = lean_box(0);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 0, v___x_102_);
v___x_104_ = v___x_56_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_102_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
else
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
lean_dec_ref_known(v___x_50_, 2);
lean_dec(v_val_47_);
lean_dec_ref(v_x_36_);
lean_dec_ref(v_type_35_);
v_a_107_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v___x_53_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_53_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_107_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
else
{
lean_object* v___x_115_; lean_object* v___x_117_; 
lean_dec(v_a_43_);
lean_dec_ref(v_x_36_);
lean_dec_ref(v_type_35_);
v___x_115_ = lean_box(0);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 0, v___x_115_);
v___x_117_ = v___x_45_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_115_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
lean_dec_ref(v_x_36_);
lean_dec_ref(v_type_35_);
v_a_120_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_42_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_42_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_35_ = stack[0].m_obj;
lean_object* v_x_36_ = stack[1].m_obj;
lean_object* v_a_37_ = stack[2].m_obj;
lean_object* v_a_38_ = stack[3].m_obj;
lean_object* v_a_39_ = stack[4].m_obj;
lean_object* v_a_40_ = stack[5].m_obj;
lean_object* v_res_128_;
v_res_128_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg(v_type_35_, v_x_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_);
stack->m_obj
 = v_res_128_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___boxed(lean_object* v_type_129_, lean_object* v_x_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg(v_type_129_, v_x_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
return v_res_136_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f(lean_object* v_00_u03b1_137_, lean_object* v_type_138_, lean_object* v_x_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg(v_type_138_, v_x_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
return v___x_145_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_138_ = stack[1].m_obj;
lean_object* v_x_139_ = stack[2].m_obj;
lean_object* v_a_140_ = stack[3].m_obj;
lean_object* v_a_141_ = stack[4].m_obj;
lean_object* v_a_142_ = stack[5].m_obj;
lean_object* v_a_143_ = stack[6].m_obj;
lean_object* v_res_146_;
v_res_146_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f(lean_box(0), v_type_138_, v_x_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_);
stack->m_obj
 = v_res_146_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___boxed(lean_object* v_00_u03b1_147_, lean_object* v_type_148_, lean_object* v_x_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f(v_00_u03b1_147_, v_type_148_, v_x_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
return v_res_155_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst(lean_object* v_inst_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_u_173_; lean_object* v_type_174_; lean_object* v_semiringInst_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_u_173_ = lean_ctor_get(v_a_167_, 0);
v_type_174_ = lean_ctor_get(v_a_167_, 1);
v_semiringInst_175_ = lean_ctor_get(v_a_167_, 5);
v___x_176_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__1));
v___x_177_ = lean_box(0);
lean_inc(v_u_173_);
v___x_178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_178_, 0, v_u_173_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
lean_inc_ref(v___x_178_);
v___x_179_ = l_Lean_mkConst(v___x_176_, v___x_178_);
v___x_180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4));
v___x_181_ = l_Lean_mkConst(v___x_180_, v___x_178_);
lean_inc_ref(v_semiringInst_175_);
lean_inc_ref_n(v_type_174_, 2);
v___x_182_ = l_Lean_mkAppB(v___x_181_, v_type_174_, v_semiringInst_175_);
v___x_183_ = l_Lean_mkAppB(v___x_179_, v_type_174_, v___x_182_);
v___x_184_ = l_Lean_Meta_isDefEqI(v_inst_166_, v___x_183_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_193_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_193_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_189_, 0, v_a_185_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_189_);
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
else
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
v_a_194_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_184_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_184_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_166_ = stack[0].m_obj;
lean_object* v_a_167_ = stack[1].m_obj;
lean_object* v_a_168_ = stack[2].m_obj;
lean_object* v_a_169_ = stack[3].m_obj;
lean_object* v_a_170_ = stack[4].m_obj;
lean_object* v_a_171_ = stack[5].m_obj;
lean_object* v_res_202_;
v_res_202_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst(v_inst_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
stack->m_obj
 = v_res_202_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___boxed(lean_object* v_inst_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst(v_inst_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec_ref(v_a_204_);
return v_res_210_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst(lean_object* v_inst_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_u_227_; lean_object* v_type_228_; lean_object* v_semiringInst_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_u_227_ = lean_ctor_get(v_a_221_, 0);
v_type_228_ = lean_ctor_get(v_a_221_, 1);
v_semiringInst_229_ = lean_ctor_get(v_a_221_, 5);
v___x_230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__1));
v___x_231_ = lean_box(0);
lean_inc(v_u_227_);
v___x_232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_232_, 0, v_u_227_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
lean_inc_ref(v___x_232_);
v___x_233_ = l_Lean_mkConst(v___x_230_, v___x_232_);
v___x_234_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3));
v___x_235_ = l_Lean_mkConst(v___x_234_, v___x_232_);
lean_inc_ref(v_semiringInst_229_);
lean_inc_ref_n(v_type_228_, 2);
v___x_236_ = l_Lean_mkAppB(v___x_235_, v_type_228_, v_semiringInst_229_);
v___x_237_ = l_Lean_mkAppB(v___x_233_, v_type_228_, v___x_236_);
v___x_238_ = l_Lean_Meta_isDefEqI(v_inst_220_, v___x_237_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_247_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_247_ == 0)
{
v___x_241_ = v___x_238_;
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_247_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_243_, 0, v_a_239_);
if (v_isShared_242_ == 0)
{
lean_ctor_set(v___x_241_, 0, v___x_243_);
v___x_245_ = v___x_241_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
else
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
v_a_248_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___x_238_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_238_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_220_ = stack[0].m_obj;
lean_object* v_a_221_ = stack[1].m_obj;
lean_object* v_a_222_ = stack[2].m_obj;
lean_object* v_a_223_ = stack[3].m_obj;
lean_object* v_a_224_ = stack[4].m_obj;
lean_object* v_a_225_ = stack[5].m_obj;
lean_object* v_res_256_;
v_res_256_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst(v_inst_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
stack->m_obj
 = v_res_256_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___boxed(lean_object* v_inst_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst(v_inst_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec_ref(v_a_258_);
return v_res_264_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst(lean_object* v_inst_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_u_281_; lean_object* v_type_282_; lean_object* v_ringInst_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_u_281_ = lean_ctor_get(v_a_275_, 0);
v_type_282_ = lean_ctor_get(v_a_275_, 1);
v_ringInst_283_ = lean_ctor_get(v_a_275_, 4);
v___x_284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__1));
v___x_285_ = lean_box(0);
lean_inc(v_u_281_);
v___x_286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_286_, 0, v_u_281_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
lean_inc_ref(v___x_286_);
v___x_287_ = l_Lean_mkConst(v___x_284_, v___x_286_);
v___x_288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3));
v___x_289_ = l_Lean_mkConst(v___x_288_, v___x_286_);
lean_inc_ref(v_ringInst_283_);
lean_inc_ref_n(v_type_282_, 2);
v___x_290_ = l_Lean_mkAppB(v___x_289_, v_type_282_, v_ringInst_283_);
v___x_291_ = l_Lean_mkAppB(v___x_287_, v_type_282_, v___x_290_);
v___x_292_ = l_Lean_Meta_isDefEqI(v_inst_274_, v___x_291_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_301_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_301_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_301_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_297_, 0, v_a_293_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_297_);
v___x_299_ = v___x_295_;
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
else
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
v_a_302_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_292_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_292_);
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_274_ = stack[0].m_obj;
lean_object* v_a_275_ = stack[1].m_obj;
lean_object* v_a_276_ = stack[2].m_obj;
lean_object* v_a_277_ = stack[3].m_obj;
lean_object* v_a_278_ = stack[4].m_obj;
lean_object* v_a_279_ = stack[5].m_obj;
lean_object* v_res_310_;
v_res_310_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst(v_inst_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
stack->m_obj
 = v_res_310_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___boxed(lean_object* v_inst_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst(v_inst_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
lean_dec_ref(v_a_312_);
return v_res_318_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst(lean_object* v_inst_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_u_335_; lean_object* v_type_336_; lean_object* v_fieldInst_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_u_335_ = lean_ctor_get(v_a_329_, 0);
v_type_336_ = lean_ctor_get(v_a_329_, 1);
v_fieldInst_337_ = lean_ctor_get(v_a_329_, 2);
v___x_338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__1));
v___x_339_ = lean_box(0);
lean_inc(v_u_335_);
v___x_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_340_, 0, v_u_335_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
lean_inc_ref(v___x_340_);
v___x_341_ = l_Lean_mkConst(v___x_338_, v___x_340_);
v___x_342_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3));
v___x_343_ = l_Lean_mkConst(v___x_342_, v___x_340_);
lean_inc_ref(v_fieldInst_337_);
lean_inc_ref_n(v_type_336_, 2);
v___x_344_ = l_Lean_mkAppB(v___x_343_, v_type_336_, v_fieldInst_337_);
v___x_345_ = l_Lean_mkAppB(v___x_341_, v_type_336_, v___x_344_);
v___x_346_ = l_Lean_Meta_isDefEqI(v_inst_328_, v___x_345_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_355_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_355_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_355_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_355_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_351_, 0, v_a_347_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v___x_351_);
v___x_353_ = v___x_349_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
v_a_356_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_346_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_346_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_328_ = stack[0].m_obj;
lean_object* v_a_329_ = stack[1].m_obj;
lean_object* v_a_330_ = stack[2].m_obj;
lean_object* v_a_331_ = stack[3].m_obj;
lean_object* v_a_332_ = stack[4].m_obj;
lean_object* v_a_333_ = stack[5].m_obj;
lean_object* v_res_364_;
v_res_364_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst(v_inst_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
stack->m_obj
 = v_res_364_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___boxed(lean_object* v_inst_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst(v_inst_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec_ref(v_a_366_);
return v_res_372_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst(lean_object* v_inst_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v_u_386_; lean_object* v_type_387_; lean_object* v_ringInst_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_u_386_ = lean_ctor_get(v_a_380_, 0);
v_type_387_ = lean_ctor_get(v_a_380_, 1);
v_ringInst_388_ = lean_ctor_get(v_a_380_, 4);
v___x_389_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1));
v___x_390_ = lean_box(0);
lean_inc(v_u_386_);
v___x_391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_391_, 0, v_u_386_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = l_Lean_mkConst(v___x_389_, v___x_391_);
lean_inc_ref(v_ringInst_388_);
lean_inc_ref(v_type_387_);
v___x_393_ = l_Lean_mkAppB(v___x_392_, v_type_387_, v_ringInst_388_);
v___x_394_ = l_Lean_Meta_isDefEqI(v_inst_379_, v___x_393_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_403_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_403_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_403_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_399_, 0, v_a_395_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_399_);
v___x_401_ = v___x_397_;
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
}
else
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
v_a_404_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_411_ == 0)
{
v___x_406_ = v___x_394_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_394_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_404_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_379_ = stack[0].m_obj;
lean_object* v_a_380_ = stack[1].m_obj;
lean_object* v_a_381_ = stack[2].m_obj;
lean_object* v_a_382_ = stack[3].m_obj;
lean_object* v_a_383_ = stack[4].m_obj;
lean_object* v_a_384_ = stack[5].m_obj;
lean_object* v_res_412_;
v_res_412_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst(v_inst_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
stack->m_obj
 = v_res_412_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___boxed(lean_object* v_inst_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst(v_inst_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec_ref(v_a_414_);
return v_res_420_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst(lean_object* v_inst_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_u_434_; lean_object* v_type_435_; lean_object* v_fieldInst_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_u_434_ = lean_ctor_get(v_a_428_, 0);
v_type_435_ = lean_ctor_get(v_a_428_, 1);
v_fieldInst_436_ = lean_ctor_get(v_a_428_, 2);
v___x_437_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1));
v___x_438_ = lean_box(0);
lean_inc(v_u_434_);
v___x_439_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_439_, 0, v_u_434_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = l_Lean_mkConst(v___x_437_, v___x_439_);
lean_inc_ref(v_fieldInst_436_);
lean_inc_ref(v_type_435_);
v___x_441_ = l_Lean_mkAppB(v___x_440_, v_type_435_, v_fieldInst_436_);
v___x_442_ = l_Lean_Meta_isDefEqI(v_inst_427_, v___x_441_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_451_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_451_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_451_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_451_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_447_, 0, v_a_443_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_447_);
v___x_449_ = v___x_445_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
v_a_452_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_442_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_442_);
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_427_ = stack[0].m_obj;
lean_object* v_a_428_ = stack[1].m_obj;
lean_object* v_a_429_ = stack[2].m_obj;
lean_object* v_a_430_ = stack[3].m_obj;
lean_object* v_a_431_ = stack[4].m_obj;
lean_object* v_a_432_ = stack[5].m_obj;
lean_object* v_res_460_;
v_res_460_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst(v_inst_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_);
stack->m_obj
 = v_res_460_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___boxed(lean_object* v_inst_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst(v_inst_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec_ref(v_a_462_);
return v_res_468_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst(lean_object* v_inst_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_u_482_; lean_object* v_type_483_; lean_object* v_semiringInst_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_u_482_ = lean_ctor_get(v_a_476_, 0);
v_type_483_ = lean_ctor_get(v_a_476_, 1);
v_semiringInst_484_ = lean_ctor_get(v_a_476_, 5);
v___x_485_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1));
v___x_486_ = lean_box(0);
lean_inc(v_u_482_);
v___x_487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_487_, 0, v_u_482_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = l_Lean_mkConst(v___x_485_, v___x_487_);
lean_inc_ref(v_semiringInst_484_);
lean_inc_ref(v_type_483_);
v___x_489_ = l_Lean_mkAppB(v___x_488_, v_type_483_, v_semiringInst_484_);
v___x_490_ = l_Lean_Meta_isDefEqI(v_inst_475_, v___x_489_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_499_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_499_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_499_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_499_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v_a_491_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_495_);
v___x_497_ = v___x_493_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
v_a_500_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_490_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_490_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_475_ = stack[0].m_obj;
lean_object* v_a_476_ = stack[1].m_obj;
lean_object* v_a_477_ = stack[2].m_obj;
lean_object* v_a_478_ = stack[3].m_obj;
lean_object* v_a_479_ = stack[4].m_obj;
lean_object* v_a_480_ = stack[5].m_obj;
lean_object* v_res_508_;
v_res_508_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst(v_inst_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
stack->m_obj
 = v_res_508_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___boxed(lean_object* v_inst_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst(v_inst_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
lean_dec_ref(v_a_510_);
return v_res_516_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst(lean_object* v_inst_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
lean_object* v_u_530_; lean_object* v_type_531_; lean_object* v_fieldInst_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_u_530_ = lean_ctor_get(v_a_524_, 0);
v_type_531_ = lean_ctor_get(v_a_524_, 1);
v_fieldInst_532_ = lean_ctor_get(v_a_524_, 2);
v___x_533_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1));
v___x_534_ = lean_box(0);
lean_inc(v_u_530_);
v___x_535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_535_, 0, v_u_530_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = l_Lean_mkConst(v___x_533_, v___x_535_);
lean_inc_ref(v_fieldInst_532_);
lean_inc_ref(v_type_531_);
v___x_537_ = l_Lean_mkAppB(v___x_536_, v_type_531_, v_fieldInst_532_);
v___x_538_ = l_Lean_Meta_isDefEqI(v_inst_523_, v___x_537_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_547_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_547_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v_a_539_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 0, v___x_543_);
v___x_545_ = v___x_541_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
v_a_548_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_538_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_538_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_523_ = stack[0].m_obj;
lean_object* v_a_524_ = stack[1].m_obj;
lean_object* v_a_525_ = stack[2].m_obj;
lean_object* v_a_526_ = stack[3].m_obj;
lean_object* v_a_527_ = stack[4].m_obj;
lean_object* v_a_528_ = stack[5].m_obj;
lean_object* v_res_556_;
v_res_556_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst(v_inst_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
stack->m_obj
 = v_res_556_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___boxed(lean_object* v_inst_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst(v_inst_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec_ref(v_a_558_);
return v_res_564_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst(lean_object* v_inst_571_, lean_object* v_n_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_u_579_; lean_object* v_type_580_; lean_object* v_semiringInst_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v_u_579_ = lean_ctor_get(v_a_573_, 0);
v_type_580_ = lean_ctor_get(v_a_573_, 1);
v_semiringInst_581_ = lean_ctor_get(v_a_573_, 5);
v___x_582_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1));
v___x_583_ = lean_box(0);
lean_inc(v_u_579_);
v___x_584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_584_, 0, v_u_579_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = l_Lean_mkConst(v___x_582_, v___x_584_);
lean_inc_ref(v_semiringInst_581_);
lean_inc_ref(v_type_580_);
v___x_586_ = l_Lean_mkApp3(v___x_585_, v_type_580_, v_semiringInst_581_, v_n_572_);
v___x_587_ = l_Lean_Meta_isDefEqI(v_inst_571_, v___x_586_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_596_; 
v_a_588_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_596_ == 0)
{
v___x_590_ = v___x_587_;
v_isShared_591_ = v_isSharedCheck_596_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_596_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_592_, 0, v_a_588_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_592_);
v___x_594_ = v___x_590_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
v_a_597_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_587_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_587_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_571_ = stack[0].m_obj;
lean_object* v_n_572_ = stack[1].m_obj;
lean_object* v_a_573_ = stack[2].m_obj;
lean_object* v_a_574_ = stack[3].m_obj;
lean_object* v_a_575_ = stack[4].m_obj;
lean_object* v_a_576_ = stack[5].m_obj;
lean_object* v_a_577_ = stack[6].m_obj;
lean_object* v_res_605_;
v_res_605_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst(v_inst_571_, v_n_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_);
stack->m_obj
 = v_res_605_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___boxed(lean_object* v_inst_606_, lean_object* v_n_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst(v_inst_606_, v_n_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
lean_dec(v_a_612_);
lean_dec_ref(v_a_611_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
lean_dec_ref(v_a_608_);
return v_res_614_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg(lean_object* v_a_621_){
_start:
{
lean_object* v_u_623_; lean_object* v_type_624_; lean_object* v_semiringInst_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v_u_623_ = lean_ctor_get(v_a_621_, 0);
v_type_624_ = lean_ctor_get(v_a_621_, 1);
v_semiringInst_625_ = lean_ctor_get(v_a_621_, 5);
v___x_626_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1));
v___x_627_ = lean_box(0);
lean_inc(v_u_623_);
v___x_628_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_628_, 0, v_u_623_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = l_Lean_mkConst(v___x_626_, v___x_628_);
lean_inc_ref(v_semiringInst_625_);
lean_inc_ref(v_type_624_);
v___x_630_ = l_Lean_mkAppB(v___x_629_, v_type_624_, v_semiringInst_625_);
v___x_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
return v___x_632_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_621_ = stack[0].m_obj;
lean_object* v_res_633_;
v_res_633_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg(v_a_621_);
stack->m_obj
 = v_res_633_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___boxed(lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg(v_a_634_);
lean_dec_ref(v_a_634_);
return v_res_636_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst(lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg(v_a_637_);
return v___x_643_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_637_ = stack[0].m_obj;
lean_object* v_a_638_ = stack[1].m_obj;
lean_object* v_a_639_ = stack[2].m_obj;
lean_object* v_a_640_ = stack[3].m_obj;
lean_object* v_a_641_ = stack[4].m_obj;
lean_object* v_res_644_;
v_res_644_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst(v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
stack->m_obj
 = v_res_644_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___boxed(lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst(v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec_ref(v_a_645_);
return v_res_651_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNatCastInst(lean_object* v_inst_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v___x_659_; lean_object* v_a_660_; lean_object* v_val_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_685_; 
v___x_659_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg(v_a_653_);
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref(v___x_659_);
v_val_661_ = lean_ctor_get(v_a_660_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v_a_660_);
if (v_isSharedCheck_685_ == 0)
{
v___x_663_ = v_a_660_;
v_isShared_664_ = v_isSharedCheck_685_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_val_661_);
lean_dec(v_a_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_685_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_Meta_isDefEqI(v_inst_652_, v_val_661_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_676_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_676_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_676_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_676_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v_a_666_);
v___x_671_ = v___x_663_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_675_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_673_; 
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_671_);
v___x_673_ = v___x_668_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_671_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_del_object(v___x_663_);
v_a_677_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_665_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_665_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNatCastInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_652_ = stack[0].m_obj;
lean_object* v_a_653_ = stack[1].m_obj;
lean_object* v_a_654_ = stack[2].m_obj;
lean_object* v_a_655_ = stack[3].m_obj;
lean_object* v_a_656_ = stack[4].m_obj;
lean_object* v_a_657_ = stack[5].m_obj;
lean_object* v_res_686_;
v_res_686_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNatCastInst(v_inst_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
stack->m_obj
 = v_res_686_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNatCastInst___boxed(lean_object* v_inst_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNatCastInst(v_inst_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec_ref(v_a_688_);
return v_res_694_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast(lean_object* v_n_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_){
_start:
{
lean_object* v_r_707_; lean_object* v_u_710_; lean_object* v_type_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_u_710_ = lean_ctor_get(v_a_700_, 0);
v_type_711_ = lean_ctor_get(v_a_700_, 1);
v___x_712_ = l_Lean_mkNatLit(v_n_699_);
v___x_713_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1));
lean_inc_ref(v_type_711_);
v___x_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_714_, 0, v_type_711_);
v___x_715_ = lean_box(0);
lean_inc_ref(v___x_712_);
v___x_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_712_);
v___x_717_ = lean_unsigned_to_nat(3u);
v___x_718_ = lean_mk_empty_array_with_capacity(v___x_717_);
v___x_719_ = lean_array_push(v___x_718_, v___x_714_);
v___x_720_ = lean_array_push(v___x_719_, v___x_715_);
v___x_721_ = lean_array_push(v___x_720_, v___x_716_);
v___x_722_ = l_Lean_Meta_mkAppOptM(v___x_713_, v___x_721_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; 
lean_dec_ref(v___x_712_);
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v___x_722_, 1);
v_r_707_ = v_a_723_;
goto v___jp_706_;
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_742_; 
v_a_724_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_742_ == 0)
{
v___x_726_ = v___x_722_;
v_isShared_727_ = v_isSharedCheck_742_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_722_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_742_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
uint8_t v___y_729_; uint8_t v___x_740_; 
v___x_740_ = l_Lean_Exception_isInterrupt(v_a_724_);
if (v___x_740_ == 0)
{
uint8_t v___x_741_; 
lean_inc(v_a_724_);
v___x_741_ = l_Lean_Exception_isRuntime(v_a_724_);
v___y_729_ = v___x_741_;
goto v___jp_728_;
}
else
{
v___y_729_ = v___x_740_;
goto v___jp_728_;
}
v___jp_728_:
{
if (v___y_729_ == 0)
{
lean_object* v___x_730_; lean_object* v_a_731_; lean_object* v_val_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
lean_del_object(v___x_726_);
lean_dec(v_a_724_);
v___x_730_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg(v_a_700_);
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
lean_dec_ref(v___x_730_);
v_val_732_ = lean_ctor_get(v_a_731_, 0);
lean_inc(v_val_732_);
lean_dec(v_a_731_);
v___x_733_ = lean_box(0);
lean_inc(v_u_710_);
v___x_734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_734_, 0, v_u_710_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = l_Lean_mkConst(v___x_713_, v___x_734_);
lean_inc_ref(v_type_711_);
v___x_736_ = l_Lean_mkApp3(v___x_735_, v_type_711_, v_val_732_, v___x_712_);
v_r_707_ = v___x_736_;
goto v___jp_706_;
}
else
{
lean_object* v___x_738_; 
lean_dec_ref(v___x_712_);
if (v_isShared_727_ == 0)
{
v___x_738_ = v___x_726_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_724_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
v___jp_706_:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_708_, 0, v_r_707_);
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
return v___x_709_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_699_ = stack[0].m_obj;
lean_object* v_a_700_ = stack[1].m_obj;
lean_object* v_a_701_ = stack[2].m_obj;
lean_object* v_a_702_ = stack[3].m_obj;
lean_object* v_a_703_ = stack[4].m_obj;
lean_object* v_a_704_ = stack[5].m_obj;
lean_object* v_res_743_;
v_res_743_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast(v_n_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_);
stack->m_obj
 = v_res_743_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___boxed(lean_object* v_n_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast(v_n_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
lean_dec(v_a_749_);
lean_dec_ref(v_a_748_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
lean_dec_ref(v_a_745_);
return v_res_751_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(lean_object* v_a_758_){
_start:
{
lean_object* v_u_760_; lean_object* v_type_761_; lean_object* v_ringInst_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v_u_760_ = lean_ctor_get(v_a_758_, 0);
v_type_761_ = lean_ctor_get(v_a_758_, 1);
v_ringInst_762_ = lean_ctor_get(v_a_758_, 4);
v___x_763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1));
v___x_764_ = lean_box(0);
lean_inc(v_u_760_);
v___x_765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_765_, 0, v_u_760_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = l_Lean_mkConst(v___x_763_, v___x_765_);
lean_inc_ref(v_ringInst_762_);
lean_inc_ref(v_type_761_);
v___x_767_ = l_Lean_mkAppB(v___x_766_, v_type_761_, v_ringInst_762_);
v___x_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_758_ = stack[0].m_obj;
lean_object* v_res_770_;
v_res_770_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(v_a_758_);
stack->m_obj
 = v_res_770_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___boxed(lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(v_a_771_);
lean_dec_ref(v_a_771_);
return v_res_773_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst(lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(v_a_774_);
return v___x_780_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_774_ = stack[0].m_obj;
lean_object* v_a_775_ = stack[1].m_obj;
lean_object* v_a_776_ = stack[2].m_obj;
lean_object* v_a_777_ = stack[3].m_obj;
lean_object* v_a_778_ = stack[4].m_obj;
lean_object* v_res_781_;
v_res_781_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst(v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
stack->m_obj
 = v_res_781_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___boxed(lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst(v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec_ref(v_a_782_);
return v_res_788_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isIntCastInst(lean_object* v_inst_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___x_796_; lean_object* v_a_797_; lean_object* v_val_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_822_; 
v___x_796_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(v_a_790_);
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref(v___x_796_);
v_val_798_ = lean_ctor_get(v_a_797_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v_a_797_);
if (v_isSharedCheck_822_ == 0)
{
v___x_800_ = v_a_797_;
v_isShared_801_ = v_isSharedCheck_822_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_val_798_);
lean_dec(v_a_797_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_822_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_Meta_isDefEqI(v_inst_789_, v_val_798_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_813_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_813_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_813_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_813_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v_a_803_);
v___x_808_ = v___x_800_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_812_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_810_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_808_);
v___x_810_ = v___x_805_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_del_object(v___x_800_);
v_a_814_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_802_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_802_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isIntCastInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_789_ = stack[0].m_obj;
lean_object* v_a_790_ = stack[1].m_obj;
lean_object* v_a_791_ = stack[2].m_obj;
lean_object* v_a_792_ = stack[3].m_obj;
lean_object* v_a_793_ = stack[4].m_obj;
lean_object* v_a_794_ = stack[5].m_obj;
lean_object* v_res_823_;
v_res_823_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isIntCastInst(v_inst_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
stack->m_obj
 = v_res_823_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isIntCastInst___boxed(lean_object* v_inst_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isIntCastInst(v_inst_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
lean_dec_ref(v_a_825_);
return v_res_831_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast(lean_object* v_n_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_r_844_; lean_object* v_u_847_; lean_object* v_type_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v_u_847_ = lean_ctor_get(v_a_837_, 0);
v_type_848_ = lean_ctor_get(v_a_837_, 1);
v___x_849_ = l_Lean_mkIntLit(v_n_836_);
v___x_850_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1));
lean_inc_ref(v_type_848_);
v___x_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_851_, 0, v_type_848_);
v___x_852_ = lean_box(0);
lean_inc_ref(v___x_849_);
v___x_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_853_, 0, v___x_849_);
v___x_854_ = lean_unsigned_to_nat(3u);
v___x_855_ = lean_mk_empty_array_with_capacity(v___x_854_);
v___x_856_ = lean_array_push(v___x_855_, v___x_851_);
v___x_857_ = lean_array_push(v___x_856_, v___x_852_);
v___x_858_ = lean_array_push(v___x_857_, v___x_853_);
v___x_859_ = l_Lean_Meta_mkAppOptM(v___x_850_, v___x_858_, v_a_838_, v_a_839_, v_a_840_, v_a_841_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; 
lean_dec_ref(v___x_849_);
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v___x_859_, 1);
v_r_844_ = v_a_860_;
goto v___jp_843_;
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_879_; 
v_a_861_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_879_ == 0)
{
v___x_863_ = v___x_859_;
v_isShared_864_ = v_isSharedCheck_879_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_859_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_879_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
uint8_t v___y_866_; uint8_t v___x_877_; 
v___x_877_ = l_Lean_Exception_isInterrupt(v_a_861_);
if (v___x_877_ == 0)
{
uint8_t v___x_878_; 
lean_inc(v_a_861_);
v___x_878_ = l_Lean_Exception_isRuntime(v_a_861_);
v___y_866_ = v___x_878_;
goto v___jp_865_;
}
else
{
v___y_866_ = v___x_877_;
goto v___jp_865_;
}
v___jp_865_:
{
if (v___y_866_ == 0)
{
lean_object* v___x_867_; lean_object* v_a_868_; lean_object* v_val_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
lean_del_object(v___x_863_);
lean_dec(v_a_861_);
v___x_867_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(v_a_837_);
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref(v___x_867_);
v_val_869_ = lean_ctor_get(v_a_868_, 0);
lean_inc(v_val_869_);
lean_dec(v_a_868_);
v___x_870_ = lean_box(0);
lean_inc(v_u_847_);
v___x_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_871_, 0, v_u_847_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = l_Lean_mkConst(v___x_850_, v___x_871_);
lean_inc_ref(v_type_848_);
v___x_873_ = l_Lean_mkApp3(v___x_872_, v_type_848_, v_val_869_, v___x_849_);
v_r_844_ = v___x_873_;
goto v___jp_843_;
}
else
{
lean_object* v___x_875_; 
lean_dec_ref(v___x_849_);
if (v_isShared_864_ == 0)
{
v___x_875_ = v___x_863_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_861_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
v___jp_843_:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_845_, 0, v_r_844_);
v___x_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
return v___x_846_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_836_ = stack[0].m_obj;
lean_object* v_a_837_ = stack[1].m_obj;
lean_object* v_a_838_ = stack[2].m_obj;
lean_object* v_a_839_ = stack[3].m_obj;
lean_object* v_a_840_ = stack[4].m_obj;
lean_object* v_a_841_ = stack[5].m_obj;
lean_object* v_res_880_;
v_res_880_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast(v_n_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_);
stack->m_obj
 = v_res_880_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___boxed(lean_object* v_n_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast(v_n_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_n_881_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin_spec__0(lean_object* v_a_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = lean_nat_to_int(v_a_889_);
return v___x_890_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = l_Lean_Level_ofNat(v___x_896_);
return v___x_897_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = lean_box(0);
v___x_899_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3);
v___x_900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v___x_898_);
return v___x_900_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__5(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4);
v___x_902_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3);
v___x_903_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
lean_ctor_set(v___x_903_, 1, v___x_901_);
return v___x_903_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__6(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_904_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__5);
v___x_905_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3);
v___x_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
lean_ctor_set(v___x_906_, 1, v___x_904_);
return v___x_906_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_907_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__6);
v___x_908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2));
v___x_909_ = l_Lean_Expr_const___override(v___x_908_, v___x_907_);
return v___x_909_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_box(0);
v___x_914_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__9));
v___x_915_ = l_Lean_Expr_const___override(v___x_914_, v___x_913_);
return v___x_915_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__11(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4);
v___x_917_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__1));
v___x_918_ = l_Lean_Expr_const___override(v___x_917_, v___x_916_);
return v___x_918_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__14(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_923_ = lean_box(0);
v___x_924_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__13));
v___x_925_ = l_Lean_Expr_const___override(v___x_924_, v___x_923_);
return v___x_925_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_926_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__14, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__14);
v___x_927_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_928_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__11);
v___x_929_ = l_Lean_mkAppB(v___x_928_, v___x_927_, v___x_926_);
return v___x_929_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(lean_object* v_declName_930_, lean_object* v_a_931_, lean_object* v_b_932_, lean_object* v_r_u2081_933_, lean_object* v_r_u2082_934_, lean_object* v_op_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_fst_938_; lean_object* v_snd_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_1012_; 
v_fst_938_ = lean_ctor_get(v_r_u2081_933_, 0);
v_snd_939_ = lean_ctor_get(v_r_u2081_933_, 1);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_r_u2081_933_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_941_ = v_r_u2081_933_;
v_isShared_942_ = v_isSharedCheck_1012_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_snd_939_);
lean_inc(v_fst_938_);
lean_dec(v_r_u2081_933_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_1012_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v_fst_943_; lean_object* v_snd_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_1011_; 
v_fst_943_ = lean_ctor_get(v_r_u2082_934_, 0);
v_snd_944_ = lean_ctor_get(v_r_u2082_934_, 1);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_r_u2082_934_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_946_ = v_r_u2082_934_;
v_isShared_947_ = v_isSharedCheck_1011_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_snd_944_);
lean_inc(v_fst_943_);
lean_dec(v_r_u2082_934_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_1011_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v_u_948_; lean_object* v_type_949_; lean_object* v_fieldInst_950_; lean_object* v_isChar0Inst_951_; lean_object* v_num_952_; lean_object* v_den_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_957_; 
v_u_948_ = lean_ctor_get(v_a_936_, 0);
v_type_949_ = lean_ctor_get(v_a_936_, 1);
v_fieldInst_950_ = lean_ctor_get(v_a_936_, 2);
v_isChar0Inst_951_ = lean_ctor_get(v_a_936_, 3);
v_num_952_ = lean_ctor_get(v_fst_938_, 0);
lean_inc(v_num_952_);
v_den_953_ = lean_ctor_get(v_fst_938_, 1);
lean_inc(v_den_953_);
lean_inc(v_fst_943_);
v___x_954_ = lean_apply_2(v_op_935_, v_fst_938_, v_fst_943_);
v___x_955_ = lean_box(0);
lean_inc(v_u_948_);
if (v_isShared_942_ == 0)
{
lean_ctor_set_tag(v___x_941_, 1);
lean_ctor_set(v___x_941_, 1, v___x_955_);
lean_ctor_set(v___x_941_, 0, v_u_948_);
v___x_957_ = v___x_941_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_u_948_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v___x_955_);
v___x_957_ = v_reuseFailAlloc_1010_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
lean_object* v___x_958_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_987_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_958_ = l_Lean_mkConst(v_declName_930_, v___x_957_);
v___x_1000_ = lean_unsigned_to_nat(1u);
v___x_1001_ = lean_nat_dec_eq(v_den_953_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1002_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_1003_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_1004_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_1005_ = l_Lean_instToExprRat_mkInt(v_num_952_);
lean_dec(v_num_952_);
v___x_1006_ = lean_nat_to_int(v_den_953_);
v___x_1007_ = l_Lean_instToExprRat_mkInt(v___x_1006_);
lean_dec(v___x_1006_);
v___x_1008_ = l_Lean_mkApp6(v___x_1002_, v___x_1003_, v___x_1003_, v___x_1003_, v___x_1004_, v___x_1005_, v___x_1007_);
v___y_987_ = v___x_1008_;
goto v___jp_986_;
}
else
{
lean_object* v___x_1009_; 
lean_dec(v_den_953_);
v___x_1009_ = l_Lean_instToExprRat_mkInt(v_num_952_);
lean_dec(v_num_952_);
v___y_987_ = v___x_1009_;
goto v___jp_986_;
}
v___jp_959_:
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_967_; 
lean_inc_ref(v_isChar0Inst_951_);
lean_inc_ref(v_fieldInst_950_);
lean_inc_ref(v_type_949_);
v___x_963_ = l_Lean_mkApp8(v___x_958_, v_type_949_, v_fieldInst_950_, v_isChar0Inst_951_, v_a_931_, v_b_932_, v___y_961_, v___y_960_, v___y_962_);
v___x_964_ = l_Lean_eagerReflBoolTrue;
v___x_965_ = l_Lean_mkApp3(v___x_963_, v___x_964_, v_snd_939_, v_snd_944_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 1, v___x_965_);
lean_ctor_set(v___x_946_, 0, v___x_954_);
v___x_967_ = v___x_946_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_954_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v___x_965_);
v___x_967_ = v_reuseFailAlloc_970_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
v___x_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
return v___x_969_;
}
}
v___jp_971_:
{
lean_object* v_num_974_; lean_object* v_den_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v_num_974_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_num_974_);
v_den_975_ = lean_ctor_get(v___x_954_, 1);
lean_inc(v_den_975_);
v___x_976_ = lean_unsigned_to_nat(1u);
v___x_977_ = lean_nat_dec_eq(v_den_975_, v___x_976_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_978_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_979_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_980_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_981_ = l_Lean_instToExprRat_mkInt(v_num_974_);
lean_dec(v_num_974_);
v___x_982_ = lean_nat_to_int(v_den_975_);
v___x_983_ = l_Lean_instToExprRat_mkInt(v___x_982_);
lean_dec(v___x_982_);
v___x_984_ = l_Lean_mkApp6(v___x_978_, v___x_979_, v___x_979_, v___x_979_, v___x_980_, v___x_981_, v___x_983_);
v___y_960_ = v___y_973_;
v___y_961_ = v___y_972_;
v___y_962_ = v___x_984_;
goto v___jp_959_;
}
else
{
lean_object* v___x_985_; 
lean_dec(v_den_975_);
v___x_985_ = l_Lean_instToExprRat_mkInt(v_num_974_);
lean_dec(v_num_974_);
v___y_960_ = v___y_973_;
v___y_961_ = v___y_972_;
v___y_962_ = v___x_985_;
goto v___jp_959_;
}
}
v___jp_986_:
{
lean_object* v_num_988_; lean_object* v_den_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v_num_988_ = lean_ctor_get(v_fst_943_, 0);
lean_inc(v_num_988_);
v_den_989_ = lean_ctor_get(v_fst_943_, 1);
lean_inc(v_den_989_);
lean_dec(v_fst_943_);
v___x_990_ = lean_unsigned_to_nat(1u);
v___x_991_ = lean_nat_dec_eq(v_den_989_, v___x_990_);
if (v___x_991_ == 0)
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_992_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_993_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_994_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_995_ = l_Lean_instToExprRat_mkInt(v_num_988_);
lean_dec(v_num_988_);
v___x_996_ = lean_nat_to_int(v_den_989_);
v___x_997_ = l_Lean_instToExprRat_mkInt(v___x_996_);
lean_dec(v___x_996_);
v___x_998_ = l_Lean_mkApp6(v___x_992_, v___x_993_, v___x_993_, v___x_993_, v___x_994_, v___x_995_, v___x_997_);
v___y_972_ = v___y_987_;
v___y_973_ = v___x_998_;
goto v___jp_971_;
}
else
{
lean_object* v___x_999_; 
lean_dec(v_den_989_);
v___x_999_ = l_Lean_instToExprRat_mkInt(v_num_988_);
lean_dec(v_num_988_);
v___y_972_ = v___y_987_;
v___y_973_ = v___x_999_;
goto v___jp_971_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_930_ = stack[0].m_obj;
lean_object* v_a_931_ = stack[1].m_obj;
lean_object* v_b_932_ = stack[2].m_obj;
lean_object* v_r_u2081_933_ = stack[3].m_obj;
lean_object* v_r_u2082_934_ = stack[4].m_obj;
lean_object* v_op_935_ = stack[5].m_obj;
lean_object* v_a_936_ = stack[6].m_obj;
lean_object* v_res_1013_;
v_res_1013_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v_declName_930_, v_a_931_, v_b_932_, v_r_u2081_933_, v_r_u2082_934_, v_op_935_, v_a_936_);
stack->m_obj
 = v_res_1013_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___boxed(lean_object* v_declName_1014_, lean_object* v_a_1015_, lean_object* v_b_1016_, lean_object* v_r_u2081_1017_, lean_object* v_r_u2082_1018_, lean_object* v_op_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v_declName_1014_, v_a_1015_, v_b_1016_, v_r_u2081_1017_, v_r_u2082_1018_, v_op_1019_, v_a_1020_);
lean_dec_ref(v_a_1020_);
return v_res_1022_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin(lean_object* v_declName_1023_, lean_object* v_a_1024_, lean_object* v_b_1025_, lean_object* v_r_u2081_1026_, lean_object* v_r_u2082_1027_, lean_object* v_op_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v_declName_1023_, v_a_1024_, v_b_1025_, v_r_u2081_1026_, v_r_u2082_1027_, v_op_1028_, v_a_1029_);
return v___x_1035_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1023_ = stack[0].m_obj;
lean_object* v_a_1024_ = stack[1].m_obj;
lean_object* v_b_1025_ = stack[2].m_obj;
lean_object* v_r_u2081_1026_ = stack[3].m_obj;
lean_object* v_r_u2082_1027_ = stack[4].m_obj;
lean_object* v_op_1028_ = stack[5].m_obj;
lean_object* v_a_1029_ = stack[6].m_obj;
lean_object* v_a_1030_ = stack[7].m_obj;
lean_object* v_a_1031_ = stack[8].m_obj;
lean_object* v_a_1032_ = stack[9].m_obj;
lean_object* v_a_1033_ = stack[10].m_obj;
lean_object* v_res_1036_;
v_res_1036_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin(v_declName_1023_, v_a_1024_, v_b_1025_, v_r_u2081_1026_, v_r_u2082_1027_, v_op_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_);
stack->m_obj
 = v_res_1036_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___boxed(lean_object* v_declName_1037_, lean_object* v_a_1038_, lean_object* v_b_1039_, lean_object* v_r_u2081_1040_, lean_object* v_r_u2082_1041_, lean_object* v_op_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin(v_declName_1037_, v_a_1038_, v_b_1039_, v_r_u2081_1040_, v_r_u2082_1041_, v_op_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
lean_dec_ref(v_a_1043_);
return v_res_1049_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(lean_object* v_declName_1050_, lean_object* v_a_1051_, lean_object* v_r_1052_, lean_object* v_op_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_fst_1056_; lean_object* v_snd_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1104_; 
v_fst_1056_ = lean_ctor_get(v_r_1052_, 0);
v_snd_1057_ = lean_ctor_get(v_r_1052_, 1);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_r_1052_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1059_ = v_r_1052_;
v_isShared_1060_ = v_isSharedCheck_1104_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_snd_1057_);
lean_inc(v_fst_1056_);
lean_dec(v_r_1052_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1104_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v_u_1061_; lean_object* v_type_1062_; lean_object* v_fieldInst_1063_; lean_object* v_num_1064_; lean_object* v_den_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1081_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v_u_1061_ = lean_ctor_get(v_a_1054_, 0);
v_type_1062_ = lean_ctor_get(v_a_1054_, 1);
v_fieldInst_1063_ = lean_ctor_get(v_a_1054_, 2);
v_num_1064_ = lean_ctor_get(v_fst_1056_, 0);
lean_inc(v_num_1064_);
v_den_1065_ = lean_ctor_get(v_fst_1056_, 1);
lean_inc(v_den_1065_);
v___x_1066_ = lean_apply_1(v_op_1053_, v_fst_1056_);
v___x_1067_ = lean_box(0);
lean_inc(v_u_1061_);
v___x_1068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1068_, 0, v_u_1061_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = l_Lean_mkConst(v_declName_1050_, v___x_1068_);
v___x_1094_ = lean_unsigned_to_nat(1u);
v___x_1095_ = lean_nat_dec_eq(v_den_1065_, v___x_1094_);
if (v___x_1095_ == 0)
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1096_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_1097_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_1098_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_1099_ = l_Lean_instToExprRat_mkInt(v_num_1064_);
lean_dec(v_num_1064_);
v___x_1100_ = lean_nat_to_int(v_den_1065_);
v___x_1101_ = l_Lean_instToExprRat_mkInt(v___x_1100_);
lean_dec(v___x_1100_);
v___x_1102_ = l_Lean_mkApp6(v___x_1096_, v___x_1097_, v___x_1097_, v___x_1097_, v___x_1098_, v___x_1099_, v___x_1101_);
v___y_1081_ = v___x_1102_;
goto v___jp_1080_;
}
else
{
lean_object* v___x_1103_; 
lean_dec(v_den_1065_);
v___x_1103_ = l_Lean_instToExprRat_mkInt(v_num_1064_);
lean_dec(v_num_1064_);
v___y_1081_ = v___x_1103_;
goto v___jp_1080_;
}
v___jp_1070_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1073_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_fieldInst_1063_);
lean_inc_ref(v_type_1062_);
v___x_1074_ = l_Lean_mkApp7(v___x_1069_, v_type_1062_, v_fieldInst_1063_, v_a_1051_, v___y_1071_, v___y_1072_, v___x_1073_, v_snd_1057_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 1, v___x_1074_);
lean_ctor_set(v___x_1059_, 0, v___x_1066_);
v___x_1076_ = v___x_1059_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
}
v___jp_1080_:
{
lean_object* v_num_1082_; lean_object* v_den_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v_num_1082_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_num_1082_);
v_den_1083_ = lean_ctor_get(v___x_1066_, 1);
lean_inc(v_den_1083_);
v___x_1084_ = lean_unsigned_to_nat(1u);
v___x_1085_ = lean_nat_dec_eq(v_den_1083_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1086_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_1087_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_1088_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_1089_ = l_Lean_instToExprRat_mkInt(v_num_1082_);
lean_dec(v_num_1082_);
v___x_1090_ = lean_nat_to_int(v_den_1083_);
v___x_1091_ = l_Lean_instToExprRat_mkInt(v___x_1090_);
lean_dec(v___x_1090_);
v___x_1092_ = l_Lean_mkApp6(v___x_1086_, v___x_1087_, v___x_1087_, v___x_1087_, v___x_1088_, v___x_1089_, v___x_1091_);
v___y_1071_ = v___y_1081_;
v___y_1072_ = v___x_1092_;
goto v___jp_1070_;
}
else
{
lean_object* v___x_1093_; 
lean_dec(v_den_1083_);
v___x_1093_ = l_Lean_instToExprRat_mkInt(v_num_1082_);
lean_dec(v_num_1082_);
v___y_1071_ = v___y_1081_;
v___y_1072_ = v___x_1093_;
goto v___jp_1070_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1050_ = stack[0].m_obj;
lean_object* v_a_1051_ = stack[1].m_obj;
lean_object* v_r_1052_ = stack[2].m_obj;
lean_object* v_op_1053_ = stack[3].m_obj;
lean_object* v_a_1054_ = stack[4].m_obj;
lean_object* v_res_1105_;
v_res_1105_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(v_declName_1050_, v_a_1051_, v_r_1052_, v_op_1053_, v_a_1054_);
stack->m_obj
 = v_res_1105_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg___boxed(lean_object* v_declName_1106_, lean_object* v_a_1107_, lean_object* v_r_1108_, lean_object* v_op_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(v_declName_1106_, v_a_1107_, v_r_1108_, v_op_1109_, v_a_1110_);
lean_dec_ref(v_a_1110_);
return v_res_1112_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary(lean_object* v_declName_1113_, lean_object* v_a_1114_, lean_object* v_r_1115_, lean_object* v_op_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(v_declName_1113_, v_a_1114_, v_r_1115_, v_op_1116_, v_a_1117_);
return v___x_1123_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1113_ = stack[0].m_obj;
lean_object* v_a_1114_ = stack[1].m_obj;
lean_object* v_r_1115_ = stack[2].m_obj;
lean_object* v_op_1116_ = stack[3].m_obj;
lean_object* v_a_1117_ = stack[4].m_obj;
lean_object* v_a_1118_ = stack[5].m_obj;
lean_object* v_a_1119_ = stack[6].m_obj;
lean_object* v_a_1120_ = stack[7].m_obj;
lean_object* v_a_1121_ = stack[8].m_obj;
lean_object* v_res_1124_;
v_res_1124_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary(v_declName_1113_, v_a_1114_, v_r_1115_, v_op_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_);
stack->m_obj
 = v_res_1124_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___boxed(lean_object* v_declName_1125_, lean_object* v_a_1126_, lean_object* v_r_1127_, lean_object* v_op_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary(v_declName_1125_, v_a_1126_, v_r_1127_, v_op_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
lean_dec_ref(v_a_1129_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval_spec__1(lean_object* v_a_1136_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Rat_ofInt(v_a_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval_spec__0(lean_object* v_a_1138_){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_nat_to_int(v_a_1138_);
v___x_1140_ = l_Rat_ofInt(v___x_1139_);
return v___x_1140_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1217_ = lean_unsigned_to_nat(0u);
v___x_1218_ = lean_nat_to_int(v___x_1217_);
return v___x_1218_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38(void){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4);
v___x_1220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13));
v___x_1221_ = l_Lean_Expr_const___override(v___x_1220_, v___x_1219_);
return v___x_1221_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41(void){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1225_ = lean_box(0);
v___x_1226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__40));
v___x_1227_ = l_Lean_Expr_const___override(v___x_1226_, v___x_1225_);
return v___x_1227_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1232_ = lean_box(0);
v___x_1233_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__43));
v___x_1234_ = l_Lean_Expr_const___override(v___x_1233_, v___x_1232_);
return v___x_1234_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(lean_object* v_e_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v___f_1287_; lean_object* v___f_1288_; lean_object* v___f_1289_; lean_object* v___f_1290_; lean_object* v___f_1291_; lean_object* v___f_1292_; lean_object* v___x_1293_; 
v___f_1287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__0));
v___f_1288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__1));
v___f_1289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__2));
v___f_1290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__3));
v___f_1291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4));
v___f_1292_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__5));
v___x_1293_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1277_, v_a_1280_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1293_, 1);
v___x_1295_ = l_Lean_Expr_cleanupAnnotations(v_a_1294_);
v___x_1296_ = l_Lean_Expr_isApp(v___x_1295_);
if (v___x_1296_ == 0)
{
lean_dec_ref(v___x_1295_);
goto v___jp_1284_;
}
else
{
lean_object* v_arg_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v_arg_1297_ = lean_ctor_get(v___x_1295_, 1);
lean_inc_ref(v_arg_1297_);
v___x_1298_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1295_);
v___x_1299_ = l_Lean_Expr_isApp(v___x_1298_);
if (v___x_1299_ == 0)
{
lean_dec_ref(v___x_1298_);
lean_dec_ref(v_arg_1297_);
goto v___jp_1284_;
}
else
{
lean_object* v_arg_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v_arg_1300_ = lean_ctor_get(v___x_1298_, 1);
lean_inc_ref(v_arg_1300_);
v___x_1301_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1298_);
v___x_1302_ = l_Lean_Expr_isApp(v___x_1301_);
if (v___x_1302_ == 0)
{
lean_dec_ref(v___x_1301_);
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
goto v___jp_1284_;
}
else
{
lean_object* v_arg_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v_arg_1303_ = lean_ctor_get(v___x_1301_, 1);
lean_inc_ref(v_arg_1303_);
v___x_1304_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1301_);
v___x_1305_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1));
v___x_1306_ = l_Lean_Expr_isConstOf(v___x_1304_, v___x_1305_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1));
v___x_1308_ = l_Lean_Expr_isConstOf(v___x_1304_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1309_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7));
v___x_1310_ = l_Lean_Expr_isConstOf(v___x_1304_, v___x_1309_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; uint8_t v___x_1312_; 
v___x_1311_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10));
v___x_1312_ = l_Lean_Expr_isConstOf(v___x_1304_, v___x_1311_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1313_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13));
v___x_1314_ = l_Lean_Expr_isConstOf(v___x_1304_, v___x_1313_);
if (v___x_1314_ == 0)
{
uint8_t v___x_1315_; 
v___x_1315_ = l_Lean_Expr_isApp(v___x_1304_);
if (v___x_1315_ == 0)
{
lean_dec_ref(v___x_1304_);
lean_dec_ref(v_arg_1303_);
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
goto v___jp_1284_;
}
else
{
lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1316_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1304_);
v___x_1317_ = l_Lean_Expr_isApp(v___x_1316_);
if (v___x_1317_ == 0)
{
lean_dec_ref(v___x_1316_);
lean_dec_ref(v_arg_1303_);
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
goto v___jp_1284_;
}
else
{
lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1316_);
v___x_1319_ = l_Lean_Expr_isApp(v___x_1318_);
if (v___x_1319_ == 0)
{
lean_dec_ref(v___x_1318_);
lean_dec_ref(v_arg_1303_);
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
goto v___jp_1284_;
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1320_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1318_);
v___x_1321_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16));
v___x_1322_ = l_Lean_Expr_isConstOf(v___x_1320_, v___x_1321_);
if (v___x_1322_ == 0)
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2));
v___x_1324_ = l_Lean_Expr_isConstOf(v___x_1320_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19));
v___x_1326_ = l_Lean_Expr_isConstOf(v___x_1320_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__22));
v___x_1328_ = l_Lean_Expr_isConstOf(v___x_1320_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__25));
v___x_1330_ = l_Lean_Expr_isConstOf(v___x_1320_, v___x_1329_);
lean_dec_ref(v___x_1320_);
if (v___x_1330_ == 0)
{
lean_dec_ref(v_arg_1303_);
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
goto v___jp_1284_;
}
else
{
lean_object* v___x_1331_; 
v___x_1331_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst(v_arg_1303_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1354_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1354_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1354_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
if (lean_obj_tag(v_a_1332_) == 0)
{
lean_object* v___x_1336_; lean_object* v___x_1338_; 
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
v___x_1336_ = lean_box(0);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1336_);
v___x_1338_ = v___x_1334_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
else
{
lean_object* v_val_1340_; uint8_t v___x_1341_; 
v_val_1340_ = lean_ctor_get(v_a_1332_, 0);
lean_inc(v_val_1340_);
lean_dec_ref_known(v_a_1332_, 1);
v___x_1341_ = lean_unbox(v_val_1340_);
lean_dec(v_val_1340_);
if (v___x_1341_ == 0)
{
lean_object* v___x_1342_; lean_object* v___x_1344_; 
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
v___x_1342_ = lean_box(0);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v___x_1342_);
v___x_1344_ = v___x_1334_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
else
{
lean_object* v___x_1346_; 
lean_del_object(v___x_1334_);
lean_inc_ref(v_arg_1300_);
v___x_1346_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1300_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
if (lean_obj_tag(v_a_1347_) == 0)
{
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
return v___x_1346_;
}
else
{
lean_object* v_val_1348_; lean_object* v___x_1349_; 
lean_inc_ref(v_a_1347_);
lean_dec_ref_known(v___x_1346_, 1);
v_val_1348_ = lean_ctor_get(v_a_1347_, 0);
lean_inc(v_val_1348_);
lean_dec_ref_known(v_a_1347_, 1);
lean_inc_ref(v_arg_1297_);
v___x_1349_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1297_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
if (lean_obj_tag(v_a_1350_) == 0)
{
lean_dec(v_val_1348_);
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
return v___x_1349_;
}
else
{
lean_object* v_val_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
lean_inc_ref(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
v_val_1351_ = lean_ctor_get(v_a_1350_, 0);
lean_inc(v_val_1351_);
lean_dec_ref_known(v_a_1350_, 1);
v___x_1352_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28));
v___x_1353_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v___x_1352_, v_arg_1300_, v_arg_1297_, v_val_1348_, v_val_1351_, v___f_1292_, v_a_1278_);
return v___x_1353_;
}
}
else
{
lean_dec(v_val_1348_);
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
return v___x_1349_;
}
}
}
else
{
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
return v___x_1346_;
}
}
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
v_a_1355_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1331_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1331_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
else
{
lean_object* v___x_1363_; 
lean_dec_ref(v___x_1320_);
v___x_1363_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst(v_arg_1303_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1386_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1386_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1386_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
if (lean_obj_tag(v_a_1364_) == 0)
{
lean_object* v___x_1368_; lean_object* v___x_1370_; 
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
v___x_1368_ = lean_box(0);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1368_);
v___x_1370_ = v___x_1366_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
else
{
lean_object* v_val_1372_; uint8_t v___x_1373_; 
v_val_1372_ = lean_ctor_get(v_a_1364_, 0);
lean_inc(v_val_1372_);
lean_dec_ref_known(v_a_1364_, 1);
v___x_1373_ = lean_unbox(v_val_1372_);
lean_dec(v_val_1372_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
v___x_1374_ = lean_box(0);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1374_);
v___x_1376_ = v___x_1366_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
else
{
lean_object* v___x_1378_; 
lean_del_object(v___x_1366_);
lean_inc_ref(v_arg_1300_);
v___x_1378_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1300_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
if (lean_obj_tag(v_a_1379_) == 0)
{
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
return v___x_1378_;
}
else
{
lean_object* v_val_1380_; lean_object* v___x_1381_; 
lean_inc_ref(v_a_1379_);
lean_dec_ref_known(v___x_1378_, 1);
v_val_1380_ = lean_ctor_get(v_a_1379_, 0);
lean_inc(v_val_1380_);
lean_dec_ref_known(v_a_1379_, 1);
lean_inc_ref(v_arg_1297_);
v___x_1381_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1297_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
if (lean_obj_tag(v_a_1382_) == 0)
{
lean_dec(v_val_1380_);
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
return v___x_1381_;
}
else
{
lean_object* v_val_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_inc_ref(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
v_val_1383_ = lean_ctor_get(v_a_1382_, 0);
lean_inc(v_val_1383_);
lean_dec_ref_known(v_a_1382_, 1);
v___x_1384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30));
v___x_1385_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v___x_1384_, v_arg_1300_, v_arg_1297_, v_val_1380_, v_val_1383_, v___f_1291_, v_a_1278_);
return v___x_1385_;
}
}
else
{
lean_dec(v_val_1380_);
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
return v___x_1381_;
}
}
}
else
{
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
return v___x_1378_;
}
}
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
v_a_1387_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1363_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1363_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
else
{
lean_object* v___x_1395_; 
lean_dec_ref(v___x_1320_);
v___x_1395_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst(v_arg_1303_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1418_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1418_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1418_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
if (lean_obj_tag(v_a_1396_) == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
v___x_1400_ = lean_box(0);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___x_1400_);
v___x_1402_ = v___x_1398_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
else
{
lean_object* v_val_1404_; uint8_t v___x_1405_; 
v_val_1404_ = lean_ctor_get(v_a_1396_, 0);
lean_inc(v_val_1404_);
lean_dec_ref_known(v_a_1396_, 1);
v___x_1405_ = lean_unbox(v_val_1404_);
lean_dec(v_val_1404_);
if (v___x_1405_ == 0)
{
lean_object* v___x_1406_; lean_object* v___x_1408_; 
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
v___x_1406_ = lean_box(0);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___x_1406_);
v___x_1408_ = v___x_1398_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
else
{
lean_object* v___x_1410_; 
lean_del_object(v___x_1398_);
lean_inc_ref(v_arg_1300_);
v___x_1410_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1300_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
if (lean_obj_tag(v_a_1411_) == 0)
{
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
return v___x_1410_;
}
else
{
lean_object* v_val_1412_; lean_object* v___x_1413_; 
lean_inc_ref(v_a_1411_);
lean_dec_ref_known(v___x_1410_, 1);
v_val_1412_ = lean_ctor_get(v_a_1411_, 0);
lean_inc(v_val_1412_);
lean_dec_ref_known(v_a_1411_, 1);
lean_inc_ref(v_arg_1297_);
v___x_1413_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1297_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
if (lean_obj_tag(v_a_1414_) == 0)
{
lean_dec(v_val_1412_);
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
return v___x_1413_;
}
else
{
lean_object* v_val_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
lean_inc_ref(v_a_1414_);
lean_dec_ref_known(v___x_1413_, 1);
v_val_1415_ = lean_ctor_get(v_a_1414_, 0);
lean_inc(v_val_1415_);
lean_dec_ref_known(v_a_1414_, 1);
v___x_1416_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32));
v___x_1417_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v___x_1416_, v_arg_1300_, v_arg_1297_, v_val_1412_, v_val_1415_, v___f_1290_, v_a_1278_);
return v___x_1417_;
}
}
else
{
lean_dec(v_val_1412_);
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
return v___x_1413_;
}
}
}
else
{
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
return v___x_1410_;
}
}
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
v_a_1419_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1395_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1395_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
}
else
{
lean_object* v___x_1427_; 
lean_dec_ref(v___x_1320_);
v___x_1427_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst(v_arg_1303_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1450_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1450_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1450_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
if (lean_obj_tag(v_a_1428_) == 0)
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
v___x_1432_ = lean_box(0);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1432_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
else
{
lean_object* v_val_1436_; uint8_t v___x_1437_; 
v_val_1436_ = lean_ctor_get(v_a_1428_, 0);
lean_inc(v_val_1436_);
lean_dec_ref_known(v_a_1428_, 1);
v___x_1437_ = lean_unbox(v_val_1436_);
lean_dec(v_val_1436_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
v___x_1438_ = lean_box(0);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 0, v___x_1438_);
v___x_1440_ = v___x_1430_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
else
{
lean_object* v___x_1442_; 
lean_del_object(v___x_1430_);
lean_inc_ref(v_arg_1300_);
v___x_1442_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1300_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
if (lean_obj_tag(v_a_1443_) == 0)
{
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
return v___x_1442_;
}
else
{
lean_object* v_val_1444_; lean_object* v___x_1445_; 
lean_inc_ref(v_a_1443_);
lean_dec_ref_known(v___x_1442_, 1);
v_val_1444_ = lean_ctor_get(v_a_1443_, 0);
lean_inc(v_val_1444_);
lean_dec_ref_known(v_a_1443_, 1);
lean_inc_ref(v_arg_1297_);
v___x_1445_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1297_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
if (lean_obj_tag(v_a_1446_) == 0)
{
lean_dec(v_val_1444_);
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
return v___x_1445_;
}
else
{
lean_object* v_val_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_inc_ref(v_a_1446_);
lean_dec_ref_known(v___x_1445_, 1);
v_val_1447_ = lean_ctor_get(v_a_1446_, 0);
lean_inc(v_val_1447_);
lean_dec_ref_known(v_a_1446_, 1);
v___x_1448_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34));
v___x_1449_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v___x_1448_, v_arg_1300_, v_arg_1297_, v_val_1444_, v_val_1447_, v___f_1289_, v_a_1278_);
return v___x_1449_;
}
}
else
{
lean_dec(v_val_1444_);
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
return v___x_1445_;
}
}
}
else
{
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
return v___x_1442_;
}
}
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
v_a_1451_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1427_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1427_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
else
{
lean_object* v___x_1459_; 
lean_dec_ref(v___x_1320_);
lean_inc_ref(v_arg_1303_);
v___x_1459_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst(v_arg_1303_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1712_; 
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1462_ = v___x_1459_;
v_isShared_1463_ = v_isSharedCheck_1712_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1459_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1712_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
if (lean_obj_tag(v_a_1460_) == 0)
{
lean_object* v___x_1464_; lean_object* v___x_1466_; 
lean_dec_ref(v_arg_1303_);
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
v___x_1464_ = lean_box(0);
if (v_isShared_1463_ == 0)
{
lean_ctor_set(v___x_1462_, 0, v___x_1464_);
v___x_1466_ = v___x_1462_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
else
{
lean_object* v_val_1468_; uint8_t v___x_1469_; 
lean_del_object(v___x_1462_);
v_val_1468_ = lean_ctor_get(v_a_1460_, 0);
lean_inc(v_val_1468_);
lean_dec_ref_known(v_a_1460_, 1);
v___x_1469_ = lean_unbox(v_val_1468_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; 
v___x_1470_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst(v_arg_1303_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1602_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_1602_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1602_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
if (lean_obj_tag(v_a_1471_) == 0)
{
lean_object* v___x_1475_; lean_object* v___x_1477_; 
lean_dec(v_val_1468_);
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
v___x_1475_ = lean_box(0);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1475_);
v___x_1477_ = v___x_1473_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
else
{
lean_object* v_val_1479_; uint8_t v___x_1480_; 
v_val_1479_ = lean_ctor_get(v_a_1471_, 0);
lean_inc(v_val_1479_);
lean_dec_ref_known(v_a_1471_, 1);
v___x_1480_ = lean_unbox(v_val_1479_);
lean_dec(v_val_1479_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; lean_object* v___x_1483_; 
lean_dec(v_val_1468_);
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
v___x_1481_ = lean_box(0);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1481_);
v___x_1483_ = v___x_1473_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
else
{
lean_object* v___x_1485_; 
lean_del_object(v___x_1473_);
lean_inc_ref(v_arg_1300_);
v___x_1485_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1300_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
if (lean_obj_tag(v_a_1486_) == 0)
{
lean_dec(v_val_1468_);
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
return v___x_1485_;
}
else
{
lean_object* v_val_1487_; lean_object* v_fst_1488_; lean_object* v_snd_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1601_; 
lean_inc_ref(v_a_1486_);
lean_dec_ref_known(v___x_1485_, 1);
v_val_1487_ = lean_ctor_get(v_a_1486_, 0);
lean_inc(v_val_1487_);
lean_dec_ref_known(v_a_1486_, 1);
v_fst_1488_ = lean_ctor_get(v_val_1487_, 0);
v_snd_1489_ = lean_ctor_get(v_val_1487_, 1);
v_isSharedCheck_1601_ = !lean_is_exclusive(v_val_1487_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1491_ = v_val_1487_;
v_isShared_1492_ = v_isSharedCheck_1601_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_snd_1489_);
lean_inc(v_fst_1488_);
lean_dec(v_val_1487_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1601_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_Meta_getIntValue_x3f(v_arg_1297_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1592_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1592_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1592_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
if (lean_obj_tag(v_a_1494_) == 1)
{
lean_object* v_val_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1587_; 
lean_del_object(v___x_1496_);
v_val_1498_ = lean_ctor_get(v_a_1494_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_a_1494_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1500_ = v_a_1494_;
v_isShared_1501_ = v_isSharedCheck_1587_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_val_1498_);
lean_dec(v_a_1494_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1587_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; uint8_t v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = lean_nat_abs(v_val_1498_);
v___x_1503_ = lean_unbox(v_val_1468_);
lean_dec(v_val_1468_);
v___x_1504_ = l_Lean_checkExponent(v___x_1502_, v___x_1503_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1578_; 
v_a_1505_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1507_ = v___x_1504_;
v_isShared_1508_ = v_isSharedCheck_1578_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1504_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1578_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
uint8_t v___x_1509_; 
v___x_1509_ = lean_unbox(v_a_1505_);
lean_dec(v_a_1505_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; lean_object* v___x_1512_; 
lean_del_object(v___x_1500_);
lean_dec(v_val_1498_);
lean_del_object(v___x_1491_);
lean_dec(v_snd_1489_);
lean_dec(v_fst_1488_);
lean_dec_ref(v_arg_1300_);
v___x_1510_ = lean_box(0);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1510_);
v___x_1512_ = v___x_1507_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
else
{
lean_object* v_u_1514_; lean_object* v_type_1515_; lean_object* v_fieldInst_1516_; lean_object* v_isChar0Inst_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1554_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v_u_1514_ = lean_ctor_get(v_a_1278_, 0);
v_type_1515_ = lean_ctor_get(v_a_1278_, 1);
v_fieldInst_1516_ = lean_ctor_get(v_a_1278_, 2);
v_isChar0Inst_1517_ = lean_ctor_get(v_a_1278_, 3);
lean_inc(v_fst_1488_);
v___x_1518_ = l_Rat_zpow(v_fst_1488_, v_val_1498_);
v___x_1519_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36));
v___x_1520_ = lean_box(0);
lean_inc(v_u_1514_);
v___x_1521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1521_, 0, v_u_1514_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = l_Lean_mkConst(v___x_1519_, v___x_1521_);
v___x_1567_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37);
v___x_1568_ = lean_int_dec_le(v___x_1567_, v_val_1498_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1569_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38);
v___x_1570_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41);
v___x_1571_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44);
v___x_1572_ = lean_int_neg(v_val_1498_);
lean_dec(v_val_1498_);
v___x_1573_ = l_Int_toNat(v___x_1572_);
lean_dec(v___x_1572_);
v___x_1574_ = l_Lean_instToExprInt_mkNat(v___x_1573_);
v___x_1575_ = l_Lean_mkApp3(v___x_1569_, v___x_1570_, v___x_1571_, v___x_1574_);
v___y_1554_ = v___x_1575_;
goto v___jp_1553_;
}
else
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = l_Int_toNat(v_val_1498_);
lean_dec(v_val_1498_);
v___x_1577_ = l_Lean_instToExprInt_mkNat(v___x_1576_);
v___y_1554_ = v___x_1577_;
goto v___jp_1553_;
}
v___jp_1523_:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; 
v___x_1527_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_isChar0Inst_1517_);
lean_inc_ref(v_fieldInst_1516_);
lean_inc_ref(v_type_1515_);
v___x_1528_ = l_Lean_mkApp9(v___x_1522_, v_type_1515_, v_fieldInst_1516_, v_isChar0Inst_1517_, v_arg_1300_, v___y_1525_, v___y_1524_, v___y_1526_, v___x_1527_, v_snd_1489_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 1, v___x_1528_);
lean_ctor_set(v___x_1491_, 0, v___x_1518_);
v___x_1530_ = v___x_1491_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
lean_object* v___x_1532_; 
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v___x_1530_);
v___x_1532_ = v___x_1500_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1530_);
v___x_1532_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_object* v___x_1534_; 
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 0, v___x_1532_);
v___x_1534_ = v___x_1507_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
v___jp_1538_:
{
lean_object* v_num_1541_; lean_object* v_den_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v_num_1541_ = lean_ctor_get(v___x_1518_, 0);
v_den_1542_ = lean_ctor_get(v___x_1518_, 1);
v___x_1543_ = lean_unsigned_to_nat(1u);
v___x_1544_ = lean_nat_dec_eq(v_den_1542_, v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1545_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_1546_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_1547_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_1548_ = l_Lean_instToExprRat_mkInt(v_num_1541_);
lean_inc(v_den_1542_);
v___x_1549_ = lean_nat_to_int(v_den_1542_);
v___x_1550_ = l_Lean_instToExprRat_mkInt(v___x_1549_);
lean_dec(v___x_1549_);
v___x_1551_ = l_Lean_mkApp6(v___x_1545_, v___x_1546_, v___x_1546_, v___x_1546_, v___x_1547_, v___x_1548_, v___x_1550_);
v___y_1524_ = v___y_1540_;
v___y_1525_ = v___y_1539_;
v___y_1526_ = v___x_1551_;
goto v___jp_1523_;
}
else
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_instToExprRat_mkInt(v_num_1541_);
v___y_1524_ = v___y_1540_;
v___y_1525_ = v___y_1539_;
v___y_1526_ = v___x_1552_;
goto v___jp_1523_;
}
}
v___jp_1553_:
{
lean_object* v_num_1555_; lean_object* v_den_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v_num_1555_ = lean_ctor_get(v_fst_1488_, 0);
lean_inc(v_num_1555_);
v_den_1556_ = lean_ctor_get(v_fst_1488_, 1);
lean_inc(v_den_1556_);
lean_dec(v_fst_1488_);
v___x_1557_ = lean_unsigned_to_nat(1u);
v___x_1558_ = lean_nat_dec_eq(v_den_1556_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1559_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_1560_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_1561_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_1562_ = l_Lean_instToExprRat_mkInt(v_num_1555_);
lean_dec(v_num_1555_);
v___x_1563_ = lean_nat_to_int(v_den_1556_);
v___x_1564_ = l_Lean_instToExprRat_mkInt(v___x_1563_);
lean_dec(v___x_1563_);
v___x_1565_ = l_Lean_mkApp6(v___x_1559_, v___x_1560_, v___x_1560_, v___x_1560_, v___x_1561_, v___x_1562_, v___x_1564_);
v___y_1539_ = v___y_1554_;
v___y_1540_ = v___x_1565_;
goto v___jp_1538_;
}
else
{
lean_object* v___x_1566_; 
lean_dec(v_den_1556_);
v___x_1566_ = l_Lean_instToExprRat_mkInt(v_num_1555_);
lean_dec(v_num_1555_);
v___y_1539_ = v___y_1554_;
v___y_1540_ = v___x_1566_;
goto v___jp_1538_;
}
}
}
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_del_object(v___x_1500_);
lean_dec(v_val_1498_);
lean_del_object(v___x_1491_);
lean_dec(v_snd_1489_);
lean_dec(v_fst_1488_);
lean_dec_ref(v_arg_1300_);
v_a_1579_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1504_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1504_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1590_; 
lean_dec(v_a_1494_);
lean_del_object(v___x_1491_);
lean_dec(v_snd_1489_);
lean_dec(v_fst_1488_);
lean_dec(v_val_1468_);
lean_dec_ref(v_arg_1300_);
v___x_1588_ = lean_box(0);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v___x_1588_);
v___x_1590_ = v___x_1496_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_del_object(v___x_1491_);
lean_dec(v_snd_1489_);
lean_dec(v_fst_1488_);
lean_dec(v_val_1468_);
lean_dec_ref(v_arg_1300_);
v_a_1593_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1493_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1493_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
}
else
{
lean_dec(v_val_1468_);
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
return v___x_1485_;
}
}
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec(v_val_1468_);
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
v_a_1603_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1470_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1470_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
else
{
lean_object* v___x_1611_; 
lean_dec(v_val_1468_);
lean_dec_ref(v_arg_1303_);
lean_inc_ref(v_arg_1300_);
v___x_1611_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1300_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1611_) == 0)
{
lean_object* v_a_1612_; 
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
if (lean_obj_tag(v_a_1612_) == 0)
{
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
return v___x_1611_;
}
else
{
lean_object* v_val_1613_; lean_object* v_fst_1614_; lean_object* v_snd_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1711_; 
lean_inc_ref(v_a_1612_);
lean_dec_ref_known(v___x_1611_, 1);
v_val_1613_ = lean_ctor_get(v_a_1612_, 0);
lean_inc(v_val_1613_);
lean_dec_ref_known(v_a_1612_, 1);
v_fst_1614_ = lean_ctor_get(v_val_1613_, 0);
v_snd_1615_ = lean_ctor_get(v_val_1613_, 1);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_val_1613_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1617_ = v_val_1613_;
v_isShared_1618_ = v_isSharedCheck_1711_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_snd_1615_);
lean_inc(v_fst_1614_);
lean_dec(v_val_1613_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1711_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_Meta_getNatValue_x3f(v_arg_1297_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
lean_dec_ref(v_arg_1297_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1702_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1622_ = v___x_1619_;
v_isShared_1623_ = v_isSharedCheck_1702_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1619_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1702_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
if (lean_obj_tag(v_a_1620_) == 1)
{
lean_object* v_val_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1697_; 
lean_del_object(v___x_1622_);
v_val_1624_ = lean_ctor_get(v_a_1620_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v_a_1620_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1626_ = v_a_1620_;
v_isShared_1627_ = v_isSharedCheck_1697_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_val_1624_);
lean_dec(v_a_1620_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1697_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; 
lean_inc(v_val_1624_);
v___x_1628_ = l_Lean_checkExponent(v_val_1624_, v___x_1314_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1688_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1688_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1688_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
uint8_t v___x_1633_; 
v___x_1633_ = lean_unbox(v_a_1629_);
lean_dec(v_a_1629_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1636_; 
lean_del_object(v___x_1626_);
lean_dec(v_val_1624_);
lean_del_object(v___x_1617_);
lean_dec(v_snd_1615_);
lean_dec(v_fst_1614_);
lean_dec_ref(v_arg_1300_);
v___x_1634_ = lean_box(0);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1634_);
v___x_1636_ = v___x_1631_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
else
{
lean_object* v_u_1638_; lean_object* v_type_1639_; lean_object* v_fieldInst_1640_; lean_object* v_isChar0Inst_1641_; lean_object* v_num_1642_; lean_object* v_den_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___y_1651_; lean_object* v___y_1652_; lean_object* v___y_1665_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v_u_1638_ = lean_ctor_get(v_a_1278_, 0);
v_type_1639_ = lean_ctor_get(v_a_1278_, 1);
v_fieldInst_1640_ = lean_ctor_get(v_a_1278_, 2);
v_isChar0Inst_1641_ = lean_ctor_get(v_a_1278_, 3);
v_num_1642_ = lean_ctor_get(v_fst_1614_, 0);
lean_inc(v_num_1642_);
v_den_1643_ = lean_ctor_get(v_fst_1614_, 1);
lean_inc(v_den_1643_);
v___x_1644_ = l_Rat_pow(v_fst_1614_, v_val_1624_);
v___x_1645_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46));
v___x_1646_ = lean_box(0);
lean_inc(v_u_1638_);
v___x_1647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1647_, 0, v_u_1638_);
lean_ctor_set(v___x_1647_, 1, v___x_1646_);
v___x_1648_ = l_Lean_mkConst(v___x_1645_, v___x_1647_);
v___x_1649_ = l_Lean_mkNatLit(v_val_1624_);
v___x_1678_ = lean_unsigned_to_nat(1u);
v___x_1679_ = lean_nat_dec_eq(v_den_1643_, v___x_1678_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1680_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_1681_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_1682_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_1683_ = l_Lean_instToExprRat_mkInt(v_num_1642_);
lean_dec(v_num_1642_);
v___x_1684_ = lean_nat_to_int(v_den_1643_);
v___x_1685_ = l_Lean_instToExprRat_mkInt(v___x_1684_);
lean_dec(v___x_1684_);
v___x_1686_ = l_Lean_mkApp6(v___x_1680_, v___x_1681_, v___x_1681_, v___x_1681_, v___x_1682_, v___x_1683_, v___x_1685_);
v___y_1665_ = v___x_1686_;
goto v___jp_1664_;
}
else
{
lean_object* v___x_1687_; 
lean_dec(v_den_1643_);
v___x_1687_ = l_Lean_instToExprRat_mkInt(v_num_1642_);
lean_dec(v_num_1642_);
v___y_1665_ = v___x_1687_;
goto v___jp_1664_;
}
v___jp_1650_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1653_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_isChar0Inst_1641_);
lean_inc_ref(v_fieldInst_1640_);
lean_inc_ref(v_type_1639_);
v___x_1654_ = l_Lean_mkApp9(v___x_1648_, v_type_1639_, v_fieldInst_1640_, v_isChar0Inst_1641_, v_arg_1300_, v___x_1649_, v___y_1651_, v___y_1652_, v___x_1653_, v_snd_1615_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 1, v___x_1654_);
lean_ctor_set(v___x_1617_, 0, v___x_1644_);
v___x_1656_ = v___x_1617_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1644_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v___x_1654_);
v___x_1656_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1658_; 
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v___x_1656_);
v___x_1658_ = v___x_1626_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1660_; 
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1658_);
v___x_1660_ = v___x_1631_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
v___jp_1664_:
{
lean_object* v_num_1666_; lean_object* v_den_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v_num_1666_ = lean_ctor_get(v___x_1644_, 0);
v_den_1667_ = lean_ctor_get(v___x_1644_, 1);
v___x_1668_ = lean_unsigned_to_nat(1u);
v___x_1669_ = lean_nat_dec_eq(v_den_1667_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1670_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_1671_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_1672_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_1673_ = l_Lean_instToExprRat_mkInt(v_num_1666_);
lean_inc(v_den_1667_);
v___x_1674_ = lean_nat_to_int(v_den_1667_);
v___x_1675_ = l_Lean_instToExprRat_mkInt(v___x_1674_);
lean_dec(v___x_1674_);
v___x_1676_ = l_Lean_mkApp6(v___x_1670_, v___x_1671_, v___x_1671_, v___x_1671_, v___x_1672_, v___x_1673_, v___x_1675_);
v___y_1651_ = v___y_1665_;
v___y_1652_ = v___x_1676_;
goto v___jp_1650_;
}
else
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Lean_instToExprRat_mkInt(v_num_1666_);
v___y_1651_ = v___y_1665_;
v___y_1652_ = v___x_1677_;
goto v___jp_1650_;
}
}
}
}
}
else
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1696_; 
lean_del_object(v___x_1626_);
lean_dec(v_val_1624_);
lean_del_object(v___x_1617_);
lean_dec(v_snd_1615_);
lean_dec(v_fst_1614_);
lean_dec_ref(v_arg_1300_);
v_a_1689_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1691_ = v___x_1628_;
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1628_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1696_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1694_; 
if (v_isShared_1692_ == 0)
{
v___x_1694_ = v___x_1691_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_a_1689_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
else
{
lean_object* v___x_1698_; lean_object* v___x_1700_; 
lean_dec(v_a_1620_);
lean_del_object(v___x_1617_);
lean_dec(v_snd_1615_);
lean_dec(v_fst_1614_);
lean_dec_ref(v_arg_1300_);
v___x_1698_ = lean_box(0);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v___x_1698_);
v___x_1700_ = v___x_1622_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_del_object(v___x_1617_);
lean_dec(v_snd_1615_);
lean_dec(v_fst_1614_);
lean_dec_ref(v_arg_1300_);
v_a_1703_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1619_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1619_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
return v___x_1611_;
}
}
}
}
}
else
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1720_; 
lean_dec_ref(v_arg_1303_);
lean_dec_ref(v_arg_1300_);
lean_dec_ref(v_arg_1297_);
v_a_1713_ = lean_ctor_get(v___x_1459_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1715_ = v___x_1459_;
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1459_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1720_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_a_1713_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
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
lean_object* v___x_1721_; 
lean_dec_ref(v___x_1304_);
lean_dec_ref(v_arg_1303_);
v___x_1721_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst(v_arg_1300_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1741_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1724_ = v___x_1721_;
v_isShared_1725_ = v_isSharedCheck_1741_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_dec(v___x_1721_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1741_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
if (lean_obj_tag(v_a_1722_) == 0)
{
lean_object* v___x_1726_; lean_object* v___x_1728_; 
lean_dec_ref(v_arg_1297_);
v___x_1726_ = lean_box(0);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1726_);
v___x_1728_ = v___x_1724_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
else
{
lean_object* v_val_1730_; uint8_t v___x_1731_; 
v_val_1730_ = lean_ctor_get(v_a_1722_, 0);
lean_inc(v_val_1730_);
lean_dec_ref_known(v_a_1722_, 1);
v___x_1731_ = lean_unbox(v_val_1730_);
lean_dec(v_val_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1734_; 
lean_dec_ref(v_arg_1297_);
v___x_1732_ = lean_box(0);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1732_);
v___x_1734_ = v___x_1724_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1732_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
else
{
lean_object* v___x_1736_; 
lean_del_object(v___x_1724_);
lean_inc_ref(v_arg_1297_);
v___x_1736_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1297_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
if (lean_obj_tag(v_a_1737_) == 0)
{
lean_dec_ref(v_arg_1297_);
return v___x_1736_;
}
else
{
lean_object* v_val_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_inc_ref(v_a_1737_);
lean_dec_ref_known(v___x_1736_, 1);
v_val_1738_ = lean_ctor_get(v_a_1737_, 0);
lean_inc(v_val_1738_);
lean_dec_ref_known(v_a_1737_, 1);
v___x_1739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48));
v___x_1740_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(v___x_1739_, v_arg_1297_, v_val_1738_, v___f_1288_, v_a_1278_);
return v___x_1740_;
}
}
else
{
lean_dec_ref(v_arg_1297_);
return v___x_1736_;
}
}
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec_ref(v_arg_1297_);
v_a_1742_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1721_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1721_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
else
{
lean_object* v___x_1750_; 
lean_dec_ref(v___x_1304_);
lean_dec_ref(v_arg_1303_);
v___x_1750_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst(v_arg_1300_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1770_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1753_ = v___x_1750_;
v_isShared_1754_ = v_isSharedCheck_1770_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1750_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1770_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
if (lean_obj_tag(v_a_1751_) == 0)
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
lean_dec_ref(v_arg_1297_);
v___x_1755_ = lean_box(0);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1755_);
v___x_1757_ = v___x_1753_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1755_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
else
{
lean_object* v_val_1759_; uint8_t v___x_1760_; 
v_val_1759_ = lean_ctor_get(v_a_1751_, 0);
lean_inc(v_val_1759_);
lean_dec_ref_known(v_a_1751_, 1);
v___x_1760_ = lean_unbox(v_val_1759_);
lean_dec(v_val_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v___x_1763_; 
lean_dec_ref(v_arg_1297_);
v___x_1761_ = lean_box(0);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1761_);
v___x_1763_ = v___x_1753_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
else
{
lean_object* v___x_1765_; 
lean_del_object(v___x_1753_);
lean_inc_ref(v_arg_1297_);
v___x_1765_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1297_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
if (lean_obj_tag(v_a_1766_) == 0)
{
lean_dec_ref(v_arg_1297_);
return v___x_1765_;
}
else
{
lean_object* v_val_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_inc_ref(v_a_1766_);
lean_dec_ref_known(v___x_1765_, 1);
v_val_1767_ = lean_ctor_get(v_a_1766_, 0);
lean_inc(v_val_1767_);
lean_dec_ref_known(v_a_1766_, 1);
v___x_1768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50));
v___x_1769_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(v___x_1768_, v_arg_1297_, v_val_1767_, v___f_1287_, v_a_1278_);
return v___x_1769_;
}
}
else
{
lean_dec_ref(v_arg_1297_);
return v___x_1765_;
}
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec_ref(v_arg_1297_);
v_a_1771_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1750_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1750_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
else
{
lean_object* v___x_1779_; 
lean_dec_ref(v___x_1304_);
lean_dec_ref(v_arg_1303_);
lean_inc_ref(v_arg_1300_);
v___x_1779_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst(v_arg_1297_, v_arg_1300_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1834_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1782_ = v___x_1779_;
v_isShared_1783_ = v_isSharedCheck_1834_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1779_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1834_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
if (lean_obj_tag(v_a_1780_) == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1786_; 
lean_dec_ref(v_arg_1300_);
v___x_1784_ = lean_box(0);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 0, v___x_1784_);
v___x_1786_ = v___x_1782_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
else
{
lean_object* v_val_1788_; uint8_t v___x_1789_; 
v_val_1788_ = lean_ctor_get(v_a_1780_, 0);
lean_inc(v_val_1788_);
lean_dec_ref_known(v_a_1780_, 1);
v___x_1789_ = lean_unbox(v_val_1788_);
lean_dec(v_val_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; lean_object* v___x_1792_; 
lean_dec_ref(v_arg_1300_);
v___x_1790_ = lean_box(0);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 0, v___x_1790_);
v___x_1792_ = v___x_1782_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
else
{
lean_object* v___x_1794_; 
lean_del_object(v___x_1782_);
v___x_1794_ = l_Lean_Meta_getNatValue_x3f(v_arg_1300_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
lean_dec_ref(v_arg_1300_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1825_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1797_ = v___x_1794_;
v_isShared_1798_ = v_isSharedCheck_1825_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1794_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1825_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
if (lean_obj_tag(v_a_1795_) == 1)
{
lean_object* v_val_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1820_; 
v_val_1799_ = lean_ctor_get(v_a_1795_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_a_1795_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1801_ = v_a_1795_;
v_isShared_1802_ = v_isSharedCheck_1820_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_val_1799_);
lean_dec(v_a_1795_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1820_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v_u_1803_; lean_object* v_type_1804_; lean_object* v_fieldInst_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1815_; 
v_u_1803_ = lean_ctor_get(v_a_1278_, 0);
v_type_1804_ = lean_ctor_get(v_a_1278_, 1);
v_fieldInst_1805_ = lean_ctor_get(v_a_1278_, 2);
v___x_1806_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52));
v___x_1807_ = lean_box(0);
lean_inc(v_u_1803_);
v___x_1808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1808_, 0, v_u_1803_);
lean_ctor_set(v___x_1808_, 1, v___x_1807_);
v___x_1809_ = l_Lean_mkConst(v___x_1806_, v___x_1808_);
lean_inc(v_val_1799_);
v___x_1810_ = l_Lean_mkNatLit(v_val_1799_);
lean_inc_ref(v_fieldInst_1805_);
lean_inc_ref(v_type_1804_);
v___x_1811_ = l_Lean_mkApp3(v___x_1809_, v_type_1804_, v_fieldInst_1805_, v___x_1810_);
v___x_1812_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval_spec__0(v_val_1799_);
v___x_1813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
lean_ctor_set(v___x_1813_, 1, v___x_1811_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1813_);
v___x_1815_ = v___x_1801_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
lean_object* v___x_1817_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___x_1815_);
v___x_1817_ = v___x_1797_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1823_; 
lean_dec(v_a_1795_);
v___x_1821_ = lean_box(0);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 0, v___x_1821_);
v___x_1823_ = v___x_1797_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1821_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
v_a_1826_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1794_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1794_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_dec_ref(v_arg_1300_);
v_a_1835_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1779_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1779_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
}
else
{
lean_object* v___x_1843_; 
lean_dec_ref(v___x_1304_);
lean_dec_ref(v_arg_1303_);
v___x_1843_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNatCastInst(v_arg_1300_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1898_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1898_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1898_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
if (lean_obj_tag(v_a_1844_) == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1850_; 
lean_dec_ref(v_arg_1297_);
v___x_1848_ = lean_box(0);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1848_);
v___x_1850_ = v___x_1846_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
else
{
lean_object* v_val_1852_; uint8_t v___x_1853_; 
v_val_1852_ = lean_ctor_get(v_a_1844_, 0);
lean_inc(v_val_1852_);
lean_dec_ref_known(v_a_1844_, 1);
v___x_1853_ = lean_unbox(v_val_1852_);
lean_dec(v_val_1852_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
lean_dec_ref(v_arg_1297_);
v___x_1854_ = lean_box(0);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1854_);
v___x_1856_ = v___x_1846_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
else
{
lean_object* v___x_1858_; 
lean_del_object(v___x_1846_);
v___x_1858_ = l_Lean_Meta_getNatValue_x3f(v_arg_1297_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
lean_dec_ref(v_arg_1297_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1889_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1861_ = v___x_1858_;
v_isShared_1862_ = v_isSharedCheck_1889_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1858_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1889_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
if (lean_obj_tag(v_a_1859_) == 1)
{
lean_object* v_val_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1884_; 
v_val_1863_ = lean_ctor_get(v_a_1859_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v_a_1859_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1865_ = v_a_1859_;
v_isShared_1866_ = v_isSharedCheck_1884_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_val_1863_);
lean_dec(v_a_1859_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1884_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v_u_1867_; lean_object* v_type_1868_; lean_object* v_fieldInst_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1879_; 
v_u_1867_ = lean_ctor_get(v_a_1278_, 0);
v_type_1868_ = lean_ctor_get(v_a_1278_, 1);
v_fieldInst_1869_ = lean_ctor_get(v_a_1278_, 2);
v___x_1870_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54));
v___x_1871_ = lean_box(0);
lean_inc(v_u_1867_);
v___x_1872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1872_, 0, v_u_1867_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = l_Lean_mkConst(v___x_1870_, v___x_1872_);
lean_inc(v_val_1863_);
v___x_1874_ = l_Lean_mkNatLit(v_val_1863_);
lean_inc_ref(v_fieldInst_1869_);
lean_inc_ref(v_type_1868_);
v___x_1875_ = l_Lean_mkApp3(v___x_1873_, v_type_1868_, v_fieldInst_1869_, v___x_1874_);
v___x_1876_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval_spec__0(v_val_1863_);
v___x_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
lean_ctor_set(v___x_1877_, 1, v___x_1875_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1877_);
v___x_1879_ = v___x_1865_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1881_; 
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1879_);
v___x_1881_ = v___x_1861_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
else
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
lean_dec(v_a_1859_);
v___x_1885_ = lean_box(0);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 0, v___x_1885_);
v___x_1887_ = v___x_1861_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
v_a_1890_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1858_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1858_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec_ref(v_arg_1297_);
v_a_1899_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1843_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1843_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1904_; 
if (v_isShared_1902_ == 0)
{
v___x_1904_ = v___x_1901_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_a_1899_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
}
}
else
{
lean_object* v___x_1907_; 
lean_dec_ref(v___x_1304_);
lean_dec_ref(v_arg_1303_);
v___x_1907_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isIntCastInst(v_arg_1300_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1974_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1910_ = v___x_1907_;
v_isShared_1911_ = v_isSharedCheck_1974_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1907_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1974_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
if (lean_obj_tag(v_a_1908_) == 0)
{
lean_object* v___x_1912_; lean_object* v___x_1914_; 
lean_dec_ref(v_arg_1297_);
v___x_1912_ = lean_box(0);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v___x_1912_);
v___x_1914_ = v___x_1910_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
else
{
lean_object* v_val_1916_; uint8_t v___x_1917_; 
v_val_1916_ = lean_ctor_get(v_a_1908_, 0);
lean_inc(v_val_1916_);
lean_dec_ref_known(v_a_1908_, 1);
v___x_1917_ = lean_unbox(v_val_1916_);
lean_dec(v_val_1916_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; lean_object* v___x_1920_; 
lean_dec_ref(v_arg_1297_);
v___x_1918_ = lean_box(0);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v___x_1918_);
v___x_1920_ = v___x_1910_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
else
{
lean_object* v___x_1922_; 
lean_del_object(v___x_1910_);
v___x_1922_ = l_Lean_Meta_getIntValue_x3f(v_arg_1297_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1965_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1925_ = v___x_1922_;
v_isShared_1926_ = v_isSharedCheck_1965_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1922_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1965_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
if (lean_obj_tag(v_a_1923_) == 1)
{
lean_object* v_val_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1960_; 
v_val_1927_ = lean_ctor_get(v_a_1923_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_a_1923_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1929_ = v_a_1923_;
v_isShared_1930_ = v_isSharedCheck_1960_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_val_1927_);
lean_dec(v_a_1923_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1960_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v_u_1931_; lean_object* v_type_1932_; lean_object* v_fieldInst_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___y_1939_; lean_object* v___x_1949_; uint8_t v___x_1950_; 
v_u_1931_ = lean_ctor_get(v_a_1278_, 0);
v_type_1932_ = lean_ctor_get(v_a_1278_, 1);
v_fieldInst_1933_ = lean_ctor_get(v_a_1278_, 2);
v___x_1934_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56));
v___x_1935_ = lean_box(0);
lean_inc(v_u_1931_);
v___x_1936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1936_, 0, v_u_1931_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = l_Lean_mkConst(v___x_1934_, v___x_1936_);
v___x_1949_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37);
v___x_1950_ = lean_int_dec_le(v___x_1949_, v_val_1927_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1951_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38);
v___x_1952_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41);
v___x_1953_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44);
v___x_1954_ = lean_int_neg(v_val_1927_);
v___x_1955_ = l_Int_toNat(v___x_1954_);
lean_dec(v___x_1954_);
v___x_1956_ = l_Lean_instToExprInt_mkNat(v___x_1955_);
v___x_1957_ = l_Lean_mkApp3(v___x_1951_, v___x_1952_, v___x_1953_, v___x_1956_);
v___y_1939_ = v___x_1957_;
goto v___jp_1938_;
}
else
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = l_Int_toNat(v_val_1927_);
v___x_1959_ = l_Lean_instToExprInt_mkNat(v___x_1958_);
v___y_1939_ = v___x_1959_;
goto v___jp_1938_;
}
v___jp_1938_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1944_; 
lean_inc_ref(v_fieldInst_1933_);
lean_inc_ref(v_type_1932_);
v___x_1940_ = l_Lean_mkApp3(v___x_1937_, v_type_1932_, v_fieldInst_1933_, v___y_1939_);
v___x_1941_ = l_Rat_ofInt(v_val_1927_);
v___x_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
lean_ctor_set(v___x_1942_, 1, v___x_1940_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 0, v___x_1942_);
v___x_1944_ = v___x_1929_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1946_; 
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 0, v___x_1944_);
v___x_1946_ = v___x_1925_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1963_; 
lean_dec(v_a_1923_);
v___x_1961_ = lean_box(0);
if (v_isShared_1926_ == 0)
{
lean_ctor_set(v___x_1925_, 0, v___x_1961_);
v___x_1963_ = v___x_1925_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
v_a_1966_ = lean_ctor_get(v___x_1922_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1922_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1922_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1922_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_dec_ref(v_arg_1297_);
v_a_1975_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1907_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1907_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
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
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
v_a_1983_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1293_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1293_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
v___jp_1284_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = lean_box(0);
v___x_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
return v___x_1286_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1277_ = stack[0].m_obj;
lean_object* v_a_1278_ = stack[1].m_obj;
lean_object* v_a_1279_ = stack[2].m_obj;
lean_object* v_a_1280_ = stack[3].m_obj;
lean_object* v_a_1281_ = stack[4].m_obj;
lean_object* v_a_1282_ = stack[5].m_obj;
lean_object* v_res_1991_;
v_res_1991_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_e_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_);
stack->m_obj
 = v_res_1991_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___boxed(lean_object* v_e_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_e_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_);
lean_dec(v_a_1997_);
lean_dec_ref(v_a_1996_);
lean_dec(v_a_1995_);
lean_dec_ref(v_a_1994_);
lean_dec_ref(v_a_1993_);
return v_res_1999_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(lean_object* v_e_2000_){
_start:
{
lean_object* v_a_2002_; lean_object* v_b_2003_; lean_object* v___x_2006_; uint8_t v___x_2007_; 
v___x_2006_ = l_Lean_Expr_cleanupAnnotations(v_e_2000_);
v___x_2007_ = l_Lean_Expr_isApp(v___x_2006_);
if (v___x_2007_ == 0)
{
lean_dec_ref(v___x_2006_);
return v___x_2007_;
}
else
{
lean_object* v_arg_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; 
v_arg_2008_ = lean_ctor_get(v___x_2006_, 1);
lean_inc_ref(v_arg_2008_);
v___x_2009_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2006_);
v___x_2010_ = l_Lean_Expr_isApp(v___x_2009_);
if (v___x_2010_ == 0)
{
lean_dec_ref(v___x_2009_);
lean_dec_ref(v_arg_2008_);
return v___x_2010_;
}
else
{
lean_object* v_arg_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v_arg_2011_ = lean_ctor_get(v___x_2009_, 1);
lean_inc_ref(v_arg_2011_);
v___x_2012_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2009_);
v___x_2013_ = l_Lean_Expr_isApp(v___x_2012_);
if (v___x_2013_ == 0)
{
lean_dec_ref(v___x_2012_);
lean_dec_ref(v_arg_2011_);
lean_dec_ref(v_arg_2008_);
return v___x_2013_;
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2014_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2012_);
v___x_2015_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1));
v___x_2016_ = l_Lean_Expr_isConstOf(v___x_2014_, v___x_2015_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1));
v___x_2018_ = l_Lean_Expr_isConstOf(v___x_2014_, v___x_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; uint8_t v___x_2020_; 
v___x_2019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7));
v___x_2020_ = l_Lean_Expr_isConstOf(v___x_2014_, v___x_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10));
v___x_2022_ = l_Lean_Expr_isConstOf(v___x_2014_, v___x_2021_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13));
v___x_2024_ = l_Lean_Expr_isConstOf(v___x_2014_, v___x_2023_);
if (v___x_2024_ == 0)
{
uint8_t v___x_2025_; 
v___x_2025_ = l_Lean_Expr_isApp(v___x_2014_);
if (v___x_2025_ == 0)
{
lean_dec_ref(v___x_2014_);
lean_dec_ref(v_arg_2011_);
lean_dec_ref(v_arg_2008_);
return v___x_2025_;
}
else
{
lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2026_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2014_);
v___x_2027_ = l_Lean_Expr_isApp(v___x_2026_);
if (v___x_2027_ == 0)
{
lean_dec_ref(v___x_2026_);
lean_dec_ref(v_arg_2011_);
lean_dec_ref(v_arg_2008_);
return v___x_2027_;
}
else
{
lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2028_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2026_);
v___x_2029_ = l_Lean_Expr_isApp(v___x_2028_);
if (v___x_2029_ == 0)
{
lean_dec_ref(v___x_2028_);
lean_dec_ref(v_arg_2011_);
lean_dec_ref(v_arg_2008_);
return v___x_2029_;
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; 
v___x_2030_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2028_);
v___x_2031_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16));
v___x_2032_ = l_Lean_Expr_isConstOf(v___x_2030_, v___x_2031_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2033_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2));
v___x_2034_ = l_Lean_Expr_isConstOf(v___x_2030_, v___x_2033_);
if (v___x_2034_ == 0)
{
lean_object* v___x_2035_; uint8_t v___x_2036_; 
v___x_2035_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19));
v___x_2036_ = l_Lean_Expr_isConstOf(v___x_2030_, v___x_2035_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__22));
v___x_2038_ = l_Lean_Expr_isConstOf(v___x_2030_, v___x_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; uint8_t v___x_2040_; 
v___x_2039_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__25));
v___x_2040_ = l_Lean_Expr_isConstOf(v___x_2030_, v___x_2039_);
lean_dec_ref(v___x_2030_);
if (v___x_2040_ == 0)
{
lean_dec_ref(v_arg_2011_);
lean_dec_ref(v_arg_2008_);
return v___x_2040_;
}
else
{
v_a_2002_ = v_arg_2011_;
v_b_2003_ = v_arg_2008_;
goto v___jp_2001_;
}
}
else
{
lean_dec_ref(v___x_2030_);
v_a_2002_ = v_arg_2011_;
v_b_2003_ = v_arg_2008_;
goto v___jp_2001_;
}
}
else
{
lean_dec_ref(v___x_2030_);
v_a_2002_ = v_arg_2011_;
v_b_2003_ = v_arg_2008_;
goto v___jp_2001_;
}
}
else
{
lean_dec_ref(v___x_2030_);
v_a_2002_ = v_arg_2011_;
v_b_2003_ = v_arg_2008_;
goto v___jp_2001_;
}
}
else
{
lean_dec_ref(v___x_2030_);
v_a_2002_ = v_arg_2011_;
v_b_2003_ = v_arg_2008_;
goto v___jp_2001_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2014_);
lean_dec_ref(v_arg_2011_);
v_e_2000_ = v_arg_2008_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_2014_);
lean_dec_ref(v_arg_2011_);
v_e_2000_ = v_arg_2008_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_2014_);
lean_dec_ref(v_arg_2011_);
lean_dec_ref(v_arg_2008_);
return v___x_2020_;
}
}
else
{
lean_dec_ref(v___x_2014_);
lean_dec_ref(v_arg_2011_);
lean_dec_ref(v_arg_2008_);
return v___x_2018_;
}
}
else
{
lean_dec_ref(v___x_2014_);
lean_dec_ref(v_arg_2011_);
lean_dec_ref(v_arg_2008_);
return v___x_2016_;
}
}
}
}
v___jp_2001_:
{
uint8_t v___x_2004_; 
v___x_2004_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(v_a_2002_);
if (v___x_2004_ == 0)
{
lean_dec_ref(v_b_2003_);
return v___x_2004_;
}
else
{
v_e_2000_ = v_b_2003_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2000_ = stack[0].m_obj;
uint8_t v_res_2043_;
v_res_2043_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(v_e_2000_);
stack->m_num = v_res_2043_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable___boxed(lean_object* v_e_2044_){
_start:
{
uint8_t v_res_2045_; lean_object* v_r_2046_; 
v_res_2045_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(v_e_2044_);
v_r_2046_ = lean_box(v_res_2045_);
return v_r_2046_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_evalFieldExpr_x3f(lean_object* v_e_2047_, lean_object* v_type_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
uint8_t v___x_2054_; 
lean_inc_ref(v_e_2047_);
v___x_2054_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(v_e_2047_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
lean_dec_ref(v_type_2048_);
lean_dec_ref(v_e_2047_);
v___x_2055_ = lean_box(0);
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
return v___x_2056_;
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___boxed), 7, 1);
lean_closure_set(v___x_2057_, 0, v_e_2047_);
v___x_2058_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg(v_type_2048_, v___x_2057_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_);
return v___x_2058_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_evalFieldExpr_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2047_ = stack[0].m_obj;
lean_object* v_type_2048_ = stack[1].m_obj;
lean_object* v_a_2049_ = stack[2].m_obj;
lean_object* v_a_2050_ = stack[3].m_obj;
lean_object* v_a_2051_ = stack[4].m_obj;
lean_object* v_a_2052_ = stack[5].m_obj;
lean_object* v_res_2059_;
v_res_2059_ = l_Lean_Meta_Grind_Arith_evalFieldExpr_x3f(v_e_2047_, v_type_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_);
stack->m_obj
 = v_res_2059_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalFieldExpr_x3f___boxed(lean_object* v_e_2060_, lean_object* v_type_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Lean_Meta_Grind_Arith_evalFieldExpr_x3f(v_e_2060_, v_type_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
lean_dec(v_a_2063_);
lean_dec_ref(v_a_2062_);
return v_res_2067_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = lean_unsigned_to_nat(1u);
v___x_2069_ = lean_nat_to_int(v___x_2068_);
return v___x_2069_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0(lean_object* v_e_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2098_; 
lean_inc_ref(v_e_2091_);
v___x_2098_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_e_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2348_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2348_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2348_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
if (lean_obj_tag(v_a_2099_) == 0)
{
lean_object* v___x_2103_; lean_object* v___x_2105_; 
lean_dec_ref(v_e_2091_);
v___x_2103_ = lean_box(0);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2103_);
v___x_2105_ = v___x_2101_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
else
{
lean_object* v_val_2107_; lean_object* v_fst_2108_; lean_object* v_snd_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2347_; 
lean_del_object(v___x_2101_);
v_val_2107_ = lean_ctor_get(v_a_2099_, 0);
lean_inc(v_val_2107_);
lean_dec_ref_known(v_a_2099_, 1);
v_fst_2108_ = lean_ctor_get(v_val_2107_, 0);
v_snd_2109_ = lean_ctor_get(v_val_2107_, 1);
v_isSharedCheck_2347_ = !lean_is_exclusive(v_val_2107_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2111_ = v_val_2107_;
v_isShared_2112_ = v_isSharedCheck_2347_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_snd_2109_);
lean_inc(v_fst_2108_);
lean_dec(v_val_2107_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2347_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v_num_2113_; lean_object* v_den_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2346_; 
v_num_2113_ = lean_ctor_get(v_fst_2108_, 0);
v_den_2114_ = lean_ctor_get(v_fst_2108_, 1);
v_isSharedCheck_2346_ = !lean_is_exclusive(v_fst_2108_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2116_ = v_fst_2108_;
v_isShared_2117_ = v_isSharedCheck_2346_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_den_2114_);
lean_inc(v_num_2113_);
lean_dec(v_fst_2108_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2346_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2118_; uint8_t v___x_2119_; 
v___x_2118_ = lean_unsigned_to_nat(1u);
v___x_2119_ = lean_nat_dec_eq(v_den_2114_, v___x_2118_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; uint8_t v___x_2121_; 
v___x_2120_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__0);
v___x_2121_ = lean_int_dec_eq(v_num_2113_, v___x_2120_);
if (v___x_2121_ == 0)
{
lean_object* v___x_2122_; 
v___x_2122_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast(v_num_2113_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v_val_2124_; lean_object* v___x_2125_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v_val_2124_ = lean_ctor_get(v_a_2123_, 0);
lean_inc(v_val_2124_);
lean_dec(v_a_2123_);
lean_inc(v_den_2114_);
v___x_2125_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast(v_den_2114_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v_val_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2203_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
v_val_2127_ = lean_ctor_get(v_a_2126_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v_a_2126_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2129_ = v_a_2126_;
v_isShared_2130_ = v_isSharedCheck_2203_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_val_2127_);
lean_dec(v_a_2126_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2203_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10));
v___x_2132_ = lean_mk_empty_array_with_capacity(v___x_2118_);
v___x_2133_ = lean_array_push(v___x_2132_, v_val_2127_);
v___x_2134_ = l_Lean_Meta_mkAppM(v___x_2131_, v___x_2133_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2136_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v___x_2136_ = l_Lean_Meta_mkMul(v_val_2124_, v_a_2135_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2186_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2139_ = v___x_2136_;
v_isShared_2140_ = v_isSharedCheck_2186_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2136_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2186_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v_u_2141_; lean_object* v_type_2142_; lean_object* v_fieldInst_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2147_; 
v_u_2141_ = lean_ctor_get(v___y_2092_, 0);
v_type_2142_ = lean_ctor_get(v___y_2092_, 1);
v_fieldInst_2143_ = lean_ctor_get(v___y_2092_, 2);
v___x_2144_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2));
v___x_2145_ = lean_box(0);
lean_inc(v_u_2141_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set_tag(v___x_2116_, 1);
lean_ctor_set(v___x_2116_, 1, v___x_2145_);
lean_ctor_set(v___x_2116_, 0, v_u_2141_);
v___x_2147_ = v___x_2116_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_u_2141_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
lean_object* v___x_2148_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2165_; 
v___x_2148_ = l_Lean_mkConst(v___x_2144_, v___x_2147_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2177_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_2178_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_2179_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_2180_ = l_Lean_instToExprRat_mkInt(v_num_2113_);
lean_inc(v_den_2114_);
v___x_2181_ = lean_nat_to_int(v_den_2114_);
v___x_2182_ = l_Lean_instToExprRat_mkInt(v___x_2181_);
lean_dec(v___x_2181_);
v___x_2183_ = l_Lean_mkApp6(v___x_2177_, v___x_2178_, v___x_2178_, v___x_2178_, v___x_2179_, v___x_2180_, v___x_2182_);
v___y_2165_ = v___x_2183_;
goto v___jp_2164_;
}
else
{
lean_object* v___x_2184_; 
v___x_2184_ = l_Lean_instToExprRat_mkInt(v_num_2113_);
v___y_2165_ = v___x_2184_;
goto v___jp_2164_;
}
v___jp_2149_:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2152_ = l_Lean_mkNatLit(v_den_2114_);
v___x_2153_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_fieldInst_2143_);
lean_inc_ref(v_type_2142_);
v___x_2154_ = l_Lean_mkApp8(v___x_2148_, v_type_2142_, v_fieldInst_2143_, v_e_2091_, v___y_2150_, v___y_2151_, v___x_2152_, v___x_2153_, v_snd_2109_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 1, v___x_2154_);
lean_ctor_set(v___x_2111_, 0, v_a_2137_);
v___x_2156_ = v___x_2111_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2137_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2158_; 
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 0, v___x_2156_);
v___x_2158_ = v___x_2129_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2160_; 
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2158_);
v___x_2160_ = v___x_2139_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
v___jp_2164_:
{
lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2166_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37);
v___x_2167_ = lean_int_dec_le(v___x_2166_, v_num_2113_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2168_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38);
v___x_2169_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41);
v___x_2170_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44);
v___x_2171_ = lean_int_neg(v_num_2113_);
lean_dec(v_num_2113_);
v___x_2172_ = l_Int_toNat(v___x_2171_);
lean_dec(v___x_2171_);
v___x_2173_ = l_Lean_instToExprInt_mkNat(v___x_2172_);
v___x_2174_ = l_Lean_mkApp3(v___x_2168_, v___x_2169_, v___x_2170_, v___x_2173_);
v___y_2150_ = v___y_2165_;
v___y_2151_ = v___x_2174_;
goto v___jp_2149_;
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = l_Int_toNat(v_num_2113_);
lean_dec(v_num_2113_);
v___x_2176_ = l_Lean_instToExprInt_mkNat(v___x_2175_);
v___y_2150_ = v___y_2165_;
v___y_2151_ = v___x_2176_;
goto v___jp_2149_;
}
}
}
}
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_del_object(v___x_2129_);
lean_del_object(v___x_2116_);
lean_dec(v_den_2114_);
lean_dec(v_num_2113_);
lean_del_object(v___x_2111_);
lean_dec(v_snd_2109_);
lean_dec_ref(v_e_2091_);
v_a_2187_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2136_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2136_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
else
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
lean_del_object(v___x_2129_);
lean_dec(v_val_2124_);
lean_del_object(v___x_2116_);
lean_dec(v_den_2114_);
lean_dec(v_num_2113_);
lean_del_object(v___x_2111_);
lean_dec(v_snd_2109_);
lean_dec_ref(v_e_2091_);
v_a_2195_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2197_ = v___x_2134_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2134_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_a_2195_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec(v_val_2124_);
lean_del_object(v___x_2116_);
lean_dec(v_den_2114_);
lean_dec(v_num_2113_);
lean_del_object(v___x_2111_);
lean_dec(v_snd_2109_);
lean_dec_ref(v_e_2091_);
v_a_2204_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2125_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2125_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_del_object(v___x_2116_);
lean_dec(v_den_2114_);
lean_dec(v_num_2113_);
lean_del_object(v___x_2111_);
lean_dec(v_snd_2109_);
lean_dec_ref(v_e_2091_);
v_a_2212_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2122_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2122_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_object* v___x_2220_; 
lean_inc(v_den_2114_);
v___x_2220_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast(v_den_2114_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v_val_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2274_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
lean_dec_ref_known(v___x_2220_, 1);
v_val_2222_ = lean_ctor_get(v_a_2221_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v_a_2221_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2224_ = v_a_2221_;
v_isShared_2225_ = v_isSharedCheck_2274_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_val_2222_);
lean_dec(v_a_2221_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2274_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10));
v___x_2227_ = lean_mk_empty_array_with_capacity(v___x_2118_);
v___x_2228_ = lean_array_push(v___x_2227_, v_val_2222_);
v___x_2229_ = l_Lean_Meta_mkAppM(v___x_2226_, v___x_2228_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2265_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2265_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2265_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v_u_2234_; lean_object* v_type_2235_; lean_object* v_fieldInst_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2240_; 
v_u_2234_ = lean_ctor_get(v___y_2092_, 0);
v_type_2235_ = lean_ctor_get(v___y_2092_, 1);
v_fieldInst_2236_ = lean_ctor_get(v___y_2092_, 2);
v___x_2237_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4));
v___x_2238_ = lean_box(0);
lean_inc(v_u_2234_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set_tag(v___x_2116_, 1);
lean_ctor_set(v___x_2116_, 1, v___x_2238_);
lean_ctor_set(v___x_2116_, 0, v_u_2234_);
v___x_2240_ = v___x_2116_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_u_2234_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
lean_object* v___x_2241_; lean_object* v___y_2243_; 
v___x_2241_ = l_Lean_mkConst(v___x_2237_, v___x_2240_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2256_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_2257_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_2258_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_2259_ = l_Lean_instToExprRat_mkInt(v_num_2113_);
lean_dec(v_num_2113_);
lean_inc(v_den_2114_);
v___x_2260_ = lean_nat_to_int(v_den_2114_);
v___x_2261_ = l_Lean_instToExprRat_mkInt(v___x_2260_);
lean_dec(v___x_2260_);
v___x_2262_ = l_Lean_mkApp6(v___x_2256_, v___x_2257_, v___x_2257_, v___x_2257_, v___x_2258_, v___x_2259_, v___x_2261_);
v___y_2243_ = v___x_2262_;
goto v___jp_2242_;
}
else
{
lean_object* v___x_2263_; 
v___x_2263_ = l_Lean_instToExprRat_mkInt(v_num_2113_);
lean_dec(v_num_2113_);
v___y_2243_ = v___x_2263_;
goto v___jp_2242_;
}
v___jp_2242_:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2248_; 
v___x_2244_ = l_Lean_mkNatLit(v_den_2114_);
v___x_2245_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_fieldInst_2236_);
lean_inc_ref(v_type_2235_);
v___x_2246_ = l_Lean_mkApp7(v___x_2241_, v_type_2235_, v_fieldInst_2236_, v_e_2091_, v___y_2243_, v___x_2244_, v___x_2245_, v_snd_2109_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 1, v___x_2246_);
lean_ctor_set(v___x_2111_, 0, v_a_2230_);
v___x_2248_ = v___x_2111_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2230_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v___x_2246_);
v___x_2248_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
lean_object* v___x_2250_; 
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v___x_2248_);
v___x_2250_ = v___x_2224_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
lean_object* v___x_2252_; 
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v___x_2250_);
v___x_2252_ = v___x_2232_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v___x_2250_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
lean_del_object(v___x_2224_);
lean_del_object(v___x_2116_);
lean_dec(v_den_2114_);
lean_dec(v_num_2113_);
lean_del_object(v___x_2111_);
lean_dec(v_snd_2109_);
lean_dec_ref(v_e_2091_);
v_a_2266_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2229_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2229_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
lean_del_object(v___x_2116_);
lean_dec(v_den_2114_);
lean_dec(v_num_2113_);
lean_del_object(v___x_2111_);
lean_dec(v_snd_2109_);
lean_dec_ref(v_e_2091_);
v_a_2275_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2220_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2220_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
}
else
{
lean_object* v___x_2283_; 
v___x_2283_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast(v_num_2113_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2337_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2286_ = v___x_2283_;
v_isShared_2287_ = v_isSharedCheck_2337_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2283_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2337_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v_val_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2336_; 
v_val_2288_ = lean_ctor_get(v_a_2284_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_a_2284_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2290_ = v_a_2284_;
v_isShared_2291_ = v_isSharedCheck_2336_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_val_2288_);
lean_dec(v_a_2284_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2336_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v_u_2292_; lean_object* v_type_2293_; lean_object* v_fieldInst_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2298_; 
v_u_2292_ = lean_ctor_get(v___y_2092_, 0);
v_type_2293_ = lean_ctor_get(v___y_2092_, 1);
v_fieldInst_2294_ = lean_ctor_get(v___y_2092_, 2);
v___x_2295_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6));
v___x_2296_ = lean_box(0);
lean_inc(v_u_2292_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set_tag(v___x_2116_, 1);
lean_ctor_set(v___x_2116_, 1, v___x_2296_);
lean_ctor_set(v___x_2116_, 0, v_u_2292_);
v___x_2298_ = v___x_2116_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_u_2292_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v___x_2296_);
v___x_2298_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
lean_object* v___x_2299_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2315_; 
v___x_2299_ = l_Lean_mkConst(v___x_2295_, v___x_2298_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2327_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_2328_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_2329_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_2330_ = l_Lean_instToExprRat_mkInt(v_num_2113_);
v___x_2331_ = lean_nat_to_int(v_den_2114_);
v___x_2332_ = l_Lean_instToExprRat_mkInt(v___x_2331_);
lean_dec(v___x_2331_);
v___x_2333_ = l_Lean_mkApp6(v___x_2327_, v___x_2328_, v___x_2328_, v___x_2328_, v___x_2329_, v___x_2330_, v___x_2332_);
v___y_2315_ = v___x_2333_;
goto v___jp_2314_;
}
else
{
lean_object* v___x_2334_; 
lean_dec(v_den_2114_);
v___x_2334_ = l_Lean_instToExprRat_mkInt(v_num_2113_);
v___y_2315_ = v___x_2334_;
goto v___jp_2314_;
}
v___jp_2300_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2303_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_fieldInst_2294_);
lean_inc_ref(v_type_2293_);
v___x_2304_ = l_Lean_mkApp7(v___x_2299_, v_type_2293_, v_fieldInst_2294_, v_e_2091_, v___y_2301_, v___y_2302_, v___x_2303_, v_snd_2109_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 1, v___x_2304_);
lean_ctor_set(v___x_2111_, 0, v_val_2288_);
v___x_2306_ = v___x_2111_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_val_2288_);
lean_ctor_set(v_reuseFailAlloc_2313_, 1, v___x_2304_);
v___x_2306_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
lean_object* v___x_2308_; 
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v___x_2306_);
v___x_2308_ = v___x_2290_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2310_; 
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2308_);
v___x_2310_ = v___x_2286_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
v___jp_2314_:
{
lean_object* v___x_2316_; uint8_t v___x_2317_; 
v___x_2316_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37);
v___x_2317_ = lean_int_dec_le(v___x_2316_, v_num_2113_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2318_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38);
v___x_2319_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41);
v___x_2320_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44);
v___x_2321_ = lean_int_neg(v_num_2113_);
lean_dec(v_num_2113_);
v___x_2322_ = l_Int_toNat(v___x_2321_);
lean_dec(v___x_2321_);
v___x_2323_ = l_Lean_instToExprInt_mkNat(v___x_2322_);
v___x_2324_ = l_Lean_mkApp3(v___x_2318_, v___x_2319_, v___x_2320_, v___x_2323_);
v___y_2301_ = v___y_2315_;
v___y_2302_ = v___x_2324_;
goto v___jp_2300_;
}
else
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = l_Int_toNat(v_num_2113_);
lean_dec(v_num_2113_);
v___x_2326_ = l_Lean_instToExprInt_mkNat(v___x_2325_);
v___y_2301_ = v___y_2315_;
v___y_2302_ = v___x_2326_;
goto v___jp_2300_;
}
}
}
}
}
}
else
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_del_object(v___x_2116_);
lean_dec(v_den_2114_);
lean_dec(v_num_2113_);
lean_del_object(v___x_2111_);
lean_dec(v_snd_2109_);
lean_dec_ref(v_e_2091_);
v_a_2338_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2283_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2283_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_a_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
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
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec_ref(v_e_2091_);
v_a_2349_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2098_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2098_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2091_ = stack[0].m_obj;
lean_object* v___y_2092_ = stack[1].m_obj;
lean_object* v___y_2093_ = stack[2].m_obj;
lean_object* v___y_2094_ = stack[3].m_obj;
lean_object* v___y_2095_ = stack[4].m_obj;
lean_object* v___y_2096_ = stack[5].m_obj;
lean_object* v_res_2357_;
v_res_2357_ = l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0(v_e_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
stack->m_obj
 = v_res_2357_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___boxed(lean_object* v_e_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0(v_e_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec_ref(v___y_2359_);
return v_res_2365_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f(lean_object* v_e_2366_, lean_object* v_type_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_){
_start:
{
uint8_t v___x_2373_; 
lean_inc_ref(v_e_2366_);
v___x_2373_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(v_e_2366_);
if (v___x_2373_ == 0)
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
lean_dec_ref(v_type_2367_);
lean_dec_ref(v_e_2366_);
v___x_2374_ = lean_box(0);
v___x_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
return v___x_2375_;
}
else
{
lean_object* v___f_2376_; lean_object* v___x_2377_; 
v___f_2376_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2376_, 0, v_e_2366_);
v___x_2377_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg(v_type_2367_, v___f_2376_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
return v___x_2377_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_normFieldExpr_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2366_ = stack[0].m_obj;
lean_object* v_type_2367_ = stack[1].m_obj;
lean_object* v_a_2368_ = stack[2].m_obj;
lean_object* v_a_2369_ = stack[3].m_obj;
lean_object* v_a_2370_ = stack[4].m_obj;
lean_object* v_a_2371_ = stack[5].m_obj;
lean_object* v_res_2378_;
v_res_2378_ = l_Lean_Meta_Grind_Arith_normFieldExpr_x3f(v_e_2366_, v_type_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_);
stack->m_obj
 = v_res_2378_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___boxed(lean_object* v_e_2379_, lean_object* v_type_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_Meta_Grind_Arith_normFieldExpr_x3f(v_e_2379_, v_type_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
return v_res_2386_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_FieldNormNum(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_FieldNormNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_SafeExponentiation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Init_Grind_FieldNormNum(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_FieldNormNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_SafeExponentiation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum(builtin);
}
#ifdef __cplusplus
}
#endif

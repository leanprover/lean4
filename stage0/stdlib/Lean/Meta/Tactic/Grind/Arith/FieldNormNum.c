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
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_mul___boxed(lean_object*, lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* l_Rat_div___boxed(lean_object*, lean_object*);
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
lean_object* l_Rat_neg(lean_object*);
lean_object* l_Rat_inv(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Inv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__2_value),LEAN_SCALAR_PTR_LITERAL(142, 68, 231, 210, 96, 163, 154, 19)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__3_value),LEAN_SCALAR_PTR_LITERAL(63, 31, 248, 222, 13, 64, 40, 141)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__5_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__6_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hPow"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__8_value),LEAN_SCALAR_PTR_LITERAL(155, 188, 136, 200, 106, 253, 76, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__9_value),LEAN_SCALAR_PTR_LITERAL(32, 63, 208, 57, 56, 184, 164, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__11_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__12_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__14_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__15_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__17_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__18_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_add, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NormNum"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "add_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__22_value),LEAN_SCALAR_PTR_LITERAL(151, 14, 160, 138, 120, 252, 73, 10)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__24_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mul_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__25_value),LEAN_SCALAR_PTR_LITERAL(136, 255, 164, 25, 71, 39, 174, 147)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_sub, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__27_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "sub_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28_value),LEAN_SCALAR_PTR_LITERAL(2, 162, 150, 24, 33, 169, 123, 203)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_div___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "div_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__31 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__31_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__31_value),LEAN_SCALAR_PTR_LITERAL(177, 1, 34, 4, 92, 31, 232, 201)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "zpow_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__33 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__33_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__33_value),LEAN_SCALAR_PTR_LITERAL(252, 102, 170, 198, 226, 30, 47, 17)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__40 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__40_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__40_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "npow_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__43 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__43_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__43_value),LEAN_SCALAR_PTR_LITERAL(37, 32, 174, 21, 58, 233, 39, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_neg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__45 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__45_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "neg_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46_value),LEAN_SCALAR_PTR_LITERAL(3, 23, 32, 100, 239, 35, 23, 252)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Rat_inv, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "inv_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__49 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__49_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__49_value),LEAN_SCALAR_PTR_LITERAL(0, 163, 29, 198, 30, 103, 3, 4)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ofNat_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__51 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__51_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__51_value),LEAN_SCALAR_PTR_LITERAL(136, 66, 33, 38, 61, 161, 62, 214)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "natCast_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__53 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__53_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__53_value),LEAN_SCALAR_PTR_LITERAL(117, 220, 31, 33, 212, 54, 218, 117)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "intCast_eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__55 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__55_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
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
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 252, 205, 142, 101, 192, 24, 119)}};
static const lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "eq_inv"};
static const lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(123, 176, 154, 3, 27, 184, 143, 27)}};
static const lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "eq_int"};
static const lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 164, 44, 189, 207, 226, 143, 119)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value),LEAN_SCALAR_PTR_LITERAL(250, 99, 131, 34, 185, 54, 42, 120)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg(lean_object* v_type_35_, lean_object* v_x_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_){
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
lean_dec_ref(v_a_43_);
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
lean_dec_ref(v_a_54_);
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
lean_dec_ref(v___x_72_);
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
lean_dec_ref(v_a_74_);
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
lean_dec_ref(v___x_50_);
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
lean_dec_ref(v___x_50_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___boxed(lean_object* v_type_128_, lean_object* v_x_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg(v_type_128_, v_x_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f(lean_object* v_00_u03b1_136_, lean_object* v_type_137_, lean_object* v_x_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg(v_type_137_, v_x_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___boxed(lean_object* v_00_u03b1_145_, lean_object* v_type_146_, lean_object* v_x_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f(v_00_u03b1_145_, v_type_146_, v_x_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
lean_dec(v_a_149_);
lean_dec_ref(v_a_148_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst(lean_object* v_inst_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_u_171_; lean_object* v_type_172_; lean_object* v_semiringInst_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_u_171_ = lean_ctor_get(v_a_165_, 0);
v_type_172_ = lean_ctor_get(v_a_165_, 1);
v_semiringInst_173_ = lean_ctor_get(v_a_165_, 5);
v___x_174_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__1));
v___x_175_ = lean_box(0);
lean_inc(v_u_171_);
v___x_176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_176_, 0, v_u_171_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
lean_inc_ref(v___x_176_);
v___x_177_ = l_Lean_mkConst(v___x_174_, v___x_176_);
v___x_178_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4));
v___x_179_ = l_Lean_mkConst(v___x_178_, v___x_176_);
lean_inc_ref(v_semiringInst_173_);
lean_inc_ref_n(v_type_172_, 2);
v___x_180_ = l_Lean_mkAppB(v___x_179_, v_type_172_, v_semiringInst_173_);
v___x_181_ = l_Lean_mkAppB(v___x_177_, v_type_172_, v___x_180_);
v___x_182_ = l_Lean_Meta_isDefEqI(v_inst_164_, v___x_181_, v_a_166_, v_a_167_, v_a_168_, v_a_169_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_191_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_191_ == 0)
{
v___x_185_ = v___x_182_;
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_187_, 0, v_a_183_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_187_);
v___x_189_ = v___x_185_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
v_a_192_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_182_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_182_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___boxed(lean_object* v_inst_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst(v_inst_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec(v_a_203_);
lean_dec_ref(v_a_202_);
lean_dec_ref(v_a_201_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst(lean_object* v_inst_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_u_224_; lean_object* v_type_225_; lean_object* v_semiringInst_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_u_224_ = lean_ctor_get(v_a_218_, 0);
v_type_225_ = lean_ctor_get(v_a_218_, 1);
v_semiringInst_226_ = lean_ctor_get(v_a_218_, 5);
v___x_227_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__1));
v___x_228_ = lean_box(0);
lean_inc(v_u_224_);
v___x_229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_229_, 0, v_u_224_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
lean_inc_ref(v___x_229_);
v___x_230_ = l_Lean_mkConst(v___x_227_, v___x_229_);
v___x_231_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3));
v___x_232_ = l_Lean_mkConst(v___x_231_, v___x_229_);
lean_inc_ref(v_semiringInst_226_);
lean_inc_ref_n(v_type_225_, 2);
v___x_233_ = l_Lean_mkAppB(v___x_232_, v_type_225_, v_semiringInst_226_);
v___x_234_ = l_Lean_mkAppB(v___x_230_, v_type_225_, v___x_233_);
v___x_235_ = l_Lean_Meta_isDefEqI(v_inst_217_, v___x_234_, v_a_219_, v_a_220_, v_a_221_, v_a_222_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_244_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_244_ == 0)
{
v___x_238_ = v___x_235_;
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_235_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v_a_236_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 0, v___x_240_);
v___x_242_ = v___x_238_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
v_a_245_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_235_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_235_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___boxed(lean_object* v_inst_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst(v_inst_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec_ref(v_a_254_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst(lean_object* v_inst_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_u_277_; lean_object* v_type_278_; lean_object* v_ringInst_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_u_277_ = lean_ctor_get(v_a_271_, 0);
v_type_278_ = lean_ctor_get(v_a_271_, 1);
v_ringInst_279_ = lean_ctor_get(v_a_271_, 4);
v___x_280_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__1));
v___x_281_ = lean_box(0);
lean_inc(v_u_277_);
v___x_282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_282_, 0, v_u_277_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
lean_inc_ref(v___x_282_);
v___x_283_ = l_Lean_mkConst(v___x_280_, v___x_282_);
v___x_284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3));
v___x_285_ = l_Lean_mkConst(v___x_284_, v___x_282_);
lean_inc_ref(v_ringInst_279_);
lean_inc_ref_n(v_type_278_, 2);
v___x_286_ = l_Lean_mkAppB(v___x_285_, v_type_278_, v_ringInst_279_);
v___x_287_ = l_Lean_mkAppB(v___x_283_, v_type_278_, v___x_286_);
v___x_288_ = l_Lean_Meta_isDefEqI(v_inst_270_, v___x_287_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_297_; 
v_a_289_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_297_ == 0)
{
v___x_291_ = v___x_288_;
v_isShared_292_ = v_isSharedCheck_297_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_297_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_293_, 0, v_a_289_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_293_);
v___x_295_ = v___x_291_;
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
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
v_a_298_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_288_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_288_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___boxed(lean_object* v_inst_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst(v_inst_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec_ref(v_a_307_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst(lean_object* v_inst_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_u_330_; lean_object* v_type_331_; lean_object* v_fieldInst_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_u_330_ = lean_ctor_get(v_a_324_, 0);
v_type_331_ = lean_ctor_get(v_a_324_, 1);
v_fieldInst_332_ = lean_ctor_get(v_a_324_, 2);
v___x_333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__1));
v___x_334_ = lean_box(0);
lean_inc(v_u_330_);
v___x_335_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_335_, 0, v_u_330_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
lean_inc_ref(v___x_335_);
v___x_336_ = l_Lean_mkConst(v___x_333_, v___x_335_);
v___x_337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3));
v___x_338_ = l_Lean_mkConst(v___x_337_, v___x_335_);
lean_inc_ref(v_fieldInst_332_);
lean_inc_ref_n(v_type_331_, 2);
v___x_339_ = l_Lean_mkAppB(v___x_338_, v_type_331_, v_fieldInst_332_);
v___x_340_ = l_Lean_mkAppB(v___x_336_, v_type_331_, v___x_339_);
v___x_341_ = l_Lean_Meta_isDefEqI(v_inst_323_, v___x_340_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_350_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_350_ == 0)
{
v___x_344_ = v___x_341_;
v_isShared_345_ = v_isSharedCheck_350_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_350_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v___x_348_; 
v___x_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_346_, 0, v_a_342_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_346_);
v___x_348_ = v___x_344_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v_a_351_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_341_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_341_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___boxed(lean_object* v_inst_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst(v_inst_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec_ref(v_a_360_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst(lean_object* v_inst_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_u_380_; lean_object* v_type_381_; lean_object* v_ringInst_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_u_380_ = lean_ctor_get(v_a_374_, 0);
v_type_381_ = lean_ctor_get(v_a_374_, 1);
v_ringInst_382_ = lean_ctor_get(v_a_374_, 4);
v___x_383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1));
v___x_384_ = lean_box(0);
lean_inc(v_u_380_);
v___x_385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_385_, 0, v_u_380_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = l_Lean_mkConst(v___x_383_, v___x_385_);
lean_inc_ref(v_ringInst_382_);
lean_inc_ref(v_type_381_);
v___x_387_ = l_Lean_mkAppB(v___x_386_, v_type_381_, v_ringInst_382_);
v___x_388_ = l_Lean_Meta_isDefEqI(v_inst_373_, v___x_387_, v_a_375_, v_a_376_, v_a_377_, v_a_378_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_397_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_397_ == 0)
{
v___x_391_ = v___x_388_;
v_isShared_392_ = v_isSharedCheck_397_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_388_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_397_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_393_, 0, v_a_389_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_393_);
v___x_395_ = v___x_391_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
v_a_398_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_388_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_388_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___boxed(lean_object* v_inst_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst(v_inst_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec_ref(v_a_407_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst(lean_object* v_inst_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_u_427_; lean_object* v_type_428_; lean_object* v_fieldInst_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v_u_427_ = lean_ctor_get(v_a_421_, 0);
v_type_428_ = lean_ctor_get(v_a_421_, 1);
v_fieldInst_429_ = lean_ctor_get(v_a_421_, 2);
v___x_430_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1));
v___x_431_ = lean_box(0);
lean_inc(v_u_427_);
v___x_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_432_, 0, v_u_427_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = l_Lean_mkConst(v___x_430_, v___x_432_);
lean_inc_ref(v_fieldInst_429_);
lean_inc_ref(v_type_428_);
v___x_434_ = l_Lean_mkAppB(v___x_433_, v_type_428_, v_fieldInst_429_);
v___x_435_ = l_Lean_Meta_isDefEqI(v_inst_420_, v___x_434_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_444_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_444_ == 0)
{
v___x_438_ = v___x_435_;
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_440_, 0, v_a_436_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_440_);
v___x_442_ = v___x_438_;
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
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
v_a_445_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_435_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_435_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___boxed(lean_object* v_inst_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst(v_inst_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec_ref(v_a_454_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst(lean_object* v_inst_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v_u_474_; lean_object* v_type_475_; lean_object* v_semiringInst_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v_u_474_ = lean_ctor_get(v_a_468_, 0);
v_type_475_ = lean_ctor_get(v_a_468_, 1);
v_semiringInst_476_ = lean_ctor_get(v_a_468_, 5);
v___x_477_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1));
v___x_478_ = lean_box(0);
lean_inc(v_u_474_);
v___x_479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_479_, 0, v_u_474_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
v___x_480_ = l_Lean_mkConst(v___x_477_, v___x_479_);
lean_inc_ref(v_semiringInst_476_);
lean_inc_ref(v_type_475_);
v___x_481_ = l_Lean_mkAppB(v___x_480_, v_type_475_, v_semiringInst_476_);
v___x_482_ = l_Lean_Meta_isDefEqI(v_inst_467_, v___x_481_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_491_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_491_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_491_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_491_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_487_, 0, v_a_483_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_487_);
v___x_489_ = v___x_485_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
v_a_492_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_482_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_482_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___boxed(lean_object* v_inst_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst(v_inst_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
lean_dec(v_a_505_);
lean_dec_ref(v_a_504_);
lean_dec(v_a_503_);
lean_dec_ref(v_a_502_);
lean_dec_ref(v_a_501_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst(lean_object* v_inst_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_u_521_; lean_object* v_type_522_; lean_object* v_fieldInst_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v_u_521_ = lean_ctor_get(v_a_515_, 0);
v_type_522_ = lean_ctor_get(v_a_515_, 1);
v_fieldInst_523_ = lean_ctor_get(v_a_515_, 2);
v___x_524_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1));
v___x_525_ = lean_box(0);
lean_inc(v_u_521_);
v___x_526_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_526_, 0, v_u_521_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = l_Lean_mkConst(v___x_524_, v___x_526_);
lean_inc_ref(v_fieldInst_523_);
lean_inc_ref(v_type_522_);
v___x_528_ = l_Lean_mkAppB(v___x_527_, v_type_522_, v_fieldInst_523_);
v___x_529_ = l_Lean_Meta_isDefEqI(v_inst_514_, v___x_528_, v_a_516_, v_a_517_, v_a_518_, v_a_519_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_538_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_538_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_538_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_538_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_534_, 0, v_a_530_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_534_);
v___x_536_ = v___x_532_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
v_a_539_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_529_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_529_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___boxed(lean_object* v_inst_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst(v_inst_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
lean_dec_ref(v_a_548_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst(lean_object* v_inst_561_, lean_object* v_n_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v_u_569_; lean_object* v_type_570_; lean_object* v_semiringInst_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_u_569_ = lean_ctor_get(v_a_563_, 0);
v_type_570_ = lean_ctor_get(v_a_563_, 1);
v_semiringInst_571_ = lean_ctor_get(v_a_563_, 5);
v___x_572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1));
v___x_573_ = lean_box(0);
lean_inc(v_u_569_);
v___x_574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_574_, 0, v_u_569_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = l_Lean_mkConst(v___x_572_, v___x_574_);
lean_inc_ref(v_semiringInst_571_);
lean_inc_ref(v_type_570_);
v___x_576_ = l_Lean_mkApp3(v___x_575_, v_type_570_, v_semiringInst_571_, v_n_562_);
v___x_577_ = l_Lean_Meta_isDefEqI(v_inst_561_, v___x_576_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_586_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_586_ == 0)
{
v___x_580_ = v___x_577_;
v_isShared_581_ = v_isSharedCheck_586_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_577_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_586_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_582_, 0, v_a_578_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 0, v___x_582_);
v___x_584_ = v___x_580_;
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
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
v_a_587_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_577_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_577_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___boxed(lean_object* v_inst_595_, lean_object* v_n_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst(v_inst_595_, v_n_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec_ref(v_a_597_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg(lean_object* v_a_610_){
_start:
{
lean_object* v_u_612_; lean_object* v_type_613_; lean_object* v_semiringInst_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_u_612_ = lean_ctor_get(v_a_610_, 0);
v_type_613_ = lean_ctor_get(v_a_610_, 1);
v_semiringInst_614_ = lean_ctor_get(v_a_610_, 5);
v___x_615_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1));
v___x_616_ = lean_box(0);
lean_inc(v_u_612_);
v___x_617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_617_, 0, v_u_612_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = l_Lean_mkConst(v___x_615_, v___x_617_);
lean_inc_ref(v_semiringInst_614_);
lean_inc_ref(v_type_613_);
v___x_619_ = l_Lean_mkAppB(v___x_618_, v_type_613_, v_semiringInst_614_);
v___x_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___boxed(lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg(v_a_622_);
lean_dec_ref(v_a_622_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst(lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg(v_a_625_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___boxed(lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst(v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec_ref(v_a_632_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNatCastInst(lean_object* v_inst_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v___x_646_; lean_object* v_a_647_; lean_object* v_val_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_672_; 
v___x_646_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg(v_a_640_);
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
lean_dec_ref(v___x_646_);
v_val_648_ = lean_ctor_get(v_a_647_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v_a_647_);
if (v_isSharedCheck_672_ == 0)
{
v___x_650_ = v_a_647_;
v_isShared_651_ = v_isSharedCheck_672_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_val_648_);
lean_dec(v_a_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_672_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_Meta_isDefEqI(v_inst_639_, v_val_648_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_663_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_663_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_663_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_663_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v_a_653_);
v___x_658_ = v___x_650_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_662_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
lean_object* v___x_660_; 
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_658_);
v___x_660_ = v___x_655_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_658_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_del_object(v___x_650_);
v_a_664_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_652_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_652_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNatCastInst___boxed(lean_object* v_inst_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNatCastInst(v_inst_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec_ref(v_a_674_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast(lean_object* v_n_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_){
_start:
{
lean_object* v_r_693_; lean_object* v_u_696_; lean_object* v_type_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v_u_696_ = lean_ctor_get(v_a_686_, 0);
v_type_697_ = lean_ctor_get(v_a_686_, 1);
v___x_698_ = l_Lean_mkNatLit(v_n_685_);
v___x_699_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1));
lean_inc_ref(v_type_697_);
v___x_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_700_, 0, v_type_697_);
v___x_701_ = lean_box(0);
lean_inc_ref(v___x_698_);
v___x_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_698_);
v___x_703_ = lean_unsigned_to_nat(3u);
v___x_704_ = lean_mk_empty_array_with_capacity(v___x_703_);
v___x_705_ = lean_array_push(v___x_704_, v___x_700_);
v___x_706_ = lean_array_push(v___x_705_, v___x_701_);
v___x_707_ = lean_array_push(v___x_706_, v___x_702_);
v___x_708_ = l_Lean_Meta_mkAppOptM(v___x_699_, v___x_707_, v_a_687_, v_a_688_, v_a_689_, v_a_690_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; 
lean_dec_ref(v___x_698_);
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref(v___x_708_);
v_r_693_ = v_a_709_;
goto v___jp_692_;
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_728_; 
v_a_710_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_728_ == 0)
{
v___x_712_ = v___x_708_;
v_isShared_713_ = v_isSharedCheck_728_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_708_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_728_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
uint8_t v___y_715_; uint8_t v___x_726_; 
v___x_726_ = l_Lean_Exception_isInterrupt(v_a_710_);
if (v___x_726_ == 0)
{
uint8_t v___x_727_; 
lean_inc(v_a_710_);
v___x_727_ = l_Lean_Exception_isRuntime(v_a_710_);
v___y_715_ = v___x_727_;
goto v___jp_714_;
}
else
{
v___y_715_ = v___x_726_;
goto v___jp_714_;
}
v___jp_714_:
{
if (v___y_715_ == 0)
{
lean_object* v___x_716_; lean_object* v_a_717_; lean_object* v_val_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
lean_del_object(v___x_712_);
lean_dec(v_a_710_);
v___x_716_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg(v_a_686_);
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref(v___x_716_);
v_val_718_ = lean_ctor_get(v_a_717_, 0);
lean_inc(v_val_718_);
lean_dec(v_a_717_);
v___x_719_ = lean_box(0);
lean_inc(v_u_696_);
v___x_720_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_720_, 0, v_u_696_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = l_Lean_mkConst(v___x_699_, v___x_720_);
lean_inc_ref(v_type_697_);
v___x_722_ = l_Lean_mkApp3(v___x_721_, v_type_697_, v_val_718_, v___x_698_);
v_r_693_ = v___x_722_;
goto v___jp_692_;
}
else
{
lean_object* v___x_724_; 
lean_dec_ref(v___x_698_);
if (v_isShared_713_ == 0)
{
v___x_724_ = v___x_712_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_710_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
v___jp_692_:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_694_, 0, v_r_693_);
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
return v___x_695_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___boxed(lean_object* v_n_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast(v_n_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec_ref(v_a_730_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(lean_object* v_a_743_){
_start:
{
lean_object* v_u_745_; lean_object* v_type_746_; lean_object* v_ringInst_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v_u_745_ = lean_ctor_get(v_a_743_, 0);
v_type_746_ = lean_ctor_get(v_a_743_, 1);
v_ringInst_747_ = lean_ctor_get(v_a_743_, 4);
v___x_748_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1));
v___x_749_ = lean_box(0);
lean_inc(v_u_745_);
v___x_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_750_, 0, v_u_745_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = l_Lean_mkConst(v___x_748_, v___x_750_);
lean_inc_ref(v_ringInst_747_);
lean_inc_ref(v_type_746_);
v___x_752_ = l_Lean_mkAppB(v___x_751_, v_type_746_, v_ringInst_747_);
v___x_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
v___x_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___boxed(lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(v_a_755_);
lean_dec_ref(v_a_755_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst(lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(v_a_758_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___boxed(lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst(v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec_ref(v_a_765_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isIntCastInst(lean_object* v_inst_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
lean_object* v___x_779_; lean_object* v_a_780_; lean_object* v_val_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_805_; 
v___x_779_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(v_a_773_);
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
lean_dec_ref(v___x_779_);
v_val_781_ = lean_ctor_get(v_a_780_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v_a_780_);
if (v_isSharedCheck_805_ == 0)
{
v___x_783_ = v_a_780_;
v_isShared_784_ = v_isSharedCheck_805_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_val_781_);
lean_dec(v_a_780_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_805_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_Meta_isDefEqI(v_inst_772_, v_val_781_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_796_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_796_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_796_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_796_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v_a_786_);
v___x_791_ = v___x_783_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_795_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_793_; 
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_791_);
v___x_793_ = v___x_788_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_del_object(v___x_783_);
v_a_797_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_785_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_785_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isIntCastInst___boxed(lean_object* v_inst_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isIntCastInst(v_inst_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec_ref(v_a_807_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast(lean_object* v_n_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_r_826_; lean_object* v_u_829_; lean_object* v_type_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v_u_829_ = lean_ctor_get(v_a_819_, 0);
v_type_830_ = lean_ctor_get(v_a_819_, 1);
v___x_831_ = l_Lean_mkIntLit(v_n_818_);
v___x_832_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1));
lean_inc_ref(v_type_830_);
v___x_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_833_, 0, v_type_830_);
v___x_834_ = lean_box(0);
lean_inc_ref(v___x_831_);
v___x_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_831_);
v___x_836_ = lean_unsigned_to_nat(3u);
v___x_837_ = lean_mk_empty_array_with_capacity(v___x_836_);
v___x_838_ = lean_array_push(v___x_837_, v___x_833_);
v___x_839_ = lean_array_push(v___x_838_, v___x_834_);
v___x_840_ = lean_array_push(v___x_839_, v___x_835_);
v___x_841_ = l_Lean_Meta_mkAppOptM(v___x_832_, v___x_840_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; 
lean_dec_ref(v___x_831_);
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref(v___x_841_);
v_r_826_ = v_a_842_;
goto v___jp_825_;
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_861_; 
v_a_843_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_861_ == 0)
{
v___x_845_ = v___x_841_;
v_isShared_846_ = v_isSharedCheck_861_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_841_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_861_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
uint8_t v___y_848_; uint8_t v___x_859_; 
v___x_859_ = l_Lean_Exception_isInterrupt(v_a_843_);
if (v___x_859_ == 0)
{
uint8_t v___x_860_; 
lean_inc(v_a_843_);
v___x_860_ = l_Lean_Exception_isRuntime(v_a_843_);
v___y_848_ = v___x_860_;
goto v___jp_847_;
}
else
{
v___y_848_ = v___x_859_;
goto v___jp_847_;
}
v___jp_847_:
{
if (v___y_848_ == 0)
{
lean_object* v___x_849_; lean_object* v_a_850_; lean_object* v_val_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
lean_del_object(v___x_845_);
lean_dec(v_a_843_);
v___x_849_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(v_a_819_);
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref(v___x_849_);
v_val_851_ = lean_ctor_get(v_a_850_, 0);
lean_inc(v_val_851_);
lean_dec(v_a_850_);
v___x_852_ = lean_box(0);
lean_inc(v_u_829_);
v___x_853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_853_, 0, v_u_829_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = l_Lean_mkConst(v___x_832_, v___x_853_);
lean_inc_ref(v_type_830_);
v___x_855_ = l_Lean_mkApp3(v___x_854_, v_type_830_, v_val_851_, v___x_831_);
v_r_826_ = v___x_855_;
goto v___jp_825_;
}
else
{
lean_object* v___x_857_; 
lean_dec_ref(v___x_831_);
if (v_isShared_846_ == 0)
{
v___x_857_ = v___x_845_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_843_);
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
v___jp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_827_, 0, v_r_826_);
v___x_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
return v___x_828_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___boxed(lean_object* v_n_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast(v_n_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec_ref(v_a_863_);
lean_dec(v_n_862_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin_spec__0(lean_object* v_a_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = lean_nat_to_int(v_a_870_);
return v___x_871_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = lean_unsigned_to_nat(0u);
v___x_878_ = l_Lean_Level_ofNat(v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_879_ = lean_box(0);
v___x_880_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3);
v___x_881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
lean_ctor_set(v___x_881_, 1, v___x_879_);
return v___x_881_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__5(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_882_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4);
v___x_883_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3);
v___x_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v___x_882_);
return v___x_884_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__6(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_885_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__5);
v___x_886_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3);
v___x_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v___x_885_);
return v___x_887_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_888_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__6);
v___x_889_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2));
v___x_890_ = l_Lean_Expr_const___override(v___x_889_, v___x_888_);
return v___x_890_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_894_ = lean_box(0);
v___x_895_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__9));
v___x_896_ = l_Lean_Expr_const___override(v___x_895_, v___x_894_);
return v___x_896_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__11(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4);
v___x_898_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__1));
v___x_899_ = l_Lean_Expr_const___override(v___x_898_, v___x_897_);
return v___x_899_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__14(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_904_ = lean_box(0);
v___x_905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__13));
v___x_906_ = l_Lean_Expr_const___override(v___x_905_, v___x_904_);
return v___x_906_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_907_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__14, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__14);
v___x_908_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_909_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__11);
v___x_910_ = l_Lean_mkAppB(v___x_909_, v___x_908_, v___x_907_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(lean_object* v_declName_911_, lean_object* v_a_912_, lean_object* v_b_913_, lean_object* v_r_u2081_914_, lean_object* v_r_u2082_915_, lean_object* v_op_916_, lean_object* v_a_917_){
_start:
{
lean_object* v_fst_919_; lean_object* v_snd_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_993_; 
v_fst_919_ = lean_ctor_get(v_r_u2081_914_, 0);
v_snd_920_ = lean_ctor_get(v_r_u2081_914_, 1);
v_isSharedCheck_993_ = !lean_is_exclusive(v_r_u2081_914_);
if (v_isSharedCheck_993_ == 0)
{
v___x_922_ = v_r_u2081_914_;
v_isShared_923_ = v_isSharedCheck_993_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_snd_920_);
lean_inc(v_fst_919_);
lean_dec(v_r_u2081_914_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_993_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v_fst_924_; lean_object* v_snd_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_992_; 
v_fst_924_ = lean_ctor_get(v_r_u2082_915_, 0);
v_snd_925_ = lean_ctor_get(v_r_u2082_915_, 1);
v_isSharedCheck_992_ = !lean_is_exclusive(v_r_u2082_915_);
if (v_isSharedCheck_992_ == 0)
{
v___x_927_ = v_r_u2082_915_;
v_isShared_928_ = v_isSharedCheck_992_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_snd_925_);
lean_inc(v_fst_924_);
lean_dec(v_r_u2082_915_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_992_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v_u_929_; lean_object* v_type_930_; lean_object* v_fieldInst_931_; lean_object* v_isChar0Inst_932_; lean_object* v_num_933_; lean_object* v_den_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v_u_929_ = lean_ctor_get(v_a_917_, 0);
v_type_930_ = lean_ctor_get(v_a_917_, 1);
v_fieldInst_931_ = lean_ctor_get(v_a_917_, 2);
v_isChar0Inst_932_ = lean_ctor_get(v_a_917_, 3);
v_num_933_ = lean_ctor_get(v_fst_919_, 0);
lean_inc(v_num_933_);
v_den_934_ = lean_ctor_get(v_fst_919_, 1);
lean_inc(v_den_934_);
lean_inc(v_fst_924_);
v___x_935_ = lean_apply_2(v_op_916_, v_fst_919_, v_fst_924_);
v___x_936_ = lean_box(0);
lean_inc(v_u_929_);
if (v_isShared_923_ == 0)
{
lean_ctor_set_tag(v___x_922_, 1);
lean_ctor_set(v___x_922_, 1, v___x_936_);
lean_ctor_set(v___x_922_, 0, v_u_929_);
v___x_938_ = v___x_922_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_u_929_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v___x_936_);
v___x_938_ = v_reuseFailAlloc_991_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
lean_object* v___x_939_; lean_object* v___y_941_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_953_; lean_object* v___y_954_; lean_object* v___y_968_; lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_939_ = l_Lean_mkConst(v_declName_911_, v___x_938_);
v___x_981_ = lean_unsigned_to_nat(1u);
v___x_982_ = lean_nat_dec_eq(v_den_934_, v___x_981_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_983_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_984_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_985_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_986_ = l_Lean_instToExprRat_mkInt(v_num_933_);
lean_dec(v_num_933_);
v___x_987_ = lean_nat_to_int(v_den_934_);
v___x_988_ = l_Lean_instToExprRat_mkInt(v___x_987_);
lean_dec(v___x_987_);
v___x_989_ = l_Lean_mkApp6(v___x_983_, v___x_984_, v___x_984_, v___x_984_, v___x_985_, v___x_986_, v___x_988_);
v___y_968_ = v___x_989_;
goto v___jp_967_;
}
else
{
lean_object* v___x_990_; 
lean_dec(v_den_934_);
v___x_990_ = l_Lean_instToExprRat_mkInt(v_num_933_);
lean_dec(v_num_933_);
v___y_968_ = v___x_990_;
goto v___jp_967_;
}
v___jp_940_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
lean_inc_ref(v_isChar0Inst_932_);
lean_inc_ref(v_fieldInst_931_);
lean_inc_ref(v_type_930_);
v___x_944_ = l_Lean_mkApp8(v___x_939_, v_type_930_, v_fieldInst_931_, v_isChar0Inst_932_, v_a_912_, v_b_913_, v___y_941_, v___y_942_, v___y_943_);
v___x_945_ = l_Lean_eagerReflBoolTrue;
v___x_946_ = l_Lean_mkApp3(v___x_944_, v___x_945_, v_snd_920_, v_snd_925_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 1, v___x_946_);
lean_ctor_set(v___x_927_, 0, v___x_935_);
v___x_948_ = v___x_927_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v___x_946_);
v___x_948_ = v_reuseFailAlloc_951_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
return v___x_950_;
}
}
v___jp_952_:
{
lean_object* v_num_955_; lean_object* v_den_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v_num_955_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_num_955_);
v_den_956_ = lean_ctor_get(v___x_935_, 1);
lean_inc(v_den_956_);
v___x_957_ = lean_unsigned_to_nat(1u);
v___x_958_ = lean_nat_dec_eq(v_den_956_, v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_959_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_960_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_961_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_962_ = l_Lean_instToExprRat_mkInt(v_num_955_);
lean_dec(v_num_955_);
v___x_963_ = lean_nat_to_int(v_den_956_);
v___x_964_ = l_Lean_instToExprRat_mkInt(v___x_963_);
lean_dec(v___x_963_);
v___x_965_ = l_Lean_mkApp6(v___x_959_, v___x_960_, v___x_960_, v___x_960_, v___x_961_, v___x_962_, v___x_964_);
v___y_941_ = v___y_953_;
v___y_942_ = v___y_954_;
v___y_943_ = v___x_965_;
goto v___jp_940_;
}
else
{
lean_object* v___x_966_; 
lean_dec(v_den_956_);
v___x_966_ = l_Lean_instToExprRat_mkInt(v_num_955_);
lean_dec(v_num_955_);
v___y_941_ = v___y_953_;
v___y_942_ = v___y_954_;
v___y_943_ = v___x_966_;
goto v___jp_940_;
}
}
v___jp_967_:
{
lean_object* v_num_969_; lean_object* v_den_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v_num_969_ = lean_ctor_get(v_fst_924_, 0);
lean_inc(v_num_969_);
v_den_970_ = lean_ctor_get(v_fst_924_, 1);
lean_inc(v_den_970_);
lean_dec(v_fst_924_);
v___x_971_ = lean_unsigned_to_nat(1u);
v___x_972_ = lean_nat_dec_eq(v_den_970_, v___x_971_);
if (v___x_972_ == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_973_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_974_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_975_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_976_ = l_Lean_instToExprRat_mkInt(v_num_969_);
lean_dec(v_num_969_);
v___x_977_ = lean_nat_to_int(v_den_970_);
v___x_978_ = l_Lean_instToExprRat_mkInt(v___x_977_);
lean_dec(v___x_977_);
v___x_979_ = l_Lean_mkApp6(v___x_973_, v___x_974_, v___x_974_, v___x_974_, v___x_975_, v___x_976_, v___x_978_);
v___y_953_ = v___y_968_;
v___y_954_ = v___x_979_;
goto v___jp_952_;
}
else
{
lean_object* v___x_980_; 
lean_dec(v_den_970_);
v___x_980_ = l_Lean_instToExprRat_mkInt(v_num_969_);
lean_dec(v_num_969_);
v___y_953_ = v___y_968_;
v___y_954_ = v___x_980_;
goto v___jp_952_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___boxed(lean_object* v_declName_994_, lean_object* v_a_995_, lean_object* v_b_996_, lean_object* v_r_u2081_997_, lean_object* v_r_u2082_998_, lean_object* v_op_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v_declName_994_, v_a_995_, v_b_996_, v_r_u2081_997_, v_r_u2082_998_, v_op_999_, v_a_1000_);
lean_dec_ref(v_a_1000_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin(lean_object* v_declName_1003_, lean_object* v_a_1004_, lean_object* v_b_1005_, lean_object* v_r_u2081_1006_, lean_object* v_r_u2082_1007_, lean_object* v_op_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v_declName_1003_, v_a_1004_, v_b_1005_, v_r_u2081_1006_, v_r_u2082_1007_, v_op_1008_, v_a_1009_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___boxed(lean_object* v_declName_1016_, lean_object* v_a_1017_, lean_object* v_b_1018_, lean_object* v_r_u2081_1019_, lean_object* v_r_u2082_1020_, lean_object* v_op_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin(v_declName_1016_, v_a_1017_, v_b_1018_, v_r_u2081_1019_, v_r_u2082_1020_, v_op_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec_ref(v_a_1022_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(lean_object* v_declName_1029_, lean_object* v_a_1030_, lean_object* v_r_1031_, lean_object* v_op_1032_, lean_object* v_a_1033_){
_start:
{
lean_object* v_fst_1035_; lean_object* v_snd_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1083_; 
v_fst_1035_ = lean_ctor_get(v_r_1031_, 0);
v_snd_1036_ = lean_ctor_get(v_r_1031_, 1);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_r_1031_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1038_ = v_r_1031_;
v_isShared_1039_ = v_isSharedCheck_1083_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_snd_1036_);
lean_inc(v_fst_1035_);
lean_dec(v_r_1031_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1083_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v_u_1040_; lean_object* v_type_1041_; lean_object* v_fieldInst_1042_; lean_object* v_num_1043_; lean_object* v_den_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1060_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v_u_1040_ = lean_ctor_get(v_a_1033_, 0);
v_type_1041_ = lean_ctor_get(v_a_1033_, 1);
v_fieldInst_1042_ = lean_ctor_get(v_a_1033_, 2);
v_num_1043_ = lean_ctor_get(v_fst_1035_, 0);
lean_inc(v_num_1043_);
v_den_1044_ = lean_ctor_get(v_fst_1035_, 1);
lean_inc(v_den_1044_);
v___x_1045_ = lean_apply_1(v_op_1032_, v_fst_1035_);
v___x_1046_ = lean_box(0);
lean_inc(v_u_1040_);
v___x_1047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1047_, 0, v_u_1040_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = l_Lean_mkConst(v_declName_1029_, v___x_1047_);
v___x_1073_ = lean_unsigned_to_nat(1u);
v___x_1074_ = lean_nat_dec_eq(v_den_1044_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1075_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_1076_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_1077_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_1078_ = l_Lean_instToExprRat_mkInt(v_num_1043_);
lean_dec(v_num_1043_);
v___x_1079_ = lean_nat_to_int(v_den_1044_);
v___x_1080_ = l_Lean_instToExprRat_mkInt(v___x_1079_);
lean_dec(v___x_1079_);
v___x_1081_ = l_Lean_mkApp6(v___x_1075_, v___x_1076_, v___x_1076_, v___x_1076_, v___x_1077_, v___x_1078_, v___x_1080_);
v___y_1060_ = v___x_1081_;
goto v___jp_1059_;
}
else
{
lean_object* v___x_1082_; 
lean_dec(v_den_1044_);
v___x_1082_ = l_Lean_instToExprRat_mkInt(v_num_1043_);
lean_dec(v_num_1043_);
v___y_1060_ = v___x_1082_;
goto v___jp_1059_;
}
v___jp_1049_:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1052_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_fieldInst_1042_);
lean_inc_ref(v_type_1041_);
v___x_1053_ = l_Lean_mkApp7(v___x_1048_, v_type_1041_, v_fieldInst_1042_, v_a_1030_, v___y_1050_, v___y_1051_, v___x_1052_, v_snd_1036_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 1, v___x_1053_);
lean_ctor_set(v___x_1038_, 0, v___x_1045_);
v___x_1055_ = v___x_1038_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1045_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
}
v___jp_1059_:
{
lean_object* v_num_1061_; lean_object* v_den_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
v_num_1061_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_num_1061_);
v_den_1062_ = lean_ctor_get(v___x_1045_, 1);
lean_inc(v_den_1062_);
v___x_1063_ = lean_unsigned_to_nat(1u);
v___x_1064_ = lean_nat_dec_eq(v_den_1062_, v___x_1063_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1065_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_1066_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_1067_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_1068_ = l_Lean_instToExprRat_mkInt(v_num_1061_);
lean_dec(v_num_1061_);
v___x_1069_ = lean_nat_to_int(v_den_1062_);
v___x_1070_ = l_Lean_instToExprRat_mkInt(v___x_1069_);
lean_dec(v___x_1069_);
v___x_1071_ = l_Lean_mkApp6(v___x_1065_, v___x_1066_, v___x_1066_, v___x_1066_, v___x_1067_, v___x_1068_, v___x_1070_);
v___y_1050_ = v___y_1060_;
v___y_1051_ = v___x_1071_;
goto v___jp_1049_;
}
else
{
lean_object* v___x_1072_; 
lean_dec(v_den_1062_);
v___x_1072_ = l_Lean_instToExprRat_mkInt(v_num_1061_);
lean_dec(v_num_1061_);
v___y_1050_ = v___y_1060_;
v___y_1051_ = v___x_1072_;
goto v___jp_1049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg___boxed(lean_object* v_declName_1084_, lean_object* v_a_1085_, lean_object* v_r_1086_, lean_object* v_op_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(v_declName_1084_, v_a_1085_, v_r_1086_, v_op_1087_, v_a_1088_);
lean_dec_ref(v_a_1088_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary(lean_object* v_declName_1091_, lean_object* v_a_1092_, lean_object* v_r_1093_, lean_object* v_op_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(v_declName_1091_, v_a_1092_, v_r_1093_, v_op_1094_, v_a_1095_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___boxed(lean_object* v_declName_1102_, lean_object* v_a_1103_, lean_object* v_r_1104_, lean_object* v_op_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary(v_declName_1102_, v_a_1103_, v_r_1104_, v_op_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec_ref(v_a_1106_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval_spec__1(lean_object* v_a_1113_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Rat_ofInt(v_a_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval_spec__0(lean_object* v_a_1115_){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_nat_to_int(v_a_1115_);
v___x_1117_ = l_Rat_ofInt(v___x_1116_);
return v___x_1117_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = lean_unsigned_to_nat(0u);
v___x_1193_ = lean_nat_to_int(v___x_1192_);
return v___x_1193_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4);
v___x_1195_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7));
v___x_1196_ = l_Lean_Expr_const___override(v___x_1195_, v___x_1194_);
return v___x_1196_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1200_ = lean_box(0);
v___x_1201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38));
v___x_1202_ = l_Lean_Expr_const___override(v___x_1201_, v___x_1200_);
return v___x_1202_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1207_ = lean_box(0);
v___x_1208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41));
v___x_1209_ = l_Lean_Expr_const___override(v___x_1208_, v___x_1207_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(lean_object* v_e_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1254_, v_a_1257_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1965_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1264_ = v___x_1261_;
v_isShared_1265_ = v_isSharedCheck_1965_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1261_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1965_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1271_; uint8_t v___x_1272_; 
v___x_1271_ = l_Lean_Expr_cleanupAnnotations(v_a_1262_);
v___x_1272_ = l_Lean_Expr_isApp(v___x_1271_);
if (v___x_1272_ == 0)
{
lean_dec_ref(v___x_1271_);
goto v___jp_1266_;
}
else
{
lean_object* v_arg_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v_arg_1273_ = lean_ctor_get(v___x_1271_, 1);
lean_inc_ref(v_arg_1273_);
v___x_1274_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1271_);
v___x_1275_ = l_Lean_Expr_isApp(v___x_1274_);
if (v___x_1275_ == 0)
{
lean_dec_ref(v___x_1274_);
lean_dec_ref(v_arg_1273_);
goto v___jp_1266_;
}
else
{
lean_object* v_arg_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
v_arg_1276_ = lean_ctor_get(v___x_1274_, 1);
lean_inc_ref(v_arg_1276_);
v___x_1277_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1274_);
v___x_1278_ = l_Lean_Expr_isApp(v___x_1277_);
if (v___x_1278_ == 0)
{
lean_dec_ref(v___x_1277_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
goto v___jp_1266_;
}
else
{
lean_object* v_arg_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v_arg_1279_ = lean_ctor_get(v___x_1277_, 1);
lean_inc_ref(v_arg_1279_);
v___x_1280_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1277_);
v___x_1281_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1));
v___x_1282_ = l_Lean_Expr_isConstOf(v___x_1280_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1283_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1));
v___x_1284_ = l_Lean_Expr_isConstOf(v___x_1280_, v___x_1283_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; uint8_t v___x_1286_; 
v___x_1285_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__1));
v___x_1286_ = l_Lean_Expr_isConstOf(v___x_1280_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4));
v___x_1288_ = l_Lean_Expr_isConstOf(v___x_1280_, v___x_1287_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7));
v___x_1290_ = l_Lean_Expr_isConstOf(v___x_1280_, v___x_1289_);
if (v___x_1290_ == 0)
{
uint8_t v___x_1291_; 
v___x_1291_ = l_Lean_Expr_isApp(v___x_1280_);
if (v___x_1291_ == 0)
{
lean_dec_ref(v___x_1280_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
goto v___jp_1266_;
}
else
{
lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1280_);
v___x_1293_ = l_Lean_Expr_isApp(v___x_1292_);
if (v___x_1293_ == 0)
{
lean_dec_ref(v___x_1292_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
goto v___jp_1266_;
}
else
{
lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1292_);
v___x_1295_ = l_Lean_Expr_isApp(v___x_1294_);
if (v___x_1295_ == 0)
{
lean_dec_ref(v___x_1294_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
goto v___jp_1266_;
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1296_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1294_);
v___x_1297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10));
v___x_1298_ = l_Lean_Expr_isConstOf(v___x_1296_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2));
v___x_1300_ = l_Lean_Expr_isConstOf(v___x_1296_, v___x_1299_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13));
v___x_1302_ = l_Lean_Expr_isConstOf(v___x_1296_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16));
v___x_1304_ = l_Lean_Expr_isConstOf(v___x_1296_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1305_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19));
v___x_1306_ = l_Lean_Expr_isConstOf(v___x_1296_, v___x_1305_);
lean_dec_ref(v___x_1296_);
if (v___x_1306_ == 0)
{
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
goto v___jp_1266_;
}
else
{
lean_object* v___x_1307_; 
lean_del_object(v___x_1264_);
v___x_1307_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst(v_arg_1279_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1331_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1331_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1331_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
if (lean_obj_tag(v_a_1308_) == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
v___x_1312_ = lean_box(0);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1312_);
v___x_1314_ = v___x_1310_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
else
{
lean_object* v_val_1316_; uint8_t v___x_1317_; 
v_val_1316_ = lean_ctor_get(v_a_1308_, 0);
lean_inc(v_val_1316_);
lean_dec_ref(v_a_1308_);
v___x_1317_ = lean_unbox(v_val_1316_);
lean_dec(v_val_1316_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; lean_object* v___x_1320_; 
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
v___x_1318_ = lean_box(0);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1318_);
v___x_1320_ = v___x_1310_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
else
{
lean_object* v___x_1322_; 
lean_del_object(v___x_1310_);
lean_inc_ref(v_arg_1276_);
v___x_1322_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1276_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_a_1323_);
if (lean_obj_tag(v_a_1323_) == 0)
{
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
return v___x_1322_;
}
else
{
lean_object* v_val_1324_; lean_object* v___x_1325_; 
lean_dec_ref(v___x_1322_);
v_val_1324_ = lean_ctor_get(v_a_1323_, 0);
lean_inc(v_val_1324_);
lean_dec_ref(v_a_1323_);
lean_inc_ref(v_arg_1273_);
v___x_1325_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1273_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
if (lean_obj_tag(v_a_1326_) == 0)
{
lean_dec(v_val_1324_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
return v___x_1325_;
}
else
{
lean_object* v_val_1327_; lean_object* v___f_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_dec_ref(v___x_1325_);
v_val_1327_ = lean_ctor_get(v_a_1326_, 0);
lean_inc(v_val_1327_);
lean_dec_ref(v_a_1326_);
v___f_1328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__20));
v___x_1329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23));
v___x_1330_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v___x_1329_, v_arg_1276_, v_arg_1273_, v_val_1324_, v_val_1327_, v___f_1328_, v_a_1255_);
return v___x_1330_;
}
}
else
{
lean_dec(v_val_1324_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
return v___x_1325_;
}
}
}
else
{
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
return v___x_1322_;
}
}
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
v_a_1332_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1307_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1307_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
else
{
lean_object* v___x_1340_; 
lean_dec_ref(v___x_1296_);
lean_del_object(v___x_1264_);
v___x_1340_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst(v_arg_1279_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1364_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1343_ = v___x_1340_;
v_isShared_1344_ = v_isSharedCheck_1364_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1340_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1364_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
if (lean_obj_tag(v_a_1341_) == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1347_; 
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
v___x_1345_ = lean_box(0);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1345_);
v___x_1347_ = v___x_1343_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v___x_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
else
{
lean_object* v_val_1349_; uint8_t v___x_1350_; 
v_val_1349_ = lean_ctor_get(v_a_1341_, 0);
lean_inc(v_val_1349_);
lean_dec_ref(v_a_1341_);
v___x_1350_ = lean_unbox(v_val_1349_);
lean_dec(v_val_1349_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
v___x_1351_ = lean_box(0);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1351_);
v___x_1353_ = v___x_1343_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
else
{
lean_object* v___x_1355_; 
lean_del_object(v___x_1343_);
lean_inc_ref(v_arg_1276_);
v___x_1355_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1276_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
if (lean_obj_tag(v_a_1356_) == 0)
{
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
return v___x_1355_;
}
else
{
lean_object* v_val_1357_; lean_object* v___x_1358_; 
lean_dec_ref(v___x_1355_);
v_val_1357_ = lean_ctor_get(v_a_1356_, 0);
lean_inc(v_val_1357_);
lean_dec_ref(v_a_1356_);
lean_inc_ref(v_arg_1273_);
v___x_1358_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1273_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_a_1359_);
if (lean_obj_tag(v_a_1359_) == 0)
{
lean_dec(v_val_1357_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
return v___x_1358_;
}
else
{
lean_object* v_val_1360_; lean_object* v___f_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_dec_ref(v___x_1358_);
v_val_1360_ = lean_ctor_get(v_a_1359_, 0);
lean_inc(v_val_1360_);
lean_dec_ref(v_a_1359_);
v___f_1361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__24));
v___x_1362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26));
v___x_1363_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v___x_1362_, v_arg_1276_, v_arg_1273_, v_val_1357_, v_val_1360_, v___f_1361_, v_a_1255_);
return v___x_1363_;
}
}
else
{
lean_dec(v_val_1357_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
return v___x_1358_;
}
}
}
else
{
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
return v___x_1355_;
}
}
}
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
v_a_1365_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1340_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1340_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
else
{
lean_object* v___x_1373_; 
lean_dec_ref(v___x_1296_);
lean_del_object(v___x_1264_);
v___x_1373_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst(v_arg_1279_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1397_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1376_ = v___x_1373_;
v_isShared_1377_ = v_isSharedCheck_1397_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1373_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1397_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
if (lean_obj_tag(v_a_1374_) == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1380_; 
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
v___x_1378_ = lean_box(0);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v___x_1378_);
v___x_1380_ = v___x_1376_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
else
{
lean_object* v_val_1382_; uint8_t v___x_1383_; 
v_val_1382_ = lean_ctor_get(v_a_1374_, 0);
lean_inc(v_val_1382_);
lean_dec_ref(v_a_1374_);
v___x_1383_ = lean_unbox(v_val_1382_);
lean_dec(v_val_1382_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; lean_object* v___x_1386_; 
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
v___x_1384_ = lean_box(0);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v___x_1384_);
v___x_1386_ = v___x_1376_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1384_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
else
{
lean_object* v___x_1388_; 
lean_del_object(v___x_1376_);
lean_inc_ref(v_arg_1276_);
v___x_1388_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1276_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
if (lean_obj_tag(v_a_1389_) == 0)
{
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
return v___x_1388_;
}
else
{
lean_object* v_val_1390_; lean_object* v___x_1391_; 
lean_dec_ref(v___x_1388_);
v_val_1390_ = lean_ctor_get(v_a_1389_, 0);
lean_inc(v_val_1390_);
lean_dec_ref(v_a_1389_);
lean_inc_ref(v_arg_1273_);
v___x_1391_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1273_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
if (lean_obj_tag(v_a_1392_) == 0)
{
lean_dec(v_val_1390_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
return v___x_1391_;
}
else
{
lean_object* v_val_1393_; lean_object* v___f_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_dec_ref(v___x_1391_);
v_val_1393_ = lean_ctor_get(v_a_1392_, 0);
lean_inc(v_val_1393_);
lean_dec_ref(v_a_1392_);
v___f_1394_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__27));
v___x_1395_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29));
v___x_1396_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v___x_1395_, v_arg_1276_, v_arg_1273_, v_val_1390_, v_val_1393_, v___f_1394_, v_a_1255_);
return v___x_1396_;
}
}
else
{
lean_dec(v_val_1390_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
return v___x_1391_;
}
}
}
else
{
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
return v___x_1388_;
}
}
}
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
v_a_1398_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1373_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1373_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
}
else
{
lean_object* v___x_1406_; 
lean_dec_ref(v___x_1296_);
lean_del_object(v___x_1264_);
v___x_1406_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst(v_arg_1279_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1430_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1430_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1430_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1430_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1430_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
if (lean_obj_tag(v_a_1407_) == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
v___x_1411_ = lean_box(0);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1411_);
v___x_1413_ = v___x_1409_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
else
{
lean_object* v_val_1415_; uint8_t v___x_1416_; 
v_val_1415_ = lean_ctor_get(v_a_1407_, 0);
lean_inc(v_val_1415_);
lean_dec_ref(v_a_1407_);
v___x_1416_ = lean_unbox(v_val_1415_);
lean_dec(v_val_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
v___x_1417_ = lean_box(0);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 0, v___x_1417_);
v___x_1419_ = v___x_1409_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1417_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
else
{
lean_object* v___x_1421_; 
lean_del_object(v___x_1409_);
lean_inc_ref(v_arg_1276_);
v___x_1421_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1276_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
if (lean_obj_tag(v_a_1422_) == 0)
{
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
return v___x_1421_;
}
else
{
lean_object* v_val_1423_; lean_object* v___x_1424_; 
lean_dec_ref(v___x_1421_);
v_val_1423_ = lean_ctor_get(v_a_1422_, 0);
lean_inc(v_val_1423_);
lean_dec_ref(v_a_1422_);
lean_inc_ref(v_arg_1273_);
v___x_1424_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1273_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
if (lean_obj_tag(v_a_1425_) == 0)
{
lean_dec(v_val_1423_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
return v___x_1424_;
}
else
{
lean_object* v_val_1426_; lean_object* v___f_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
lean_dec_ref(v___x_1424_);
v_val_1426_ = lean_ctor_get(v_a_1425_, 0);
lean_inc(v_val_1426_);
lean_dec_ref(v_a_1425_);
v___f_1427_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30));
v___x_1428_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32));
v___x_1429_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v___x_1428_, v_arg_1276_, v_arg_1273_, v_val_1423_, v_val_1426_, v___f_1427_, v_a_1255_);
return v___x_1429_;
}
}
else
{
lean_dec(v_val_1423_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
return v___x_1424_;
}
}
}
else
{
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
return v___x_1421_;
}
}
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
v_a_1431_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1406_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1406_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
else
{
lean_object* v___x_1439_; 
lean_dec_ref(v___x_1296_);
lean_del_object(v___x_1264_);
lean_inc_ref(v_arg_1279_);
v___x_1439_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst(v_arg_1279_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1692_; 
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1442_ = v___x_1439_;
v_isShared_1443_ = v_isSharedCheck_1692_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1439_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1692_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
if (lean_obj_tag(v_a_1440_) == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
v___x_1444_ = lean_box(0);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v___x_1444_);
v___x_1446_ = v___x_1442_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v___x_1444_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
else
{
lean_object* v_val_1448_; uint8_t v___x_1449_; 
lean_del_object(v___x_1442_);
v_val_1448_ = lean_ctor_get(v_a_1440_, 0);
lean_inc(v_val_1448_);
lean_dec_ref(v_a_1440_);
v___x_1449_ = lean_unbox(v_val_1448_);
if (v___x_1449_ == 0)
{
lean_object* v___x_1450_; 
v___x_1450_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst(v_arg_1279_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1582_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1582_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1582_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
if (lean_obj_tag(v_a_1451_) == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1457_; 
lean_dec(v_val_1448_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
v___x_1455_ = lean_box(0);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1455_);
v___x_1457_ = v___x_1453_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1455_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
else
{
lean_object* v_val_1459_; uint8_t v___x_1460_; 
v_val_1459_ = lean_ctor_get(v_a_1451_, 0);
lean_inc(v_val_1459_);
lean_dec_ref(v_a_1451_);
v___x_1460_ = lean_unbox(v_val_1459_);
lean_dec(v_val_1459_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1463_; 
lean_dec(v_val_1448_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
v___x_1461_ = lean_box(0);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1461_);
v___x_1463_ = v___x_1453_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1461_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
else
{
lean_object* v___x_1465_; 
lean_del_object(v___x_1453_);
lean_inc_ref(v_arg_1276_);
v___x_1465_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1276_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1466_);
if (lean_obj_tag(v_a_1466_) == 0)
{
lean_dec(v_val_1448_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
return v___x_1465_;
}
else
{
lean_object* v_val_1467_; lean_object* v_fst_1468_; lean_object* v_snd_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1581_; 
lean_dec_ref(v___x_1465_);
v_val_1467_ = lean_ctor_get(v_a_1466_, 0);
lean_inc(v_val_1467_);
lean_dec_ref(v_a_1466_);
v_fst_1468_ = lean_ctor_get(v_val_1467_, 0);
v_snd_1469_ = lean_ctor_get(v_val_1467_, 1);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_val_1467_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1471_ = v_val_1467_;
v_isShared_1472_ = v_isSharedCheck_1581_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_snd_1469_);
lean_inc(v_fst_1468_);
lean_dec(v_val_1467_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1581_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_Meta_getIntValue_x3f(v_arg_1273_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1572_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1476_ = v___x_1473_;
v_isShared_1477_ = v_isSharedCheck_1572_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1572_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
if (lean_obj_tag(v_a_1474_) == 1)
{
lean_object* v_val_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1567_; 
lean_del_object(v___x_1476_);
v_val_1478_ = lean_ctor_get(v_a_1474_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_a_1474_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1480_ = v_a_1474_;
v_isShared_1481_ = v_isSharedCheck_1567_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_val_1478_);
lean_dec(v_a_1474_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1567_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; uint8_t v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = lean_nat_abs(v_val_1478_);
v___x_1483_ = lean_unbox(v_val_1448_);
lean_dec(v_val_1448_);
v___x_1484_ = l_Lean_checkExponent(v___x_1482_, v___x_1483_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1558_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1558_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1558_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
uint8_t v___x_1489_; 
v___x_1489_ = lean_unbox(v_a_1485_);
lean_dec(v_a_1485_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1492_; 
lean_del_object(v___x_1480_);
lean_dec(v_val_1478_);
lean_del_object(v___x_1471_);
lean_dec(v_snd_1469_);
lean_dec(v_fst_1468_);
lean_dec_ref(v_arg_1276_);
v___x_1490_ = lean_box(0);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v___x_1490_);
v___x_1492_ = v___x_1487_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
else
{
lean_object* v_u_1494_; lean_object* v_type_1495_; lean_object* v_fieldInst_1496_; lean_object* v_isChar0Inst_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1534_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v_u_1494_ = lean_ctor_get(v_a_1255_, 0);
v_type_1495_ = lean_ctor_get(v_a_1255_, 1);
v_fieldInst_1496_ = lean_ctor_get(v_a_1255_, 2);
v_isChar0Inst_1497_ = lean_ctor_get(v_a_1255_, 3);
lean_inc(v_fst_1468_);
v___x_1498_ = l_Rat_zpow(v_fst_1468_, v_val_1478_);
v___x_1499_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34));
v___x_1500_ = lean_box(0);
lean_inc(v_u_1494_);
v___x_1501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1501_, 0, v_u_1494_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
v___x_1502_ = l_Lean_mkConst(v___x_1499_, v___x_1501_);
v___x_1547_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35);
v___x_1548_ = lean_int_dec_le(v___x_1547_, v_val_1478_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1549_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36);
v___x_1550_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39);
v___x_1551_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42);
v___x_1552_ = lean_int_neg(v_val_1478_);
lean_dec(v_val_1478_);
v___x_1553_ = l_Int_toNat(v___x_1552_);
lean_dec(v___x_1552_);
v___x_1554_ = l_Lean_instToExprInt_mkNat(v___x_1553_);
v___x_1555_ = l_Lean_mkApp3(v___x_1549_, v___x_1550_, v___x_1551_, v___x_1554_);
v___y_1534_ = v___x_1555_;
goto v___jp_1533_;
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = l_Int_toNat(v_val_1478_);
lean_dec(v_val_1478_);
v___x_1557_ = l_Lean_instToExprInt_mkNat(v___x_1556_);
v___y_1534_ = v___x_1557_;
goto v___jp_1533_;
}
v___jp_1503_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1507_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_isChar0Inst_1497_);
lean_inc_ref(v_fieldInst_1496_);
lean_inc_ref(v_type_1495_);
v___x_1508_ = l_Lean_mkApp9(v___x_1502_, v_type_1495_, v_fieldInst_1496_, v_isChar0Inst_1497_, v_arg_1276_, v___y_1504_, v___y_1505_, v___y_1506_, v___x_1507_, v_snd_1469_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 1, v___x_1508_);
lean_ctor_set(v___x_1471_, 0, v___x_1498_);
v___x_1510_ = v___x_1471_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v___x_1508_);
v___x_1510_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1512_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 0, v___x_1510_);
v___x_1512_ = v___x_1480_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1514_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v___x_1512_);
v___x_1514_ = v___x_1487_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
v___jp_1518_:
{
lean_object* v_num_1521_; lean_object* v_den_1522_; lean_object* v___x_1523_; uint8_t v___x_1524_; 
v_num_1521_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_num_1521_);
v_den_1522_ = lean_ctor_get(v___x_1498_, 1);
lean_inc(v_den_1522_);
v___x_1523_ = lean_unsigned_to_nat(1u);
v___x_1524_ = lean_nat_dec_eq(v_den_1522_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1525_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_1526_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_1527_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_1528_ = l_Lean_instToExprRat_mkInt(v_num_1521_);
lean_dec(v_num_1521_);
v___x_1529_ = lean_nat_to_int(v_den_1522_);
v___x_1530_ = l_Lean_instToExprRat_mkInt(v___x_1529_);
lean_dec(v___x_1529_);
v___x_1531_ = l_Lean_mkApp6(v___x_1525_, v___x_1526_, v___x_1526_, v___x_1526_, v___x_1527_, v___x_1528_, v___x_1530_);
v___y_1504_ = v___y_1519_;
v___y_1505_ = v___y_1520_;
v___y_1506_ = v___x_1531_;
goto v___jp_1503_;
}
else
{
lean_object* v___x_1532_; 
lean_dec(v_den_1522_);
v___x_1532_ = l_Lean_instToExprRat_mkInt(v_num_1521_);
lean_dec(v_num_1521_);
v___y_1504_ = v___y_1519_;
v___y_1505_ = v___y_1520_;
v___y_1506_ = v___x_1532_;
goto v___jp_1503_;
}
}
v___jp_1533_:
{
lean_object* v_num_1535_; lean_object* v_den_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v_num_1535_ = lean_ctor_get(v_fst_1468_, 0);
lean_inc(v_num_1535_);
v_den_1536_ = lean_ctor_get(v_fst_1468_, 1);
lean_inc(v_den_1536_);
lean_dec(v_fst_1468_);
v___x_1537_ = lean_unsigned_to_nat(1u);
v___x_1538_ = lean_nat_dec_eq(v_den_1536_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1539_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_1540_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_1541_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_1542_ = l_Lean_instToExprRat_mkInt(v_num_1535_);
lean_dec(v_num_1535_);
v___x_1543_ = lean_nat_to_int(v_den_1536_);
v___x_1544_ = l_Lean_instToExprRat_mkInt(v___x_1543_);
lean_dec(v___x_1543_);
v___x_1545_ = l_Lean_mkApp6(v___x_1539_, v___x_1540_, v___x_1540_, v___x_1540_, v___x_1541_, v___x_1542_, v___x_1544_);
v___y_1519_ = v___y_1534_;
v___y_1520_ = v___x_1545_;
goto v___jp_1518_;
}
else
{
lean_object* v___x_1546_; 
lean_dec(v_den_1536_);
v___x_1546_ = l_Lean_instToExprRat_mkInt(v_num_1535_);
lean_dec(v_num_1535_);
v___y_1519_ = v___y_1534_;
v___y_1520_ = v___x_1546_;
goto v___jp_1518_;
}
}
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_del_object(v___x_1480_);
lean_dec(v_val_1478_);
lean_del_object(v___x_1471_);
lean_dec(v_snd_1469_);
lean_dec(v_fst_1468_);
lean_dec_ref(v_arg_1276_);
v_a_1559_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1484_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1484_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1570_; 
lean_dec(v_a_1474_);
lean_del_object(v___x_1471_);
lean_dec(v_snd_1469_);
lean_dec(v_fst_1468_);
lean_dec(v_val_1448_);
lean_dec_ref(v_arg_1276_);
v___x_1568_ = lean_box(0);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v___x_1568_);
v___x_1570_ = v___x_1476_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_del_object(v___x_1471_);
lean_dec(v_snd_1469_);
lean_dec(v_fst_1468_);
lean_dec(v_val_1448_);
lean_dec_ref(v_arg_1276_);
v_a_1573_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1473_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1473_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
}
else
{
lean_dec(v_val_1448_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
return v___x_1465_;
}
}
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec(v_val_1448_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
v_a_1583_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1450_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1450_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
else
{
lean_object* v___x_1591_; 
lean_dec(v_val_1448_);
lean_dec_ref(v_arg_1279_);
lean_inc_ref(v_arg_1276_);
v___x_1591_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1276_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
if (lean_obj_tag(v_a_1592_) == 0)
{
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
return v___x_1591_;
}
else
{
lean_object* v_val_1593_; lean_object* v_fst_1594_; lean_object* v_snd_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1691_; 
lean_dec_ref(v___x_1591_);
v_val_1593_ = lean_ctor_get(v_a_1592_, 0);
lean_inc(v_val_1593_);
lean_dec_ref(v_a_1592_);
v_fst_1594_ = lean_ctor_get(v_val_1593_, 0);
v_snd_1595_ = lean_ctor_get(v_val_1593_, 1);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_val_1593_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1597_ = v_val_1593_;
v_isShared_1598_ = v_isSharedCheck_1691_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_snd_1595_);
lean_inc(v_fst_1594_);
lean_dec(v_val_1593_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1691_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_Meta_getNatValue_x3f(v_arg_1273_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
lean_dec_ref(v_arg_1273_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1682_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1602_ = v___x_1599_;
v_isShared_1603_ = v_isSharedCheck_1682_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1599_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1682_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
if (lean_obj_tag(v_a_1600_) == 1)
{
lean_object* v_val_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1677_; 
lean_del_object(v___x_1602_);
v_val_1604_ = lean_ctor_get(v_a_1600_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_a_1600_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1606_ = v_a_1600_;
v_isShared_1607_ = v_isSharedCheck_1677_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_val_1604_);
lean_dec(v_a_1600_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1677_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; 
lean_inc(v_val_1604_);
v___x_1608_ = l_Lean_checkExponent(v_val_1604_, v___x_1290_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1668_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1611_ = v___x_1608_;
v_isShared_1612_ = v_isSharedCheck_1668_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1668_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
uint8_t v___x_1613_; 
v___x_1613_ = lean_unbox(v_a_1609_);
lean_dec(v_a_1609_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; lean_object* v___x_1616_; 
lean_del_object(v___x_1606_);
lean_dec(v_val_1604_);
lean_del_object(v___x_1597_);
lean_dec(v_snd_1595_);
lean_dec(v_fst_1594_);
lean_dec_ref(v_arg_1276_);
v___x_1614_ = lean_box(0);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 0, v___x_1614_);
v___x_1616_ = v___x_1611_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
else
{
lean_object* v_u_1618_; lean_object* v_type_1619_; lean_object* v_fieldInst_1620_; lean_object* v_isChar0Inst_1621_; lean_object* v_num_1622_; lean_object* v_den_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___y_1645_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v_u_1618_ = lean_ctor_get(v_a_1255_, 0);
v_type_1619_ = lean_ctor_get(v_a_1255_, 1);
v_fieldInst_1620_ = lean_ctor_get(v_a_1255_, 2);
v_isChar0Inst_1621_ = lean_ctor_get(v_a_1255_, 3);
v_num_1622_ = lean_ctor_get(v_fst_1594_, 0);
lean_inc(v_num_1622_);
v_den_1623_ = lean_ctor_get(v_fst_1594_, 1);
lean_inc(v_den_1623_);
v___x_1624_ = l_Rat_pow(v_fst_1594_, v_val_1604_);
v___x_1625_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44));
v___x_1626_ = lean_box(0);
lean_inc(v_u_1618_);
v___x_1627_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1627_, 0, v_u_1618_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = l_Lean_mkConst(v___x_1625_, v___x_1627_);
v___x_1629_ = l_Lean_mkNatLit(v_val_1604_);
v___x_1658_ = lean_unsigned_to_nat(1u);
v___x_1659_ = lean_nat_dec_eq(v_den_1623_, v___x_1658_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1660_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_1661_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_1662_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_1663_ = l_Lean_instToExprRat_mkInt(v_num_1622_);
lean_dec(v_num_1622_);
v___x_1664_ = lean_nat_to_int(v_den_1623_);
v___x_1665_ = l_Lean_instToExprRat_mkInt(v___x_1664_);
lean_dec(v___x_1664_);
v___x_1666_ = l_Lean_mkApp6(v___x_1660_, v___x_1661_, v___x_1661_, v___x_1661_, v___x_1662_, v___x_1663_, v___x_1665_);
v___y_1645_ = v___x_1666_;
goto v___jp_1644_;
}
else
{
lean_object* v___x_1667_; 
lean_dec(v_den_1623_);
v___x_1667_ = l_Lean_instToExprRat_mkInt(v_num_1622_);
lean_dec(v_num_1622_);
v___y_1645_ = v___x_1667_;
goto v___jp_1644_;
}
v___jp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1633_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_isChar0Inst_1621_);
lean_inc_ref(v_fieldInst_1620_);
lean_inc_ref(v_type_1619_);
v___x_1634_ = l_Lean_mkApp9(v___x_1628_, v_type_1619_, v_fieldInst_1620_, v_isChar0Inst_1621_, v_arg_1276_, v___x_1629_, v___y_1631_, v___y_1632_, v___x_1633_, v_snd_1595_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 1, v___x_1634_);
lean_ctor_set(v___x_1597_, 0, v___x_1624_);
v___x_1636_ = v___x_1597_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
lean_object* v___x_1638_; 
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1636_);
v___x_1638_ = v___x_1606_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
lean_object* v___x_1640_; 
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 0, v___x_1638_);
v___x_1640_ = v___x_1611_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1638_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
v___jp_1644_:
{
lean_object* v_num_1646_; lean_object* v_den_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; 
v_num_1646_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_num_1646_);
v_den_1647_ = lean_ctor_get(v___x_1624_, 1);
lean_inc(v_den_1647_);
v___x_1648_ = lean_unsigned_to_nat(1u);
v___x_1649_ = lean_nat_dec_eq(v_den_1647_, v___x_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1650_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_1651_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_1652_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_1653_ = l_Lean_instToExprRat_mkInt(v_num_1646_);
lean_dec(v_num_1646_);
v___x_1654_ = lean_nat_to_int(v_den_1647_);
v___x_1655_ = l_Lean_instToExprRat_mkInt(v___x_1654_);
lean_dec(v___x_1654_);
v___x_1656_ = l_Lean_mkApp6(v___x_1650_, v___x_1651_, v___x_1651_, v___x_1651_, v___x_1652_, v___x_1653_, v___x_1655_);
v___y_1631_ = v___y_1645_;
v___y_1632_ = v___x_1656_;
goto v___jp_1630_;
}
else
{
lean_object* v___x_1657_; 
lean_dec(v_den_1647_);
v___x_1657_ = l_Lean_instToExprRat_mkInt(v_num_1646_);
lean_dec(v_num_1646_);
v___y_1631_ = v___y_1645_;
v___y_1632_ = v___x_1657_;
goto v___jp_1630_;
}
}
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_del_object(v___x_1606_);
lean_dec(v_val_1604_);
lean_del_object(v___x_1597_);
lean_dec(v_snd_1595_);
lean_dec(v_fst_1594_);
lean_dec_ref(v_arg_1276_);
v_a_1669_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1608_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1608_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
lean_dec(v_a_1600_);
lean_del_object(v___x_1597_);
lean_dec(v_snd_1595_);
lean_dec(v_fst_1594_);
lean_dec_ref(v_arg_1276_);
v___x_1678_ = lean_box(0);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v___x_1678_);
v___x_1680_ = v___x_1602_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_del_object(v___x_1597_);
lean_dec(v_snd_1595_);
lean_dec(v_fst_1594_);
lean_dec_ref(v_arg_1276_);
v_a_1683_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1599_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1599_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
return v___x_1591_;
}
}
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
lean_dec_ref(v_arg_1273_);
v_a_1693_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1439_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1439_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
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
lean_object* v___x_1701_; 
lean_dec_ref(v___x_1280_);
lean_dec_ref(v_arg_1279_);
lean_del_object(v___x_1264_);
v___x_1701_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst(v_arg_1276_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1722_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1704_ = v___x_1701_;
v_isShared_1705_ = v_isSharedCheck_1722_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1701_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1722_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
if (lean_obj_tag(v_a_1702_) == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
lean_dec_ref(v_arg_1273_);
v___x_1706_ = lean_box(0);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v___x_1706_);
v___x_1708_ = v___x_1704_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
else
{
lean_object* v_val_1710_; uint8_t v___x_1711_; 
v_val_1710_ = lean_ctor_get(v_a_1702_, 0);
lean_inc(v_val_1710_);
lean_dec_ref(v_a_1702_);
v___x_1711_ = lean_unbox(v_val_1710_);
lean_dec(v_val_1710_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1714_; 
lean_dec_ref(v_arg_1273_);
v___x_1712_ = lean_box(0);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v___x_1712_);
v___x_1714_ = v___x_1704_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
else
{
lean_object* v___x_1716_; 
lean_del_object(v___x_1704_);
lean_inc_ref(v_arg_1273_);
v___x_1716_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1273_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1717_);
if (lean_obj_tag(v_a_1717_) == 0)
{
lean_dec_ref(v_arg_1273_);
return v___x_1716_;
}
else
{
lean_object* v_val_1718_; lean_object* v___f_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_dec_ref(v___x_1716_);
v_val_1718_ = lean_ctor_get(v_a_1717_, 0);
lean_inc(v_val_1718_);
lean_dec_ref(v_a_1717_);
v___f_1719_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__45));
v___x_1720_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47));
v___x_1721_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(v___x_1720_, v_arg_1273_, v_val_1718_, v___f_1719_, v_a_1255_);
return v___x_1721_;
}
}
else
{
lean_dec_ref(v_arg_1273_);
return v___x_1716_;
}
}
}
}
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec_ref(v_arg_1273_);
v_a_1723_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1701_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1701_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
}
else
{
lean_object* v___x_1731_; 
lean_dec_ref(v___x_1280_);
lean_dec_ref(v_arg_1279_);
lean_del_object(v___x_1264_);
v___x_1731_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst(v_arg_1276_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1752_; 
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1734_ = v___x_1731_;
v_isShared_1735_ = v_isSharedCheck_1752_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1731_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1752_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
if (lean_obj_tag(v_a_1732_) == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1738_; 
lean_dec_ref(v_arg_1273_);
v___x_1736_ = lean_box(0);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v___x_1736_);
v___x_1738_ = v___x_1734_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
else
{
lean_object* v_val_1740_; uint8_t v___x_1741_; 
v_val_1740_ = lean_ctor_get(v_a_1732_, 0);
lean_inc(v_val_1740_);
lean_dec_ref(v_a_1732_);
v___x_1741_ = lean_unbox(v_val_1740_);
lean_dec(v_val_1740_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; lean_object* v___x_1744_; 
lean_dec_ref(v_arg_1273_);
v___x_1742_ = lean_box(0);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v___x_1742_);
v___x_1744_ = v___x_1734_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
else
{
lean_object* v___x_1746_; 
lean_del_object(v___x_1734_);
lean_inc_ref(v_arg_1273_);
v___x_1746_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1273_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
if (lean_obj_tag(v_a_1747_) == 0)
{
lean_dec_ref(v_arg_1273_);
return v___x_1746_;
}
else
{
lean_object* v_val_1748_; lean_object* v___f_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
lean_dec_ref(v___x_1746_);
v_val_1748_ = lean_ctor_get(v_a_1747_, 0);
lean_inc(v_val_1748_);
lean_dec_ref(v_a_1747_);
v___f_1749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48));
v___x_1750_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50));
v___x_1751_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(v___x_1750_, v_arg_1273_, v_val_1748_, v___f_1749_, v_a_1255_);
return v___x_1751_;
}
}
else
{
lean_dec_ref(v_arg_1273_);
return v___x_1746_;
}
}
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec_ref(v_arg_1273_);
v_a_1753_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1731_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1731_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
else
{
lean_object* v___x_1761_; 
lean_dec_ref(v___x_1280_);
lean_dec_ref(v_arg_1279_);
lean_del_object(v___x_1264_);
lean_inc_ref(v_arg_1276_);
v___x_1761_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst(v_arg_1273_, v_arg_1276_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1816_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1764_ = v___x_1761_;
v_isShared_1765_ = v_isSharedCheck_1816_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1761_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1816_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
if (lean_obj_tag(v_a_1762_) == 0)
{
lean_object* v___x_1766_; lean_object* v___x_1768_; 
lean_dec_ref(v_arg_1276_);
v___x_1766_ = lean_box(0);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v___x_1766_);
v___x_1768_ = v___x_1764_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
else
{
lean_object* v_val_1770_; uint8_t v___x_1771_; 
v_val_1770_ = lean_ctor_get(v_a_1762_, 0);
lean_inc(v_val_1770_);
lean_dec_ref(v_a_1762_);
v___x_1771_ = lean_unbox(v_val_1770_);
lean_dec(v_val_1770_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
lean_dec_ref(v_arg_1276_);
v___x_1772_ = lean_box(0);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 0, v___x_1772_);
v___x_1774_ = v___x_1764_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
else
{
lean_object* v___x_1776_; 
lean_del_object(v___x_1764_);
v___x_1776_ = l_Lean_Meta_getNatValue_x3f(v_arg_1276_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
lean_dec_ref(v_arg_1276_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1807_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1779_ = v___x_1776_;
v_isShared_1780_ = v_isSharedCheck_1807_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1807_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
if (lean_obj_tag(v_a_1777_) == 1)
{
lean_object* v_val_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1802_; 
v_val_1781_ = lean_ctor_get(v_a_1777_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v_a_1777_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1783_ = v_a_1777_;
v_isShared_1784_ = v_isSharedCheck_1802_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_val_1781_);
lean_dec(v_a_1777_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1802_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v_u_1785_; lean_object* v_type_1786_; lean_object* v_fieldInst_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1797_; 
v_u_1785_ = lean_ctor_get(v_a_1255_, 0);
v_type_1786_ = lean_ctor_get(v_a_1255_, 1);
v_fieldInst_1787_ = lean_ctor_get(v_a_1255_, 2);
v___x_1788_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52));
v___x_1789_ = lean_box(0);
lean_inc(v_u_1785_);
v___x_1790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1790_, 0, v_u_1785_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
v___x_1791_ = l_Lean_mkConst(v___x_1788_, v___x_1790_);
lean_inc(v_val_1781_);
v___x_1792_ = l_Lean_mkNatLit(v_val_1781_);
lean_inc_ref(v_fieldInst_1787_);
lean_inc_ref(v_type_1786_);
v___x_1793_ = l_Lean_mkApp3(v___x_1791_, v_type_1786_, v_fieldInst_1787_, v___x_1792_);
v___x_1794_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval_spec__0(v_val_1781_);
v___x_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1795_, 0, v___x_1794_);
lean_ctor_set(v___x_1795_, 1, v___x_1793_);
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v___x_1795_);
v___x_1797_ = v___x_1783_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1795_);
v___x_1797_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1799_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1797_);
v___x_1799_ = v___x_1779_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
else
{
lean_object* v___x_1803_; lean_object* v___x_1805_; 
lean_dec(v_a_1777_);
v___x_1803_ = lean_box(0);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1803_);
v___x_1805_ = v___x_1779_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
v_a_1808_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1776_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1776_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_dec_ref(v_arg_1276_);
v_a_1817_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1761_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1761_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
}
else
{
lean_object* v___x_1825_; 
lean_dec_ref(v___x_1280_);
lean_dec_ref(v_arg_1279_);
lean_del_object(v___x_1264_);
v___x_1825_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNatCastInst(v_arg_1276_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1880_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1828_ = v___x_1825_;
v_isShared_1829_ = v_isSharedCheck_1880_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1825_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1880_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
if (lean_obj_tag(v_a_1826_) == 0)
{
lean_object* v___x_1830_; lean_object* v___x_1832_; 
lean_dec_ref(v_arg_1273_);
v___x_1830_ = lean_box(0);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1830_);
v___x_1832_ = v___x_1828_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1830_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
else
{
lean_object* v_val_1834_; uint8_t v___x_1835_; 
v_val_1834_ = lean_ctor_get(v_a_1826_, 0);
lean_inc(v_val_1834_);
lean_dec_ref(v_a_1826_);
v___x_1835_ = lean_unbox(v_val_1834_);
lean_dec(v_val_1834_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1838_; 
lean_dec_ref(v_arg_1273_);
v___x_1836_ = lean_box(0);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1836_);
v___x_1838_ = v___x_1828_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
else
{
lean_object* v___x_1840_; 
lean_del_object(v___x_1828_);
v___x_1840_ = l_Lean_Meta_getNatValue_x3f(v_arg_1273_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
lean_dec_ref(v_arg_1273_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1871_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1871_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1871_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
if (lean_obj_tag(v_a_1841_) == 1)
{
lean_object* v_val_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1866_; 
v_val_1845_ = lean_ctor_get(v_a_1841_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v_a_1841_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1847_ = v_a_1841_;
v_isShared_1848_ = v_isSharedCheck_1866_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_val_1845_);
lean_dec(v_a_1841_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1866_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v_u_1849_; lean_object* v_type_1850_; lean_object* v_fieldInst_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1861_; 
v_u_1849_ = lean_ctor_get(v_a_1255_, 0);
v_type_1850_ = lean_ctor_get(v_a_1255_, 1);
v_fieldInst_1851_ = lean_ctor_get(v_a_1255_, 2);
v___x_1852_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54));
v___x_1853_ = lean_box(0);
lean_inc(v_u_1849_);
v___x_1854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1854_, 0, v_u_1849_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = l_Lean_mkConst(v___x_1852_, v___x_1854_);
lean_inc(v_val_1845_);
v___x_1856_ = l_Lean_mkNatLit(v_val_1845_);
lean_inc_ref(v_fieldInst_1851_);
lean_inc_ref(v_type_1850_);
v___x_1857_ = l_Lean_mkApp3(v___x_1855_, v_type_1850_, v_fieldInst_1851_, v___x_1856_);
v___x_1858_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval_spec__0(v_val_1845_);
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
lean_ctor_set(v___x_1859_, 1, v___x_1857_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v___x_1859_);
v___x_1861_ = v___x_1847_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1863_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1861_);
v___x_1863_ = v___x_1843_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
else
{
lean_object* v___x_1867_; lean_object* v___x_1869_; 
lean_dec(v_a_1841_);
v___x_1867_ = lean_box(0);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1867_);
v___x_1869_ = v___x_1843_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
v_a_1872_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1840_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1840_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec_ref(v_arg_1273_);
v_a_1881_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1825_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1825_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
}
else
{
lean_object* v___x_1889_; 
lean_dec_ref(v___x_1280_);
lean_dec_ref(v_arg_1279_);
lean_del_object(v___x_1264_);
v___x_1889_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isIntCastInst(v_arg_1276_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1956_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1892_ = v___x_1889_;
v_isShared_1893_ = v_isSharedCheck_1956_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1889_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1956_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
if (lean_obj_tag(v_a_1890_) == 0)
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
lean_dec_ref(v_arg_1273_);
v___x_1894_ = lean_box(0);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v___x_1894_);
v___x_1896_ = v___x_1892_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
else
{
lean_object* v_val_1898_; uint8_t v___x_1899_; 
v_val_1898_ = lean_ctor_get(v_a_1890_, 0);
lean_inc(v_val_1898_);
lean_dec_ref(v_a_1890_);
v___x_1899_ = lean_unbox(v_val_1898_);
lean_dec(v_val_1898_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; lean_object* v___x_1902_; 
lean_dec_ref(v_arg_1273_);
v___x_1900_ = lean_box(0);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v___x_1900_);
v___x_1902_ = v___x_1892_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1900_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
else
{
lean_object* v___x_1904_; 
lean_del_object(v___x_1892_);
v___x_1904_ = l_Lean_Meta_getIntValue_x3f(v_arg_1273_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1947_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1947_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1947_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
if (lean_obj_tag(v_a_1905_) == 1)
{
lean_object* v_val_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1942_; 
v_val_1909_ = lean_ctor_get(v_a_1905_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_a_1905_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1911_ = v_a_1905_;
v_isShared_1912_ = v_isSharedCheck_1942_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_val_1909_);
lean_dec(v_a_1905_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1942_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v_u_1913_; lean_object* v_type_1914_; lean_object* v_fieldInst_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___y_1921_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v_u_1913_ = lean_ctor_get(v_a_1255_, 0);
v_type_1914_ = lean_ctor_get(v_a_1255_, 1);
v_fieldInst_1915_ = lean_ctor_get(v_a_1255_, 2);
v___x_1916_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56));
v___x_1917_ = lean_box(0);
lean_inc(v_u_1913_);
v___x_1918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1918_, 0, v_u_1913_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = l_Lean_mkConst(v___x_1916_, v___x_1918_);
v___x_1931_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35);
v___x_1932_ = lean_int_dec_le(v___x_1931_, v_val_1909_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1933_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36);
v___x_1934_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39);
v___x_1935_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42);
v___x_1936_ = lean_int_neg(v_val_1909_);
v___x_1937_ = l_Int_toNat(v___x_1936_);
lean_dec(v___x_1936_);
v___x_1938_ = l_Lean_instToExprInt_mkNat(v___x_1937_);
v___x_1939_ = l_Lean_mkApp3(v___x_1933_, v___x_1934_, v___x_1935_, v___x_1938_);
v___y_1921_ = v___x_1939_;
goto v___jp_1920_;
}
else
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = l_Int_toNat(v_val_1909_);
v___x_1941_ = l_Lean_instToExprInt_mkNat(v___x_1940_);
v___y_1921_ = v___x_1941_;
goto v___jp_1920_;
}
v___jp_1920_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1926_; 
lean_inc_ref(v_fieldInst_1915_);
lean_inc_ref(v_type_1914_);
v___x_1922_ = l_Lean_mkApp3(v___x_1919_, v_type_1914_, v_fieldInst_1915_, v___y_1921_);
v___x_1923_ = l_Rat_ofInt(v_val_1909_);
v___x_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
lean_ctor_set(v___x_1924_, 1, v___x_1922_);
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 0, v___x_1924_);
v___x_1926_ = v___x_1911_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1928_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1926_);
v___x_1928_ = v___x_1907_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
}
else
{
lean_object* v___x_1943_; lean_object* v___x_1945_; 
lean_dec(v_a_1905_);
v___x_1943_ = lean_box(0);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1943_);
v___x_1945_ = v___x_1907_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
v_a_1948_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1904_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1904_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v___x_1953_; 
if (v_isShared_1951_ == 0)
{
v___x_1953_ = v___x_1950_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec_ref(v_arg_1273_);
v_a_1957_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1889_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1889_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
}
}
}
v___jp_1266_:
{
lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1267_ = lean_box(0);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1267_);
v___x_1269_ = v___x_1264_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
v_a_1966_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1261_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1261_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___boxed(lean_object* v_e_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_e_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
lean_dec(v_a_1977_);
lean_dec_ref(v_a_1976_);
lean_dec_ref(v_a_1975_);
return v_res_1981_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(lean_object* v_e_1982_){
_start:
{
lean_object* v_a_1984_; lean_object* v_b_1985_; lean_object* v___x_1988_; uint8_t v___x_1989_; 
v___x_1988_ = l_Lean_Expr_cleanupAnnotations(v_e_1982_);
v___x_1989_ = l_Lean_Expr_isApp(v___x_1988_);
if (v___x_1989_ == 0)
{
lean_dec_ref(v___x_1988_);
return v___x_1989_;
}
else
{
lean_object* v_arg_1990_; lean_object* v___x_1991_; uint8_t v___x_1992_; 
v_arg_1990_ = lean_ctor_get(v___x_1988_, 1);
lean_inc_ref(v_arg_1990_);
v___x_1991_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1988_);
v___x_1992_ = l_Lean_Expr_isApp(v___x_1991_);
if (v___x_1992_ == 0)
{
lean_dec_ref(v___x_1991_);
lean_dec_ref(v_arg_1990_);
return v___x_1992_;
}
else
{
lean_object* v_arg_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v_arg_1993_ = lean_ctor_get(v___x_1991_, 1);
lean_inc_ref(v_arg_1993_);
v___x_1994_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1991_);
v___x_1995_ = l_Lean_Expr_isApp(v___x_1994_);
if (v___x_1995_ == 0)
{
lean_dec_ref(v___x_1994_);
lean_dec_ref(v_arg_1993_);
lean_dec_ref(v_arg_1990_);
return v___x_1995_;
}
else
{
lean_object* v___x_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
v___x_1996_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1994_);
v___x_1997_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1));
v___x_1998_ = l_Lean_Expr_isConstOf(v___x_1996_, v___x_1997_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; uint8_t v___x_2000_; 
v___x_1999_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1));
v___x_2000_ = l_Lean_Expr_isConstOf(v___x_1996_, v___x_1999_);
if (v___x_2000_ == 0)
{
lean_object* v___x_2001_; uint8_t v___x_2002_; 
v___x_2001_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__1));
v___x_2002_ = l_Lean_Expr_isConstOf(v___x_1996_, v___x_2001_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; uint8_t v___x_2004_; 
v___x_2003_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4));
v___x_2004_ = l_Lean_Expr_isConstOf(v___x_1996_, v___x_2003_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; uint8_t v___x_2006_; 
v___x_2005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7));
v___x_2006_ = l_Lean_Expr_isConstOf(v___x_1996_, v___x_2005_);
if (v___x_2006_ == 0)
{
uint8_t v___x_2007_; 
v___x_2007_ = l_Lean_Expr_isApp(v___x_1996_);
if (v___x_2007_ == 0)
{
lean_dec_ref(v___x_1996_);
lean_dec_ref(v_arg_1993_);
lean_dec_ref(v_arg_1990_);
return v___x_2007_;
}
else
{
lean_object* v___x_2008_; uint8_t v___x_2009_; 
v___x_2008_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1996_);
v___x_2009_ = l_Lean_Expr_isApp(v___x_2008_);
if (v___x_2009_ == 0)
{
lean_dec_ref(v___x_2008_);
lean_dec_ref(v_arg_1993_);
lean_dec_ref(v_arg_1990_);
return v___x_2009_;
}
else
{
lean_object* v___x_2010_; uint8_t v___x_2011_; 
v___x_2010_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2008_);
v___x_2011_ = l_Lean_Expr_isApp(v___x_2010_);
if (v___x_2011_ == 0)
{
lean_dec_ref(v___x_2010_);
lean_dec_ref(v_arg_1993_);
lean_dec_ref(v_arg_1990_);
return v___x_2011_;
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2012_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2010_);
v___x_2013_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10));
v___x_2014_ = l_Lean_Expr_isConstOf(v___x_2012_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2015_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2));
v___x_2016_ = l_Lean_Expr_isConstOf(v___x_2012_, v___x_2015_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13));
v___x_2018_ = l_Lean_Expr_isConstOf(v___x_2012_, v___x_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; uint8_t v___x_2020_; 
v___x_2019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16));
v___x_2020_ = l_Lean_Expr_isConstOf(v___x_2012_, v___x_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19));
v___x_2022_ = l_Lean_Expr_isConstOf(v___x_2012_, v___x_2021_);
lean_dec_ref(v___x_2012_);
if (v___x_2022_ == 0)
{
lean_dec_ref(v_arg_1993_);
lean_dec_ref(v_arg_1990_);
return v___x_2022_;
}
else
{
v_a_1984_ = v_arg_1993_;
v_b_1985_ = v_arg_1990_;
goto v___jp_1983_;
}
}
else
{
lean_dec_ref(v___x_2012_);
v_a_1984_ = v_arg_1993_;
v_b_1985_ = v_arg_1990_;
goto v___jp_1983_;
}
}
else
{
lean_dec_ref(v___x_2012_);
v_a_1984_ = v_arg_1993_;
v_b_1985_ = v_arg_1990_;
goto v___jp_1983_;
}
}
else
{
lean_dec_ref(v___x_2012_);
v_a_1984_ = v_arg_1993_;
v_b_1985_ = v_arg_1990_;
goto v___jp_1983_;
}
}
else
{
lean_dec_ref(v___x_2012_);
v_a_1984_ = v_arg_1993_;
v_b_1985_ = v_arg_1990_;
goto v___jp_1983_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1996_);
lean_dec_ref(v_arg_1993_);
v_e_1982_ = v_arg_1990_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_1996_);
lean_dec_ref(v_arg_1993_);
v_e_1982_ = v_arg_1990_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_1996_);
lean_dec_ref(v_arg_1993_);
lean_dec_ref(v_arg_1990_);
return v___x_2002_;
}
}
else
{
lean_dec_ref(v___x_1996_);
lean_dec_ref(v_arg_1993_);
lean_dec_ref(v_arg_1990_);
return v___x_2000_;
}
}
else
{
lean_dec_ref(v___x_1996_);
lean_dec_ref(v_arg_1993_);
lean_dec_ref(v_arg_1990_);
return v___x_1998_;
}
}
}
}
v___jp_1983_:
{
uint8_t v___x_1986_; 
v___x_1986_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(v_a_1984_);
if (v___x_1986_ == 0)
{
lean_dec_ref(v_b_1985_);
return v___x_1986_;
}
else
{
v_e_1982_ = v_b_1985_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable___boxed(lean_object* v_e_2025_){
_start:
{
uint8_t v_res_2026_; lean_object* v_r_2027_; 
v_res_2026_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(v_e_2025_);
v_r_2027_ = lean_box(v_res_2026_);
return v_r_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalFieldExpr_x3f(lean_object* v_e_2028_, lean_object* v_type_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_){
_start:
{
uint8_t v___x_2035_; 
lean_inc_ref(v_e_2028_);
v___x_2035_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(v_e_2028_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_dec_ref(v_type_2029_);
lean_dec_ref(v_e_2028_);
v___x_2036_ = lean_box(0);
v___x_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
return v___x_2037_;
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___boxed), 7, 1);
lean_closure_set(v___x_2038_, 0, v_e_2028_);
v___x_2039_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg(v_type_2029_, v___x_2038_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_);
return v___x_2039_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalFieldExpr_x3f___boxed(lean_object* v_e_2040_, lean_object* v_type_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_Meta_Grind_Arith_evalFieldExpr_x3f(v_e_2040_, v_type_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
lean_dec(v_a_2045_);
lean_dec_ref(v_a_2044_);
lean_dec(v_a_2043_);
lean_dec_ref(v_a_2042_);
return v_res_2047_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = lean_unsigned_to_nat(1u);
v___x_2049_ = lean_nat_to_int(v___x_2048_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0(lean_object* v_e_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v___x_2078_; 
lean_inc_ref(v_e_2071_);
v___x_2078_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_e_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2328_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2328_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2328_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
if (lean_obj_tag(v_a_2079_) == 0)
{
lean_object* v___x_2083_; lean_object* v___x_2085_; 
lean_dec_ref(v_e_2071_);
v___x_2083_ = lean_box(0);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v___x_2083_);
v___x_2085_ = v___x_2081_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
else
{
lean_object* v_val_2087_; lean_object* v_fst_2088_; lean_object* v_snd_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2327_; 
lean_del_object(v___x_2081_);
v_val_2087_ = lean_ctor_get(v_a_2079_, 0);
lean_inc(v_val_2087_);
lean_dec_ref(v_a_2079_);
v_fst_2088_ = lean_ctor_get(v_val_2087_, 0);
v_snd_2089_ = lean_ctor_get(v_val_2087_, 1);
v_isSharedCheck_2327_ = !lean_is_exclusive(v_val_2087_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2091_ = v_val_2087_;
v_isShared_2092_ = v_isSharedCheck_2327_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_snd_2089_);
lean_inc(v_fst_2088_);
lean_dec(v_val_2087_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2327_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v_num_2093_; lean_object* v_den_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2326_; 
v_num_2093_ = lean_ctor_get(v_fst_2088_, 0);
v_den_2094_ = lean_ctor_get(v_fst_2088_, 1);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_fst_2088_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2096_ = v_fst_2088_;
v_isShared_2097_ = v_isSharedCheck_2326_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_den_2094_);
lean_inc(v_num_2093_);
lean_dec(v_fst_2088_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2326_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2098_; uint8_t v___x_2099_; 
v___x_2098_ = lean_unsigned_to_nat(1u);
v___x_2099_ = lean_nat_dec_eq(v_den_2094_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2100_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__0);
v___x_2101_ = lean_int_dec_eq(v_num_2093_, v___x_2100_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; 
v___x_2102_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast(v_num_2093_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v_val_2104_; lean_object* v___x_2105_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref(v___x_2102_);
v_val_2104_ = lean_ctor_get(v_a_2103_, 0);
lean_inc(v_val_2104_);
lean_dec(v_a_2103_);
lean_inc(v_den_2094_);
v___x_2105_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast(v_den_2094_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v_val_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2183_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref(v___x_2105_);
v_val_2107_ = lean_ctor_get(v_a_2106_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v_a_2106_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2109_ = v_a_2106_;
v_isShared_2110_ = v_isSharedCheck_2183_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_val_2107_);
lean_dec(v_a_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2183_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2111_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4));
v___x_2112_ = lean_mk_empty_array_with_capacity(v___x_2098_);
v___x_2113_ = lean_array_push(v___x_2112_, v_val_2107_);
v___x_2114_ = l_Lean_Meta_mkAppM(v___x_2111_, v___x_2113_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2116_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref(v___x_2114_);
v___x_2116_ = l_Lean_Meta_mkMul(v_val_2104_, v_a_2115_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2166_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2119_ = v___x_2116_;
v_isShared_2120_ = v_isSharedCheck_2166_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2166_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v_u_2121_; lean_object* v_type_2122_; lean_object* v_fieldInst_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2127_; 
v_u_2121_ = lean_ctor_get(v___y_2072_, 0);
v_type_2122_ = lean_ctor_get(v___y_2072_, 1);
v_fieldInst_2123_ = lean_ctor_get(v___y_2072_, 2);
v___x_2124_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2));
v___x_2125_ = lean_box(0);
lean_inc(v_u_2121_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set_tag(v___x_2096_, 1);
lean_ctor_set(v___x_2096_, 1, v___x_2125_);
lean_ctor_set(v___x_2096_, 0, v_u_2121_);
v___x_2127_ = v___x_2096_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_u_2121_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
lean_object* v___x_2128_; lean_object* v___y_2130_; lean_object* v___y_2131_; lean_object* v___y_2145_; 
v___x_2128_ = l_Lean_mkConst(v___x_2124_, v___x_2127_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2157_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_2158_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_2159_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_2160_ = l_Lean_instToExprRat_mkInt(v_num_2093_);
lean_inc(v_den_2094_);
v___x_2161_ = lean_nat_to_int(v_den_2094_);
v___x_2162_ = l_Lean_instToExprRat_mkInt(v___x_2161_);
lean_dec(v___x_2161_);
v___x_2163_ = l_Lean_mkApp6(v___x_2157_, v___x_2158_, v___x_2158_, v___x_2158_, v___x_2159_, v___x_2160_, v___x_2162_);
v___y_2145_ = v___x_2163_;
goto v___jp_2144_;
}
else
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_instToExprRat_mkInt(v_num_2093_);
v___y_2145_ = v___x_2164_;
goto v___jp_2144_;
}
v___jp_2129_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2136_; 
v___x_2132_ = l_Lean_mkNatLit(v_den_2094_);
v___x_2133_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_fieldInst_2123_);
lean_inc_ref(v_type_2122_);
v___x_2134_ = l_Lean_mkApp8(v___x_2128_, v_type_2122_, v_fieldInst_2123_, v_e_2071_, v___y_2130_, v___y_2131_, v___x_2132_, v___x_2133_, v_snd_2089_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 1, v___x_2134_);
lean_ctor_set(v___x_2091_, 0, v_a_2117_);
v___x_2136_ = v___x_2091_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2117_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
lean_object* v___x_2138_; 
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2136_);
v___x_2138_ = v___x_2109_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2140_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v___x_2138_);
v___x_2140_ = v___x_2119_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
v___jp_2144_:
{
lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2146_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35);
v___x_2147_ = lean_int_dec_le(v___x_2146_, v_num_2093_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2148_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36);
v___x_2149_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39);
v___x_2150_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42);
v___x_2151_ = lean_int_neg(v_num_2093_);
lean_dec(v_num_2093_);
v___x_2152_ = l_Int_toNat(v___x_2151_);
lean_dec(v___x_2151_);
v___x_2153_ = l_Lean_instToExprInt_mkNat(v___x_2152_);
v___x_2154_ = l_Lean_mkApp3(v___x_2148_, v___x_2149_, v___x_2150_, v___x_2153_);
v___y_2130_ = v___y_2145_;
v___y_2131_ = v___x_2154_;
goto v___jp_2129_;
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = l_Int_toNat(v_num_2093_);
lean_dec(v_num_2093_);
v___x_2156_ = l_Lean_instToExprInt_mkNat(v___x_2155_);
v___y_2130_ = v___y_2145_;
v___y_2131_ = v___x_2156_;
goto v___jp_2129_;
}
}
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_del_object(v___x_2109_);
lean_del_object(v___x_2096_);
lean_dec(v_den_2094_);
lean_dec(v_num_2093_);
lean_del_object(v___x_2091_);
lean_dec(v_snd_2089_);
lean_dec_ref(v_e_2071_);
v_a_2167_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2116_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2116_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_del_object(v___x_2109_);
lean_dec(v_val_2104_);
lean_del_object(v___x_2096_);
lean_dec(v_den_2094_);
lean_dec(v_num_2093_);
lean_del_object(v___x_2091_);
lean_dec(v_snd_2089_);
lean_dec_ref(v_e_2071_);
v_a_2175_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2114_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2114_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec(v_val_2104_);
lean_del_object(v___x_2096_);
lean_dec(v_den_2094_);
lean_dec(v_num_2093_);
lean_del_object(v___x_2091_);
lean_dec(v_snd_2089_);
lean_dec_ref(v_e_2071_);
v_a_2184_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2105_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2105_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_del_object(v___x_2096_);
lean_dec(v_den_2094_);
lean_dec(v_num_2093_);
lean_del_object(v___x_2091_);
lean_dec(v_snd_2089_);
lean_dec_ref(v_e_2071_);
v_a_2192_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2102_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2102_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
else
{
lean_object* v___x_2200_; 
lean_inc(v_den_2094_);
v___x_2200_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast(v_den_2094_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v_a_2201_; lean_object* v_val_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2254_; 
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref(v___x_2200_);
v_val_2202_ = lean_ctor_get(v_a_2201_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v_a_2201_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2204_ = v_a_2201_;
v_isShared_2205_ = v_isSharedCheck_2254_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_val_2202_);
lean_dec(v_a_2201_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2254_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2206_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4));
v___x_2207_ = lean_mk_empty_array_with_capacity(v___x_2098_);
v___x_2208_ = lean_array_push(v___x_2207_, v_val_2202_);
v___x_2209_ = l_Lean_Meta_mkAppM(v___x_2206_, v___x_2208_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2245_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2212_ = v___x_2209_;
v_isShared_2213_ = v_isSharedCheck_2245_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2209_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2245_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v_u_2214_; lean_object* v_type_2215_; lean_object* v_fieldInst_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2220_; 
v_u_2214_ = lean_ctor_get(v___y_2072_, 0);
v_type_2215_ = lean_ctor_get(v___y_2072_, 1);
v_fieldInst_2216_ = lean_ctor_get(v___y_2072_, 2);
v___x_2217_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4));
v___x_2218_ = lean_box(0);
lean_inc(v_u_2214_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set_tag(v___x_2096_, 1);
lean_ctor_set(v___x_2096_, 1, v___x_2218_);
lean_ctor_set(v___x_2096_, 0, v_u_2214_);
v___x_2220_ = v___x_2096_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_u_2214_);
lean_ctor_set(v_reuseFailAlloc_2244_, 1, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2221_; lean_object* v___y_2223_; 
v___x_2221_ = l_Lean_mkConst(v___x_2217_, v___x_2220_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2236_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_2237_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_2238_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_2239_ = l_Lean_instToExprRat_mkInt(v_num_2093_);
lean_dec(v_num_2093_);
lean_inc(v_den_2094_);
v___x_2240_ = lean_nat_to_int(v_den_2094_);
v___x_2241_ = l_Lean_instToExprRat_mkInt(v___x_2240_);
lean_dec(v___x_2240_);
v___x_2242_ = l_Lean_mkApp6(v___x_2236_, v___x_2237_, v___x_2237_, v___x_2237_, v___x_2238_, v___x_2239_, v___x_2241_);
v___y_2223_ = v___x_2242_;
goto v___jp_2222_;
}
else
{
lean_object* v___x_2243_; 
v___x_2243_ = l_Lean_instToExprRat_mkInt(v_num_2093_);
lean_dec(v_num_2093_);
v___y_2223_ = v___x_2243_;
goto v___jp_2222_;
}
v___jp_2222_:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2224_ = l_Lean_mkNatLit(v_den_2094_);
v___x_2225_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_fieldInst_2216_);
lean_inc_ref(v_type_2215_);
v___x_2226_ = l_Lean_mkApp7(v___x_2221_, v_type_2215_, v_fieldInst_2216_, v_e_2071_, v___y_2223_, v___x_2224_, v___x_2225_, v_snd_2089_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 1, v___x_2226_);
lean_ctor_set(v___x_2091_, 0, v_a_2210_);
v___x_2228_ = v___x_2091_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2210_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v___x_2226_);
v___x_2228_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
lean_object* v___x_2230_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2228_);
v___x_2230_ = v___x_2204_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2232_; 
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 0, v___x_2230_);
v___x_2232_ = v___x_2212_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2230_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_del_object(v___x_2204_);
lean_del_object(v___x_2096_);
lean_dec(v_den_2094_);
lean_dec(v_num_2093_);
lean_del_object(v___x_2091_);
lean_dec(v_snd_2089_);
lean_dec_ref(v_e_2071_);
v_a_2246_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2209_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2209_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
}
else
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2262_; 
lean_del_object(v___x_2096_);
lean_dec(v_den_2094_);
lean_dec(v_num_2093_);
lean_del_object(v___x_2091_);
lean_dec(v_snd_2089_);
lean_dec_ref(v_e_2071_);
v_a_2255_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2262_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2257_ = v___x_2200_;
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2200_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2262_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v_a_2255_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
}
}
}
else
{
lean_object* v___x_2263_; 
v___x_2263_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast(v_num_2093_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2317_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2266_ = v___x_2263_;
v_isShared_2267_ = v_isSharedCheck_2317_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2263_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2317_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v_val_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2316_; 
v_val_2268_ = lean_ctor_get(v_a_2264_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_a_2264_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2270_ = v_a_2264_;
v_isShared_2271_ = v_isSharedCheck_2316_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_val_2268_);
lean_dec(v_a_2264_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2316_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v_u_2272_; lean_object* v_type_2273_; lean_object* v_fieldInst_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2278_; 
v_u_2272_ = lean_ctor_get(v___y_2072_, 0);
v_type_2273_ = lean_ctor_get(v___y_2072_, 1);
v_fieldInst_2274_ = lean_ctor_get(v___y_2072_, 2);
v___x_2275_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6));
v___x_2276_ = lean_box(0);
lean_inc(v_u_2272_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set_tag(v___x_2096_, 1);
lean_ctor_set(v___x_2096_, 1, v___x_2276_);
lean_ctor_set(v___x_2096_, 0, v_u_2272_);
v___x_2278_ = v___x_2096_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_u_2272_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
lean_object* v___x_2279_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2295_; 
v___x_2279_ = l_Lean_mkConst(v___x_2275_, v___x_2278_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2307_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_2308_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_2309_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_2310_ = l_Lean_instToExprRat_mkInt(v_num_2093_);
v___x_2311_ = lean_nat_to_int(v_den_2094_);
v___x_2312_ = l_Lean_instToExprRat_mkInt(v___x_2311_);
lean_dec(v___x_2311_);
v___x_2313_ = l_Lean_mkApp6(v___x_2307_, v___x_2308_, v___x_2308_, v___x_2308_, v___x_2309_, v___x_2310_, v___x_2312_);
v___y_2295_ = v___x_2313_;
goto v___jp_2294_;
}
else
{
lean_object* v___x_2314_; 
lean_dec(v_den_2094_);
v___x_2314_ = l_Lean_instToExprRat_mkInt(v_num_2093_);
v___y_2295_ = v___x_2314_;
goto v___jp_2294_;
}
v___jp_2280_:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2286_; 
v___x_2283_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_fieldInst_2274_);
lean_inc_ref(v_type_2273_);
v___x_2284_ = l_Lean_mkApp7(v___x_2279_, v_type_2273_, v_fieldInst_2274_, v_e_2071_, v___y_2281_, v___y_2282_, v___x_2283_, v_snd_2089_);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 1, v___x_2284_);
lean_ctor_set(v___x_2091_, 0, v_val_2268_);
v___x_2286_ = v___x_2091_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_val_2268_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v___x_2284_);
v___x_2286_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
lean_object* v___x_2288_; 
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 0, v___x_2286_);
v___x_2288_ = v___x_2270_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2290_; 
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v___x_2288_);
v___x_2290_ = v___x_2266_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
v___jp_2294_:
{
lean_object* v___x_2296_; uint8_t v___x_2297_; 
v___x_2296_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35);
v___x_2297_ = lean_int_dec_le(v___x_2296_, v_num_2093_);
if (v___x_2297_ == 0)
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2298_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36);
v___x_2299_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39);
v___x_2300_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42);
v___x_2301_ = lean_int_neg(v_num_2093_);
lean_dec(v_num_2093_);
v___x_2302_ = l_Int_toNat(v___x_2301_);
lean_dec(v___x_2301_);
v___x_2303_ = l_Lean_instToExprInt_mkNat(v___x_2302_);
v___x_2304_ = l_Lean_mkApp3(v___x_2298_, v___x_2299_, v___x_2300_, v___x_2303_);
v___y_2281_ = v___y_2295_;
v___y_2282_ = v___x_2304_;
goto v___jp_2280_;
}
else
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2305_ = l_Int_toNat(v_num_2093_);
lean_dec(v_num_2093_);
v___x_2306_ = l_Lean_instToExprInt_mkNat(v___x_2305_);
v___y_2281_ = v___y_2295_;
v___y_2282_ = v___x_2306_;
goto v___jp_2280_;
}
}
}
}
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_del_object(v___x_2096_);
lean_dec(v_den_2094_);
lean_dec(v_num_2093_);
lean_del_object(v___x_2091_);
lean_dec(v_snd_2089_);
lean_dec_ref(v_e_2071_);
v_a_2318_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2263_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2263_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
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
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
lean_dec_ref(v_e_2071_);
v_a_2329_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2078_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2078_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2329_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___boxed(lean_object* v_e_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0(v_e_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec_ref(v___y_2338_);
return v_res_2344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f(lean_object* v_e_2345_, lean_object* v_type_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_){
_start:
{
uint8_t v___x_2352_; 
lean_inc_ref(v_e_2345_);
v___x_2352_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(v_e_2345_);
if (v___x_2352_ == 0)
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
lean_dec_ref(v_type_2346_);
lean_dec_ref(v_e_2345_);
v___x_2353_ = lean_box(0);
v___x_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
return v___x_2354_;
}
else
{
lean_object* v___f_2355_; lean_object* v___x_2356_; 
v___f_2355_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2355_, 0, v_e_2345_);
v___x_2356_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg(v_type_2346_, v___f_2355_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_);
return v___x_2356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___boxed(lean_object* v_e_2357_, lean_object* v_type_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Lean_Meta_Grind_Arith_normFieldExpr_x3f(v_e_2357_, v_type_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
return v_res_2364_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_FieldNormNum(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_SafeExponentiation(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

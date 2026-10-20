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
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_708_, 1);
v_r_693_ = v_a_709_;
goto v___jp_692_;
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_729_; 
v_a_710_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_729_ == 0)
{
v___x_712_ = v___x_708_;
v_isShared_713_ = v_isSharedCheck_729_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_708_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_729_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
uint8_t v___x_714_; 
v___x_714_ = l_Lean_Exception_isInterrupt(v_a_710_);
if (v___x_714_ == 0)
{
uint8_t v___x_715_; 
lean_inc(v_a_710_);
v___x_715_ = l_Lean_Exception_isRuntime(v_a_710_);
if (v___x_715_ == 0)
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
else
{
lean_object* v___x_727_; 
lean_dec_ref(v___x_698_);
if (v_isShared_713_ == 0)
{
v___x_727_ = v___x_712_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_710_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___boxed(lean_object* v_n_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast(v_n_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
lean_dec(v_a_735_);
lean_dec_ref(v_a_734_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec_ref(v_a_731_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(lean_object* v_a_744_){
_start:
{
lean_object* v_u_746_; lean_object* v_type_747_; lean_object* v_ringInst_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v_u_746_ = lean_ctor_get(v_a_744_, 0);
v_type_747_ = lean_ctor_get(v_a_744_, 1);
v_ringInst_748_ = lean_ctor_get(v_a_744_, 4);
v___x_749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1));
v___x_750_ = lean_box(0);
lean_inc(v_u_746_);
v___x_751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_751_, 0, v_u_746_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = l_Lean_mkConst(v___x_749_, v___x_751_);
lean_inc_ref(v_ringInst_748_);
lean_inc_ref(v_type_747_);
v___x_753_ = l_Lean_mkAppB(v___x_752_, v_type_747_, v_ringInst_748_);
v___x_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
v___x_755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___boxed(lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(v_a_756_);
lean_dec_ref(v_a_756_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst(lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(v_a_759_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___boxed(lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst(v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec_ref(v_a_766_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isIntCastInst(lean_object* v_inst_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v___x_780_; lean_object* v_a_781_; lean_object* v_val_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_806_; 
v___x_780_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(v_a_774_);
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref(v___x_780_);
v_val_782_ = lean_ctor_get(v_a_781_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v_a_781_);
if (v_isSharedCheck_806_ == 0)
{
v___x_784_ = v_a_781_;
v_isShared_785_ = v_isSharedCheck_806_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_val_782_);
lean_dec(v_a_781_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_806_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; 
v___x_786_ = l_Lean_Meta_isDefEqI(v_inst_773_, v_val_782_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_797_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_797_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_797_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_797_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v_a_787_);
v___x_792_ = v___x_784_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_796_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_794_; 
if (v_isShared_790_ == 0)
{
lean_ctor_set(v___x_789_, 0, v___x_792_);
v___x_794_ = v___x_789_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_del_object(v___x_784_);
v_a_798_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_786_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_786_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isIntCastInst___boxed(lean_object* v_inst_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isIntCastInst(v_inst_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec_ref(v_a_808_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast(lean_object* v_n_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v_r_827_; lean_object* v_u_830_; lean_object* v_type_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_u_830_ = lean_ctor_get(v_a_820_, 0);
v_type_831_ = lean_ctor_get(v_a_820_, 1);
v___x_832_ = l_Lean_mkIntLit(v_n_819_);
v___x_833_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1));
lean_inc_ref(v_type_831_);
v___x_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_834_, 0, v_type_831_);
v___x_835_ = lean_box(0);
lean_inc_ref(v___x_832_);
v___x_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_836_, 0, v___x_832_);
v___x_837_ = lean_unsigned_to_nat(3u);
v___x_838_ = lean_mk_empty_array_with_capacity(v___x_837_);
v___x_839_ = lean_array_push(v___x_838_, v___x_834_);
v___x_840_ = lean_array_push(v___x_839_, v___x_835_);
v___x_841_ = lean_array_push(v___x_840_, v___x_836_);
v___x_842_ = l_Lean_Meta_mkAppOptM(v___x_833_, v___x_841_, v_a_821_, v_a_822_, v_a_823_, v_a_824_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; 
lean_dec_ref(v___x_832_);
v_a_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v___x_842_, 1);
v_r_827_ = v_a_843_;
goto v___jp_826_;
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_863_; 
v_a_844_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_863_ == 0)
{
v___x_846_ = v___x_842_;
v_isShared_847_ = v_isSharedCheck_863_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_842_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_863_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
uint8_t v___x_848_; 
v___x_848_ = l_Lean_Exception_isInterrupt(v_a_844_);
if (v___x_848_ == 0)
{
uint8_t v___x_849_; 
lean_inc(v_a_844_);
v___x_849_ = l_Lean_Exception_isRuntime(v_a_844_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; lean_object* v_a_851_; lean_object* v_val_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
lean_del_object(v___x_846_);
lean_dec(v_a_844_);
v___x_850_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(v_a_820_);
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref(v___x_850_);
v_val_852_ = lean_ctor_get(v_a_851_, 0);
lean_inc(v_val_852_);
lean_dec(v_a_851_);
v___x_853_ = lean_box(0);
lean_inc(v_u_830_);
v___x_854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_854_, 0, v_u_830_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = l_Lean_mkConst(v___x_833_, v___x_854_);
lean_inc_ref(v_type_831_);
v___x_856_ = l_Lean_mkApp3(v___x_855_, v_type_831_, v_val_852_, v___x_832_);
v_r_827_ = v___x_856_;
goto v___jp_826_;
}
else
{
lean_object* v___x_858_; 
lean_dec_ref(v___x_832_);
if (v_isShared_847_ == 0)
{
v___x_858_ = v___x_846_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_844_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
else
{
lean_object* v___x_861_; 
lean_dec_ref(v___x_832_);
if (v_isShared_847_ == 0)
{
v___x_861_ = v___x_846_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_844_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
v___jp_826_:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_828_, 0, v_r_827_);
v___x_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
return v___x_829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___boxed(lean_object* v_n_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast(v_n_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec_ref(v_a_865_);
lean_dec(v_n_864_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin_spec__0(lean_object* v_a_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = lean_nat_to_int(v_a_872_);
return v___x_873_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_unsigned_to_nat(0u);
v___x_880_ = l_Lean_Level_ofNat(v___x_879_);
return v___x_880_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_881_ = lean_box(0);
v___x_882_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3);
v___x_883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
lean_ctor_set(v___x_883_, 1, v___x_881_);
return v___x_883_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__5(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_884_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4);
v___x_885_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3);
v___x_886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
lean_ctor_set(v___x_886_, 1, v___x_884_);
return v___x_886_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__6(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_887_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__5, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__5);
v___x_888_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3);
v___x_889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v___x_887_);
return v___x_889_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_890_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__6, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__6);
v___x_891_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2));
v___x_892_ = l_Lean_Expr_const___override(v___x_891_, v___x_890_);
return v___x_892_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = lean_box(0);
v___x_897_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__9));
v___x_898_ = l_Lean_Expr_const___override(v___x_897_, v___x_896_);
return v___x_898_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__11(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4);
v___x_900_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__1));
v___x_901_ = l_Lean_Expr_const___override(v___x_900_, v___x_899_);
return v___x_901_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__14(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = lean_box(0);
v___x_907_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__13));
v___x_908_ = l_Lean_Expr_const___override(v___x_907_, v___x_906_);
return v___x_908_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_909_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__14, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__14_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__14);
v___x_910_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_911_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__11, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__11);
v___x_912_ = l_Lean_mkAppB(v___x_911_, v___x_910_, v___x_909_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(lean_object* v_declName_913_, lean_object* v_a_914_, lean_object* v_b_915_, lean_object* v_r_u2081_916_, lean_object* v_r_u2082_917_, lean_object* v_op_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_fst_921_; lean_object* v_snd_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_995_; 
v_fst_921_ = lean_ctor_get(v_r_u2081_916_, 0);
v_snd_922_ = lean_ctor_get(v_r_u2081_916_, 1);
v_isSharedCheck_995_ = !lean_is_exclusive(v_r_u2081_916_);
if (v_isSharedCheck_995_ == 0)
{
v___x_924_ = v_r_u2081_916_;
v_isShared_925_ = v_isSharedCheck_995_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_snd_922_);
lean_inc(v_fst_921_);
lean_dec(v_r_u2081_916_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_995_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v_fst_926_; lean_object* v_snd_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_994_; 
v_fst_926_ = lean_ctor_get(v_r_u2082_917_, 0);
v_snd_927_ = lean_ctor_get(v_r_u2082_917_, 1);
v_isSharedCheck_994_ = !lean_is_exclusive(v_r_u2082_917_);
if (v_isSharedCheck_994_ == 0)
{
v___x_929_ = v_r_u2082_917_;
v_isShared_930_ = v_isSharedCheck_994_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_snd_927_);
lean_inc(v_fst_926_);
lean_dec(v_r_u2082_917_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_994_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v_u_931_; lean_object* v_type_932_; lean_object* v_fieldInst_933_; lean_object* v_isChar0Inst_934_; lean_object* v_num_935_; lean_object* v_den_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v_u_931_ = lean_ctor_get(v_a_919_, 0);
v_type_932_ = lean_ctor_get(v_a_919_, 1);
v_fieldInst_933_ = lean_ctor_get(v_a_919_, 2);
v_isChar0Inst_934_ = lean_ctor_get(v_a_919_, 3);
v_num_935_ = lean_ctor_get(v_fst_921_, 0);
lean_inc(v_num_935_);
v_den_936_ = lean_ctor_get(v_fst_921_, 1);
lean_inc(v_den_936_);
lean_inc(v_fst_926_);
v___x_937_ = lean_apply_2(v_op_918_, v_fst_921_, v_fst_926_);
v___x_938_ = lean_box(0);
lean_inc(v_u_931_);
if (v_isShared_925_ == 0)
{
lean_ctor_set_tag(v___x_924_, 1);
lean_ctor_set(v___x_924_, 1, v___x_938_);
lean_ctor_set(v___x_924_, 0, v_u_931_);
v___x_940_ = v___x_924_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_u_931_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v___x_938_);
v___x_940_ = v_reuseFailAlloc_993_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
lean_object* v___x_941_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_970_; lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_941_ = l_Lean_mkConst(v_declName_913_, v___x_940_);
v___x_983_ = lean_unsigned_to_nat(1u);
v___x_984_ = lean_nat_dec_eq(v_den_936_, v___x_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_985_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_986_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_987_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_988_ = l_Lean_instToExprRat_mkInt(v_num_935_);
lean_dec(v_num_935_);
v___x_989_ = lean_nat_to_int(v_den_936_);
v___x_990_ = l_Lean_instToExprRat_mkInt(v___x_989_);
lean_dec(v___x_989_);
v___x_991_ = l_Lean_mkApp6(v___x_985_, v___x_986_, v___x_986_, v___x_986_, v___x_987_, v___x_988_, v___x_990_);
v___y_970_ = v___x_991_;
goto v___jp_969_;
}
else
{
lean_object* v___x_992_; 
lean_dec(v_den_936_);
v___x_992_ = l_Lean_instToExprRat_mkInt(v_num_935_);
lean_dec(v_num_935_);
v___y_970_ = v___x_992_;
goto v___jp_969_;
}
v___jp_942_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_950_; 
lean_inc_ref(v_isChar0Inst_934_);
lean_inc_ref(v_fieldInst_933_);
lean_inc_ref(v_type_932_);
v___x_946_ = l_Lean_mkApp8(v___x_941_, v_type_932_, v_fieldInst_933_, v_isChar0Inst_934_, v_a_914_, v_b_915_, v___y_944_, v___y_943_, v___y_945_);
v___x_947_ = l_Lean_eagerReflBoolTrue;
v___x_948_ = l_Lean_mkApp3(v___x_946_, v___x_947_, v_snd_922_, v_snd_927_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 1, v___x_948_);
lean_ctor_set(v___x_929_, 0, v___x_937_);
v___x_950_ = v___x_929_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v___x_948_);
v___x_950_ = v_reuseFailAlloc_953_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
}
v___jp_954_:
{
lean_object* v_num_957_; lean_object* v_den_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v_num_957_ = lean_ctor_get(v___x_937_, 0);
lean_inc(v_num_957_);
v_den_958_ = lean_ctor_get(v___x_937_, 1);
lean_inc(v_den_958_);
v___x_959_ = lean_unsigned_to_nat(1u);
v___x_960_ = lean_nat_dec_eq(v_den_958_, v___x_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_961_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_962_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_963_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_964_ = l_Lean_instToExprRat_mkInt(v_num_957_);
lean_dec(v_num_957_);
v___x_965_ = lean_nat_to_int(v_den_958_);
v___x_966_ = l_Lean_instToExprRat_mkInt(v___x_965_);
lean_dec(v___x_965_);
v___x_967_ = l_Lean_mkApp6(v___x_961_, v___x_962_, v___x_962_, v___x_962_, v___x_963_, v___x_964_, v___x_966_);
v___y_943_ = v___y_956_;
v___y_944_ = v___y_955_;
v___y_945_ = v___x_967_;
goto v___jp_942_;
}
else
{
lean_object* v___x_968_; 
lean_dec(v_den_958_);
v___x_968_ = l_Lean_instToExprRat_mkInt(v_num_957_);
lean_dec(v_num_957_);
v___y_943_ = v___y_956_;
v___y_944_ = v___y_955_;
v___y_945_ = v___x_968_;
goto v___jp_942_;
}
}
v___jp_969_:
{
lean_object* v_num_971_; lean_object* v_den_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v_num_971_ = lean_ctor_get(v_fst_926_, 0);
lean_inc(v_num_971_);
v_den_972_ = lean_ctor_get(v_fst_926_, 1);
lean_inc(v_den_972_);
lean_dec(v_fst_926_);
v___x_973_ = lean_unsigned_to_nat(1u);
v___x_974_ = lean_nat_dec_eq(v_den_972_, v___x_973_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_975_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_976_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_977_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_978_ = l_Lean_instToExprRat_mkInt(v_num_971_);
lean_dec(v_num_971_);
v___x_979_ = lean_nat_to_int(v_den_972_);
v___x_980_ = l_Lean_instToExprRat_mkInt(v___x_979_);
lean_dec(v___x_979_);
v___x_981_ = l_Lean_mkApp6(v___x_975_, v___x_976_, v___x_976_, v___x_976_, v___x_977_, v___x_978_, v___x_980_);
v___y_955_ = v___y_970_;
v___y_956_ = v___x_981_;
goto v___jp_954_;
}
else
{
lean_object* v___x_982_; 
lean_dec(v_den_972_);
v___x_982_ = l_Lean_instToExprRat_mkInt(v_num_971_);
lean_dec(v_num_971_);
v___y_955_ = v___y_970_;
v___y_956_ = v___x_982_;
goto v___jp_954_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___boxed(lean_object* v_declName_996_, lean_object* v_a_997_, lean_object* v_b_998_, lean_object* v_r_u2081_999_, lean_object* v_r_u2082_1000_, lean_object* v_op_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v_declName_996_, v_a_997_, v_b_998_, v_r_u2081_999_, v_r_u2082_1000_, v_op_1001_, v_a_1002_);
lean_dec_ref(v_a_1002_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin(lean_object* v_declName_1005_, lean_object* v_a_1006_, lean_object* v_b_1007_, lean_object* v_r_u2081_1008_, lean_object* v_r_u2082_1009_, lean_object* v_op_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v_declName_1005_, v_a_1006_, v_b_1007_, v_r_u2081_1008_, v_r_u2082_1009_, v_op_1010_, v_a_1011_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___boxed(lean_object* v_declName_1018_, lean_object* v_a_1019_, lean_object* v_b_1020_, lean_object* v_r_u2081_1021_, lean_object* v_r_u2082_1022_, lean_object* v_op_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin(v_declName_1018_, v_a_1019_, v_b_1020_, v_r_u2081_1021_, v_r_u2082_1022_, v_op_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec_ref(v_a_1024_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(lean_object* v_declName_1031_, lean_object* v_a_1032_, lean_object* v_r_1033_, lean_object* v_op_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_fst_1037_; lean_object* v_snd_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1085_; 
v_fst_1037_ = lean_ctor_get(v_r_1033_, 0);
v_snd_1038_ = lean_ctor_get(v_r_1033_, 1);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_r_1033_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1040_ = v_r_1033_;
v_isShared_1041_ = v_isSharedCheck_1085_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_snd_1038_);
lean_inc(v_fst_1037_);
lean_dec(v_r_1033_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1085_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v_u_1042_; lean_object* v_type_1043_; lean_object* v_fieldInst_1044_; lean_object* v_num_1045_; lean_object* v_den_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v___y_1062_; lean_object* v___x_1075_; uint8_t v___x_1076_; 
v_u_1042_ = lean_ctor_get(v_a_1035_, 0);
v_type_1043_ = lean_ctor_get(v_a_1035_, 1);
v_fieldInst_1044_ = lean_ctor_get(v_a_1035_, 2);
v_num_1045_ = lean_ctor_get(v_fst_1037_, 0);
lean_inc(v_num_1045_);
v_den_1046_ = lean_ctor_get(v_fst_1037_, 1);
lean_inc(v_den_1046_);
v___x_1047_ = lean_apply_1(v_op_1034_, v_fst_1037_);
v___x_1048_ = lean_box(0);
lean_inc(v_u_1042_);
v___x_1049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1049_, 0, v_u_1042_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = l_Lean_mkConst(v_declName_1031_, v___x_1049_);
v___x_1075_ = lean_unsigned_to_nat(1u);
v___x_1076_ = lean_nat_dec_eq(v_den_1046_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1077_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_1078_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_1079_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_1080_ = l_Lean_instToExprRat_mkInt(v_num_1045_);
lean_dec(v_num_1045_);
v___x_1081_ = lean_nat_to_int(v_den_1046_);
v___x_1082_ = l_Lean_instToExprRat_mkInt(v___x_1081_);
lean_dec(v___x_1081_);
v___x_1083_ = l_Lean_mkApp6(v___x_1077_, v___x_1078_, v___x_1078_, v___x_1078_, v___x_1079_, v___x_1080_, v___x_1082_);
v___y_1062_ = v___x_1083_;
goto v___jp_1061_;
}
else
{
lean_object* v___x_1084_; 
lean_dec(v_den_1046_);
v___x_1084_ = l_Lean_instToExprRat_mkInt(v_num_1045_);
lean_dec(v_num_1045_);
v___y_1062_ = v___x_1084_;
goto v___jp_1061_;
}
v___jp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1054_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_fieldInst_1044_);
lean_inc_ref(v_type_1043_);
v___x_1055_ = l_Lean_mkApp7(v___x_1050_, v_type_1043_, v_fieldInst_1044_, v_a_1032_, v___y_1052_, v___y_1053_, v___x_1054_, v_snd_1038_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 1, v___x_1055_);
lean_ctor_set(v___x_1040_, 0, v___x_1047_);
v___x_1057_ = v___x_1040_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
}
v___jp_1061_:
{
lean_object* v_num_1063_; lean_object* v_den_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v_num_1063_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_num_1063_);
v_den_1064_ = lean_ctor_get(v___x_1047_, 1);
lean_inc(v_den_1064_);
v___x_1065_ = lean_unsigned_to_nat(1u);
v___x_1066_ = lean_nat_dec_eq(v_den_1064_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1067_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_1068_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_1069_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_1070_ = l_Lean_instToExprRat_mkInt(v_num_1063_);
lean_dec(v_num_1063_);
v___x_1071_ = lean_nat_to_int(v_den_1064_);
v___x_1072_ = l_Lean_instToExprRat_mkInt(v___x_1071_);
lean_dec(v___x_1071_);
v___x_1073_ = l_Lean_mkApp6(v___x_1067_, v___x_1068_, v___x_1068_, v___x_1068_, v___x_1069_, v___x_1070_, v___x_1072_);
v___y_1052_ = v___y_1062_;
v___y_1053_ = v___x_1073_;
goto v___jp_1051_;
}
else
{
lean_object* v___x_1074_; 
lean_dec(v_den_1064_);
v___x_1074_ = l_Lean_instToExprRat_mkInt(v_num_1063_);
lean_dec(v_num_1063_);
v___y_1052_ = v___y_1062_;
v___y_1053_ = v___x_1074_;
goto v___jp_1051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg___boxed(lean_object* v_declName_1086_, lean_object* v_a_1087_, lean_object* v_r_1088_, lean_object* v_op_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(v_declName_1086_, v_a_1087_, v_r_1088_, v_op_1089_, v_a_1090_);
lean_dec_ref(v_a_1090_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary(lean_object* v_declName_1093_, lean_object* v_a_1094_, lean_object* v_r_1095_, lean_object* v_op_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(v_declName_1093_, v_a_1094_, v_r_1095_, v_op_1096_, v_a_1097_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___boxed(lean_object* v_declName_1104_, lean_object* v_a_1105_, lean_object* v_r_1106_, lean_object* v_op_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary(v_declName_1104_, v_a_1105_, v_r_1106_, v_op_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec_ref(v_a_1108_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval_spec__1(lean_object* v_a_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Rat_ofInt(v_a_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval_spec__0(lean_object* v_a_1117_){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = lean_nat_to_int(v_a_1117_);
v___x_1119_ = l_Rat_ofInt(v___x_1118_);
return v___x_1119_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37(void){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = lean_nat_to_int(v___x_1196_);
return v___x_1197_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4);
v___x_1199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13));
v___x_1200_ = l_Lean_Expr_const___override(v___x_1199_, v___x_1198_);
return v___x_1200_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1204_ = lean_box(0);
v___x_1205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__40));
v___x_1206_ = l_Lean_Expr_const___override(v___x_1205_, v___x_1204_);
return v___x_1206_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = lean_box(0);
v___x_1212_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__43));
v___x_1213_ = l_Lean_Expr_const___override(v___x_1212_, v___x_1211_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(lean_object* v_e_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v___f_1266_; lean_object* v___f_1267_; lean_object* v___f_1268_; lean_object* v___f_1269_; lean_object* v___f_1270_; lean_object* v___f_1271_; lean_object* v___x_1272_; 
v___f_1266_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__0));
v___f_1267_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__1));
v___f_1268_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__2));
v___f_1269_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__3));
v___f_1270_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4));
v___f_1271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__5));
v___x_1272_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1256_, v_a_1259_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1272_, 1);
v___x_1274_ = l_Lean_Expr_cleanupAnnotations(v_a_1273_);
v___x_1275_ = l_Lean_Expr_isApp(v___x_1274_);
if (v___x_1275_ == 0)
{
lean_dec_ref(v___x_1274_);
goto v___jp_1263_;
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
goto v___jp_1263_;
}
else
{
lean_object* v_arg_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; 
v_arg_1279_ = lean_ctor_get(v___x_1277_, 1);
lean_inc_ref(v_arg_1279_);
v___x_1280_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1277_);
v___x_1281_ = l_Lean_Expr_isApp(v___x_1280_);
if (v___x_1281_ == 0)
{
lean_dec_ref(v___x_1280_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
goto v___jp_1263_;
}
else
{
lean_object* v_arg_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v_arg_1282_ = lean_ctor_get(v___x_1280_, 1);
lean_inc_ref(v_arg_1282_);
v___x_1283_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1280_);
v___x_1284_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1));
v___x_1285_ = l_Lean_Expr_isConstOf(v___x_1283_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1286_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1));
v___x_1287_ = l_Lean_Expr_isConstOf(v___x_1283_, v___x_1286_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7));
v___x_1289_ = l_Lean_Expr_isConstOf(v___x_1283_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; uint8_t v___x_1291_; 
v___x_1290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10));
v___x_1291_ = l_Lean_Expr_isConstOf(v___x_1283_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13));
v___x_1293_ = l_Lean_Expr_isConstOf(v___x_1283_, v___x_1292_);
if (v___x_1293_ == 0)
{
uint8_t v___x_1294_; 
v___x_1294_ = l_Lean_Expr_isApp(v___x_1283_);
if (v___x_1294_ == 0)
{
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_arg_1282_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
goto v___jp_1263_;
}
else
{
lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1283_);
v___x_1296_ = l_Lean_Expr_isApp(v___x_1295_);
if (v___x_1296_ == 0)
{
lean_dec_ref(v___x_1295_);
lean_dec_ref(v_arg_1282_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
goto v___jp_1263_;
}
else
{
lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1297_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1295_);
v___x_1298_ = l_Lean_Expr_isApp(v___x_1297_);
if (v___x_1298_ == 0)
{
lean_dec_ref(v___x_1297_);
lean_dec_ref(v_arg_1282_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
goto v___jp_1263_;
}
else
{
lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v___x_1299_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1297_);
v___x_1300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16));
v___x_1301_ = l_Lean_Expr_isConstOf(v___x_1299_, v___x_1300_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1302_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2));
v___x_1303_ = l_Lean_Expr_isConstOf(v___x_1299_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1304_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19));
v___x_1305_ = l_Lean_Expr_isConstOf(v___x_1299_, v___x_1304_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__22));
v___x_1307_ = l_Lean_Expr_isConstOf(v___x_1299_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__25));
v___x_1309_ = l_Lean_Expr_isConstOf(v___x_1299_, v___x_1308_);
lean_dec_ref(v___x_1299_);
if (v___x_1309_ == 0)
{
lean_dec_ref(v_arg_1282_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
goto v___jp_1263_;
}
else
{
lean_object* v___x_1310_; 
v___x_1310_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst(v_arg_1282_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1333_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1333_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1333_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
if (lean_obj_tag(v_a_1311_) == 0)
{
lean_object* v___x_1315_; lean_object* v___x_1317_; 
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
v___x_1315_ = lean_box(0);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1315_);
v___x_1317_ = v___x_1313_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
else
{
lean_object* v_val_1319_; uint8_t v___x_1320_; 
v_val_1319_ = lean_ctor_get(v_a_1311_, 0);
lean_inc(v_val_1319_);
lean_dec_ref_known(v_a_1311_, 1);
v___x_1320_ = lean_unbox(v_val_1319_);
lean_dec(v_val_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1323_; 
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
v___x_1321_ = lean_box(0);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1321_);
v___x_1323_ = v___x_1313_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
else
{
lean_object* v___x_1325_; 
lean_del_object(v___x_1313_);
lean_inc_ref(v_arg_1279_);
v___x_1325_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1279_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
if (lean_obj_tag(v_a_1326_) == 0)
{
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
return v___x_1325_;
}
else
{
lean_object* v_val_1327_; lean_object* v___x_1328_; 
lean_inc_ref(v_a_1326_);
lean_dec_ref_known(v___x_1325_, 1);
v_val_1327_ = lean_ctor_get(v_a_1326_, 0);
lean_inc(v_val_1327_);
lean_dec_ref_known(v_a_1326_, 1);
lean_inc_ref(v_arg_1276_);
v___x_1328_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1276_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
if (lean_obj_tag(v_a_1329_) == 0)
{
lean_dec(v_val_1327_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
return v___x_1328_;
}
else
{
lean_object* v_val_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_inc_ref(v_a_1329_);
lean_dec_ref_known(v___x_1328_, 1);
v_val_1330_ = lean_ctor_get(v_a_1329_, 0);
lean_inc(v_val_1330_);
lean_dec_ref_known(v_a_1329_, 1);
v___x_1331_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28));
v___x_1332_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v___x_1331_, v_arg_1279_, v_arg_1276_, v_val_1327_, v_val_1330_, v___f_1271_, v_a_1257_);
return v___x_1332_;
}
}
else
{
lean_dec(v_val_1327_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
return v___x_1328_;
}
}
}
else
{
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
return v___x_1325_;
}
}
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
v_a_1334_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1310_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1310_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
}
else
{
lean_object* v___x_1342_; 
lean_dec_ref(v___x_1299_);
v___x_1342_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst(v_arg_1282_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1365_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1365_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1365_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
if (lean_obj_tag(v_a_1343_) == 0)
{
lean_object* v___x_1347_; lean_object* v___x_1349_; 
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
v___x_1347_ = lean_box(0);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1347_);
v___x_1349_ = v___x_1345_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
else
{
lean_object* v_val_1351_; uint8_t v___x_1352_; 
v_val_1351_ = lean_ctor_get(v_a_1343_, 0);
lean_inc(v_val_1351_);
lean_dec_ref_known(v_a_1343_, 1);
v___x_1352_ = lean_unbox(v_val_1351_);
lean_dec(v_val_1351_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; lean_object* v___x_1355_; 
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
v___x_1353_ = lean_box(0);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 0, v___x_1353_);
v___x_1355_ = v___x_1345_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
else
{
lean_object* v___x_1357_; 
lean_del_object(v___x_1345_);
lean_inc_ref(v_arg_1279_);
v___x_1357_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1279_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
if (lean_obj_tag(v_a_1358_) == 0)
{
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
return v___x_1357_;
}
else
{
lean_object* v_val_1359_; lean_object* v___x_1360_; 
lean_inc_ref(v_a_1358_);
lean_dec_ref_known(v___x_1357_, 1);
v_val_1359_ = lean_ctor_get(v_a_1358_, 0);
lean_inc(v_val_1359_);
lean_dec_ref_known(v_a_1358_, 1);
lean_inc_ref(v_arg_1276_);
v___x_1360_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1276_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
if (lean_obj_tag(v_a_1361_) == 0)
{
lean_dec(v_val_1359_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
return v___x_1360_;
}
else
{
lean_object* v_val_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; 
lean_inc_ref(v_a_1361_);
lean_dec_ref_known(v___x_1360_, 1);
v_val_1362_ = lean_ctor_get(v_a_1361_, 0);
lean_inc(v_val_1362_);
lean_dec_ref_known(v_a_1361_, 1);
v___x_1363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30));
v___x_1364_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v___x_1363_, v_arg_1279_, v_arg_1276_, v_val_1359_, v_val_1362_, v___f_1270_, v_a_1257_);
return v___x_1364_;
}
}
else
{
lean_dec(v_val_1359_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
return v___x_1360_;
}
}
}
else
{
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
return v___x_1357_;
}
}
}
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
v_a_1366_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1342_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1342_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1371_; 
if (v_isShared_1369_ == 0)
{
v___x_1371_ = v___x_1368_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
}
}
else
{
lean_object* v___x_1374_; 
lean_dec_ref(v___x_1299_);
v___x_1374_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst(v_arg_1282_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1397_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1377_ = v___x_1374_;
v_isShared_1378_ = v_isSharedCheck_1397_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1374_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1397_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
if (lean_obj_tag(v_a_1375_) == 0)
{
lean_object* v___x_1379_; lean_object* v___x_1381_; 
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
v___x_1379_ = lean_box(0);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v___x_1379_);
v___x_1381_ = v___x_1377_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
else
{
lean_object* v_val_1383_; uint8_t v___x_1384_; 
v_val_1383_ = lean_ctor_get(v_a_1375_, 0);
lean_inc(v_val_1383_);
lean_dec_ref_known(v_a_1375_, 1);
v___x_1384_ = lean_unbox(v_val_1383_);
lean_dec(v_val_1383_);
if (v___x_1384_ == 0)
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
v___x_1385_ = lean_box(0);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v___x_1385_);
v___x_1387_ = v___x_1377_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
else
{
lean_object* v___x_1389_; 
lean_del_object(v___x_1377_);
lean_inc_ref(v_arg_1279_);
v___x_1389_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1279_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
if (lean_obj_tag(v_a_1390_) == 0)
{
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
return v___x_1389_;
}
else
{
lean_object* v_val_1391_; lean_object* v___x_1392_; 
lean_inc_ref(v_a_1390_);
lean_dec_ref_known(v___x_1389_, 1);
v_val_1391_ = lean_ctor_get(v_a_1390_, 0);
lean_inc(v_val_1391_);
lean_dec_ref_known(v_a_1390_, 1);
lean_inc_ref(v_arg_1276_);
v___x_1392_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1276_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
if (lean_obj_tag(v_a_1393_) == 0)
{
lean_dec(v_val_1391_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
return v___x_1392_;
}
else
{
lean_object* v_val_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_inc_ref(v_a_1393_);
lean_dec_ref_known(v___x_1392_, 1);
v_val_1394_ = lean_ctor_get(v_a_1393_, 0);
lean_inc(v_val_1394_);
lean_dec_ref_known(v_a_1393_, 1);
v___x_1395_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32));
v___x_1396_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v___x_1395_, v_arg_1279_, v_arg_1276_, v_val_1391_, v_val_1394_, v___f_1269_, v_a_1257_);
return v___x_1396_;
}
}
else
{
lean_dec(v_val_1391_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
return v___x_1392_;
}
}
}
else
{
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
return v___x_1389_;
}
}
}
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
v_a_1398_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1374_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1374_);
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
lean_dec_ref(v___x_1299_);
v___x_1406_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst(v_arg_1282_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1429_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1429_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1429_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
if (lean_obj_tag(v_a_1407_) == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
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
lean_dec_ref_known(v_a_1407_, 1);
v___x_1416_ = lean_unbox(v_val_1415_);
lean_dec(v_val_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1419_; 
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
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
lean_inc_ref(v_arg_1279_);
v___x_1421_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1279_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
if (lean_obj_tag(v_a_1422_) == 0)
{
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
return v___x_1421_;
}
else
{
lean_object* v_val_1423_; lean_object* v___x_1424_; 
lean_inc_ref(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
v_val_1423_ = lean_ctor_get(v_a_1422_, 0);
lean_inc(v_val_1423_);
lean_dec_ref_known(v_a_1422_, 1);
lean_inc_ref(v_arg_1276_);
v___x_1424_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1276_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
if (lean_obj_tag(v_a_1425_) == 0)
{
lean_dec(v_val_1423_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
return v___x_1424_;
}
else
{
lean_object* v_val_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
lean_inc_ref(v_a_1425_);
lean_dec_ref_known(v___x_1424_, 1);
v_val_1426_ = lean_ctor_get(v_a_1425_, 0);
lean_inc(v_val_1426_);
lean_dec_ref_known(v_a_1425_, 1);
v___x_1427_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34));
v___x_1428_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v___x_1427_, v_arg_1279_, v_arg_1276_, v_val_1423_, v_val_1426_, v___f_1268_, v_a_1257_);
return v___x_1428_;
}
}
else
{
lean_dec(v_val_1423_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
return v___x_1424_;
}
}
}
else
{
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
return v___x_1421_;
}
}
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
v_a_1430_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1406_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1406_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
else
{
lean_object* v___x_1438_; 
lean_dec_ref(v___x_1299_);
lean_inc_ref(v_arg_1282_);
v___x_1438_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst(v_arg_1282_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1691_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1441_ = v___x_1438_;
v_isShared_1442_ = v_isSharedCheck_1691_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1691_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
if (lean_obj_tag(v_a_1439_) == 0)
{
lean_object* v___x_1443_; lean_object* v___x_1445_; 
lean_dec_ref(v_arg_1282_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
v___x_1443_ = lean_box(0);
if (v_isShared_1442_ == 0)
{
lean_ctor_set(v___x_1441_, 0, v___x_1443_);
v___x_1445_ = v___x_1441_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
else
{
lean_object* v_val_1447_; uint8_t v___x_1448_; 
lean_del_object(v___x_1441_);
v_val_1447_ = lean_ctor_get(v_a_1439_, 0);
lean_inc(v_val_1447_);
lean_dec_ref_known(v_a_1439_, 1);
v___x_1448_ = lean_unbox(v_val_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; 
v___x_1449_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst(v_arg_1282_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1581_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1452_ = v___x_1449_;
v_isShared_1453_ = v_isSharedCheck_1581_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1449_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1581_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
if (lean_obj_tag(v_a_1450_) == 0)
{
lean_object* v___x_1454_; lean_object* v___x_1456_; 
lean_dec(v_val_1447_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
v___x_1454_ = lean_box(0);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1454_);
v___x_1456_ = v___x_1452_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
else
{
lean_object* v_val_1458_; uint8_t v___x_1459_; 
v_val_1458_ = lean_ctor_get(v_a_1450_, 0);
lean_inc(v_val_1458_);
lean_dec_ref_known(v_a_1450_, 1);
v___x_1459_ = lean_unbox(v_val_1458_);
lean_dec(v_val_1458_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; lean_object* v___x_1462_; 
lean_dec(v_val_1447_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
v___x_1460_ = lean_box(0);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 0, v___x_1460_);
v___x_1462_ = v___x_1452_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
else
{
lean_object* v___x_1464_; 
lean_del_object(v___x_1452_);
lean_inc_ref(v_arg_1279_);
v___x_1464_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1279_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
if (lean_obj_tag(v_a_1465_) == 0)
{
lean_dec(v_val_1447_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
return v___x_1464_;
}
else
{
lean_object* v_val_1466_; lean_object* v_fst_1467_; lean_object* v_snd_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1580_; 
lean_inc_ref(v_a_1465_);
lean_dec_ref_known(v___x_1464_, 1);
v_val_1466_ = lean_ctor_get(v_a_1465_, 0);
lean_inc(v_val_1466_);
lean_dec_ref_known(v_a_1465_, 1);
v_fst_1467_ = lean_ctor_get(v_val_1466_, 0);
v_snd_1468_ = lean_ctor_get(v_val_1466_, 1);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_val_1466_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1470_ = v_val_1466_;
v_isShared_1471_ = v_isSharedCheck_1580_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_snd_1468_);
lean_inc(v_fst_1467_);
lean_dec(v_val_1466_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1580_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_Meta_getIntValue_x3f(v_arg_1276_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1571_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1475_ = v___x_1472_;
v_isShared_1476_ = v_isSharedCheck_1571_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1472_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1571_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
if (lean_obj_tag(v_a_1473_) == 1)
{
lean_object* v_val_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1566_; 
lean_del_object(v___x_1475_);
v_val_1477_ = lean_ctor_get(v_a_1473_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_a_1473_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1479_ = v_a_1473_;
v_isShared_1480_ = v_isSharedCheck_1566_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_val_1477_);
lean_dec(v_a_1473_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1566_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1481_; uint8_t v___x_1482_; lean_object* v___x_1483_; 
v___x_1481_ = lean_nat_abs(v_val_1477_);
v___x_1482_ = lean_unbox(v_val_1447_);
lean_dec(v_val_1447_);
v___x_1483_ = l_Lean_checkExponent(v___x_1481_, v___x_1482_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1557_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1486_ = v___x_1483_;
v_isShared_1487_ = v_isSharedCheck_1557_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1483_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1557_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
uint8_t v___x_1488_; 
v___x_1488_ = lean_unbox(v_a_1484_);
lean_dec(v_a_1484_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; lean_object* v___x_1491_; 
lean_del_object(v___x_1479_);
lean_dec(v_val_1477_);
lean_del_object(v___x_1470_);
lean_dec(v_snd_1468_);
lean_dec(v_fst_1467_);
lean_dec_ref(v_arg_1279_);
v___x_1489_ = lean_box(0);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1489_);
v___x_1491_ = v___x_1486_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
else
{
lean_object* v_u_1493_; lean_object* v_type_1494_; lean_object* v_fieldInst_1495_; lean_object* v_isChar0Inst_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___y_1503_; lean_object* v___y_1504_; lean_object* v___y_1505_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1533_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v_u_1493_ = lean_ctor_get(v_a_1257_, 0);
v_type_1494_ = lean_ctor_get(v_a_1257_, 1);
v_fieldInst_1495_ = lean_ctor_get(v_a_1257_, 2);
v_isChar0Inst_1496_ = lean_ctor_get(v_a_1257_, 3);
lean_inc(v_fst_1467_);
v___x_1497_ = l_Rat_zpow(v_fst_1467_, v_val_1477_);
v___x_1498_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36));
v___x_1499_ = lean_box(0);
lean_inc(v_u_1493_);
v___x_1500_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1500_, 0, v_u_1493_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
v___x_1501_ = l_Lean_mkConst(v___x_1498_, v___x_1500_);
v___x_1546_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37);
v___x_1547_ = lean_int_dec_le(v___x_1546_, v_val_1477_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1548_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38);
v___x_1549_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41);
v___x_1550_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44);
v___x_1551_ = lean_int_neg(v_val_1477_);
lean_dec(v_val_1477_);
v___x_1552_ = l_Int_toNat(v___x_1551_);
lean_dec(v___x_1551_);
v___x_1553_ = l_Lean_instToExprInt_mkNat(v___x_1552_);
v___x_1554_ = l_Lean_mkApp3(v___x_1548_, v___x_1549_, v___x_1550_, v___x_1553_);
v___y_1533_ = v___x_1554_;
goto v___jp_1532_;
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = l_Int_toNat(v_val_1477_);
lean_dec(v_val_1477_);
v___x_1556_ = l_Lean_instToExprInt_mkNat(v___x_1555_);
v___y_1533_ = v___x_1556_;
goto v___jp_1532_;
}
v___jp_1502_:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1506_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_isChar0Inst_1496_);
lean_inc_ref(v_fieldInst_1495_);
lean_inc_ref(v_type_1494_);
v___x_1507_ = l_Lean_mkApp9(v___x_1501_, v_type_1494_, v_fieldInst_1495_, v_isChar0Inst_1496_, v_arg_1279_, v___y_1504_, v___y_1503_, v___y_1505_, v___x_1506_, v_snd_1468_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 1, v___x_1507_);
lean_ctor_set(v___x_1470_, 0, v___x_1497_);
v___x_1509_ = v___x_1470_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
lean_object* v___x_1511_; 
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 0, v___x_1509_);
v___x_1511_ = v___x_1479_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1513_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1511_);
v___x_1513_ = v___x_1486_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
v___jp_1517_:
{
lean_object* v_num_1520_; lean_object* v_den_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v_num_1520_ = lean_ctor_get(v___x_1497_, 0);
v_den_1521_ = lean_ctor_get(v___x_1497_, 1);
v___x_1522_ = lean_unsigned_to_nat(1u);
v___x_1523_ = lean_nat_dec_eq(v_den_1521_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1524_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_1525_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_1526_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_1527_ = l_Lean_instToExprRat_mkInt(v_num_1520_);
lean_inc(v_den_1521_);
v___x_1528_ = lean_nat_to_int(v_den_1521_);
v___x_1529_ = l_Lean_instToExprRat_mkInt(v___x_1528_);
lean_dec(v___x_1528_);
v___x_1530_ = l_Lean_mkApp6(v___x_1524_, v___x_1525_, v___x_1525_, v___x_1525_, v___x_1526_, v___x_1527_, v___x_1529_);
v___y_1503_ = v___y_1519_;
v___y_1504_ = v___y_1518_;
v___y_1505_ = v___x_1530_;
goto v___jp_1502_;
}
else
{
lean_object* v___x_1531_; 
v___x_1531_ = l_Lean_instToExprRat_mkInt(v_num_1520_);
v___y_1503_ = v___y_1519_;
v___y_1504_ = v___y_1518_;
v___y_1505_ = v___x_1531_;
goto v___jp_1502_;
}
}
v___jp_1532_:
{
lean_object* v_num_1534_; lean_object* v_den_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v_num_1534_ = lean_ctor_get(v_fst_1467_, 0);
lean_inc(v_num_1534_);
v_den_1535_ = lean_ctor_get(v_fst_1467_, 1);
lean_inc(v_den_1535_);
lean_dec(v_fst_1467_);
v___x_1536_ = lean_unsigned_to_nat(1u);
v___x_1537_ = lean_nat_dec_eq(v_den_1535_, v___x_1536_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1538_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_1539_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_1540_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_1541_ = l_Lean_instToExprRat_mkInt(v_num_1534_);
lean_dec(v_num_1534_);
v___x_1542_ = lean_nat_to_int(v_den_1535_);
v___x_1543_ = l_Lean_instToExprRat_mkInt(v___x_1542_);
lean_dec(v___x_1542_);
v___x_1544_ = l_Lean_mkApp6(v___x_1538_, v___x_1539_, v___x_1539_, v___x_1539_, v___x_1540_, v___x_1541_, v___x_1543_);
v___y_1518_ = v___y_1533_;
v___y_1519_ = v___x_1544_;
goto v___jp_1517_;
}
else
{
lean_object* v___x_1545_; 
lean_dec(v_den_1535_);
v___x_1545_ = l_Lean_instToExprRat_mkInt(v_num_1534_);
lean_dec(v_num_1534_);
v___y_1518_ = v___y_1533_;
v___y_1519_ = v___x_1545_;
goto v___jp_1517_;
}
}
}
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_del_object(v___x_1479_);
lean_dec(v_val_1477_);
lean_del_object(v___x_1470_);
lean_dec(v_snd_1468_);
lean_dec(v_fst_1467_);
lean_dec_ref(v_arg_1279_);
v_a_1558_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1483_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1483_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1569_; 
lean_dec(v_a_1473_);
lean_del_object(v___x_1470_);
lean_dec(v_snd_1468_);
lean_dec(v_fst_1467_);
lean_dec(v_val_1447_);
lean_dec_ref(v_arg_1279_);
v___x_1567_ = lean_box(0);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v___x_1567_);
v___x_1569_ = v___x_1475_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_del_object(v___x_1470_);
lean_dec(v_snd_1468_);
lean_dec(v_fst_1467_);
lean_dec(v_val_1447_);
lean_dec_ref(v_arg_1279_);
v_a_1572_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1472_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1472_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
}
else
{
lean_dec(v_val_1447_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
return v___x_1464_;
}
}
}
}
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec(v_val_1447_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
v_a_1582_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1449_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1449_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
else
{
lean_object* v___x_1590_; 
lean_dec(v_val_1447_);
lean_dec_ref(v_arg_1282_);
lean_inc_ref(v_arg_1279_);
v___x_1590_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1279_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
if (lean_obj_tag(v_a_1591_) == 0)
{
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
return v___x_1590_;
}
else
{
lean_object* v_val_1592_; lean_object* v_fst_1593_; lean_object* v_snd_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1690_; 
lean_inc_ref(v_a_1591_);
lean_dec_ref_known(v___x_1590_, 1);
v_val_1592_ = lean_ctor_get(v_a_1591_, 0);
lean_inc(v_val_1592_);
lean_dec_ref_known(v_a_1591_, 1);
v_fst_1593_ = lean_ctor_get(v_val_1592_, 0);
v_snd_1594_ = lean_ctor_get(v_val_1592_, 1);
v_isSharedCheck_1690_ = !lean_is_exclusive(v_val_1592_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1596_ = v_val_1592_;
v_isShared_1597_ = v_isSharedCheck_1690_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_snd_1594_);
lean_inc(v_fst_1593_);
lean_dec(v_val_1592_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1690_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_Meta_getNatValue_x3f(v_arg_1276_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
lean_dec_ref(v_arg_1276_);
if (lean_obj_tag(v___x_1598_) == 0)
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1681_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1601_ = v___x_1598_;
v_isShared_1602_ = v_isSharedCheck_1681_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v___x_1598_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1681_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
if (lean_obj_tag(v_a_1599_) == 1)
{
lean_object* v_val_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1676_; 
lean_del_object(v___x_1601_);
v_val_1603_ = lean_ctor_get(v_a_1599_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_a_1599_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1605_ = v_a_1599_;
v_isShared_1606_ = v_isSharedCheck_1676_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_val_1603_);
lean_dec(v_a_1599_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1676_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; 
lean_inc(v_val_1603_);
v___x_1607_ = l_Lean_checkExponent(v_val_1603_, v___x_1293_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1607_) == 0)
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1667_; 
v_a_1608_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1610_ = v___x_1607_;
v_isShared_1611_ = v_isSharedCheck_1667_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1607_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1667_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
uint8_t v___x_1612_; 
v___x_1612_ = lean_unbox(v_a_1608_);
lean_dec(v_a_1608_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; lean_object* v___x_1615_; 
lean_del_object(v___x_1605_);
lean_dec(v_val_1603_);
lean_del_object(v___x_1596_);
lean_dec(v_snd_1594_);
lean_dec(v_fst_1593_);
lean_dec_ref(v_arg_1279_);
v___x_1613_ = lean_box(0);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v___x_1613_);
v___x_1615_ = v___x_1610_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
else
{
lean_object* v_u_1617_; lean_object* v_type_1618_; lean_object* v_fieldInst_1619_; lean_object* v_isChar0Inst_1620_; lean_object* v_num_1621_; lean_object* v_den_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1644_; lean_object* v___x_1657_; uint8_t v___x_1658_; 
v_u_1617_ = lean_ctor_get(v_a_1257_, 0);
v_type_1618_ = lean_ctor_get(v_a_1257_, 1);
v_fieldInst_1619_ = lean_ctor_get(v_a_1257_, 2);
v_isChar0Inst_1620_ = lean_ctor_get(v_a_1257_, 3);
v_num_1621_ = lean_ctor_get(v_fst_1593_, 0);
lean_inc(v_num_1621_);
v_den_1622_ = lean_ctor_get(v_fst_1593_, 1);
lean_inc(v_den_1622_);
v___x_1623_ = l_Rat_pow(v_fst_1593_, v_val_1603_);
v___x_1624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46));
v___x_1625_ = lean_box(0);
lean_inc(v_u_1617_);
v___x_1626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1626_, 0, v_u_1617_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
v___x_1627_ = l_Lean_mkConst(v___x_1624_, v___x_1626_);
v___x_1628_ = l_Lean_mkNatLit(v_val_1603_);
v___x_1657_ = lean_unsigned_to_nat(1u);
v___x_1658_ = lean_nat_dec_eq(v_den_1622_, v___x_1657_);
if (v___x_1658_ == 0)
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1659_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_1660_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_1661_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_1662_ = l_Lean_instToExprRat_mkInt(v_num_1621_);
lean_dec(v_num_1621_);
v___x_1663_ = lean_nat_to_int(v_den_1622_);
v___x_1664_ = l_Lean_instToExprRat_mkInt(v___x_1663_);
lean_dec(v___x_1663_);
v___x_1665_ = l_Lean_mkApp6(v___x_1659_, v___x_1660_, v___x_1660_, v___x_1660_, v___x_1661_, v___x_1662_, v___x_1664_);
v___y_1644_ = v___x_1665_;
goto v___jp_1643_;
}
else
{
lean_object* v___x_1666_; 
lean_dec(v_den_1622_);
v___x_1666_ = l_Lean_instToExprRat_mkInt(v_num_1621_);
lean_dec(v_num_1621_);
v___y_1644_ = v___x_1666_;
goto v___jp_1643_;
}
v___jp_1629_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1632_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_isChar0Inst_1620_);
lean_inc_ref(v_fieldInst_1619_);
lean_inc_ref(v_type_1618_);
v___x_1633_ = l_Lean_mkApp9(v___x_1627_, v_type_1618_, v_fieldInst_1619_, v_isChar0Inst_1620_, v_arg_1279_, v___x_1628_, v___y_1630_, v___y_1631_, v___x_1632_, v_snd_1594_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 1, v___x_1633_);
lean_ctor_set(v___x_1596_, 0, v___x_1623_);
v___x_1635_ = v___x_1596_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v___x_1633_);
v___x_1635_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1637_; 
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 0, v___x_1635_);
v___x_1637_ = v___x_1605_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1639_; 
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v___x_1637_);
v___x_1639_ = v___x_1610_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
v___jp_1643_:
{
lean_object* v_num_1645_; lean_object* v_den_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; 
v_num_1645_ = lean_ctor_get(v___x_1623_, 0);
v_den_1646_ = lean_ctor_get(v___x_1623_, 1);
v___x_1647_ = lean_unsigned_to_nat(1u);
v___x_1648_ = lean_nat_dec_eq(v_den_1646_, v___x_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1649_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_1650_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_1651_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_1652_ = l_Lean_instToExprRat_mkInt(v_num_1645_);
lean_inc(v_den_1646_);
v___x_1653_ = lean_nat_to_int(v_den_1646_);
v___x_1654_ = l_Lean_instToExprRat_mkInt(v___x_1653_);
lean_dec(v___x_1653_);
v___x_1655_ = l_Lean_mkApp6(v___x_1649_, v___x_1650_, v___x_1650_, v___x_1650_, v___x_1651_, v___x_1652_, v___x_1654_);
v___y_1630_ = v___y_1644_;
v___y_1631_ = v___x_1655_;
goto v___jp_1629_;
}
else
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_instToExprRat_mkInt(v_num_1645_);
v___y_1630_ = v___y_1644_;
v___y_1631_ = v___x_1656_;
goto v___jp_1629_;
}
}
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_del_object(v___x_1605_);
lean_dec(v_val_1603_);
lean_del_object(v___x_1596_);
lean_dec(v_snd_1594_);
lean_dec(v_fst_1593_);
lean_dec_ref(v_arg_1279_);
v_a_1668_ = lean_ctor_get(v___x_1607_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1607_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1607_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
lean_dec(v_a_1599_);
lean_del_object(v___x_1596_);
lean_dec(v_snd_1594_);
lean_dec(v_fst_1593_);
lean_dec_ref(v_arg_1279_);
v___x_1677_ = lean_box(0);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 0, v___x_1677_);
v___x_1679_ = v___x_1601_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_del_object(v___x_1596_);
lean_dec(v_snd_1594_);
lean_dec(v_fst_1593_);
lean_dec_ref(v_arg_1279_);
v_a_1682_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1598_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1598_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
return v___x_1590_;
}
}
}
}
}
else
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1699_; 
lean_dec_ref(v_arg_1282_);
lean_dec_ref(v_arg_1279_);
lean_dec_ref(v_arg_1276_);
v_a_1692_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1694_ = v___x_1438_;
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1438_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1699_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
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
lean_object* v___x_1700_; 
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_arg_1282_);
v___x_1700_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst(v_arg_1279_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1720_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1720_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1720_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
if (lean_obj_tag(v_a_1701_) == 0)
{
lean_object* v___x_1705_; lean_object* v___x_1707_; 
lean_dec_ref(v_arg_1276_);
v___x_1705_ = lean_box(0);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1705_);
v___x_1707_ = v___x_1703_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
else
{
lean_object* v_val_1709_; uint8_t v___x_1710_; 
v_val_1709_ = lean_ctor_get(v_a_1701_, 0);
lean_inc(v_val_1709_);
lean_dec_ref_known(v_a_1701_, 1);
v___x_1710_ = lean_unbox(v_val_1709_);
lean_dec(v_val_1709_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; lean_object* v___x_1713_; 
lean_dec_ref(v_arg_1276_);
v___x_1711_ = lean_box(0);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1711_);
v___x_1713_ = v___x_1703_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1711_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
else
{
lean_object* v___x_1715_; 
lean_del_object(v___x_1703_);
lean_inc_ref(v_arg_1276_);
v___x_1715_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1276_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
if (lean_obj_tag(v_a_1716_) == 0)
{
lean_dec_ref(v_arg_1276_);
return v___x_1715_;
}
else
{
lean_object* v_val_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_inc_ref(v_a_1716_);
lean_dec_ref_known(v___x_1715_, 1);
v_val_1717_ = lean_ctor_get(v_a_1716_, 0);
lean_inc(v_val_1717_);
lean_dec_ref_known(v_a_1716_, 1);
v___x_1718_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48));
v___x_1719_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(v___x_1718_, v_arg_1276_, v_val_1717_, v___f_1267_, v_a_1257_);
return v___x_1719_;
}
}
else
{
lean_dec_ref(v_arg_1276_);
return v___x_1715_;
}
}
}
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec_ref(v_arg_1276_);
v_a_1721_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1700_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1700_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
else
{
lean_object* v___x_1729_; 
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_arg_1282_);
v___x_1729_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst(v_arg_1279_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1749_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1732_ = v___x_1729_;
v_isShared_1733_ = v_isSharedCheck_1749_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_dec(v___x_1729_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1749_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
if (lean_obj_tag(v_a_1730_) == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1736_; 
lean_dec_ref(v_arg_1276_);
v___x_1734_ = lean_box(0);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v___x_1734_);
v___x_1736_ = v___x_1732_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1734_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
else
{
lean_object* v_val_1738_; uint8_t v___x_1739_; 
v_val_1738_ = lean_ctor_get(v_a_1730_, 0);
lean_inc(v_val_1738_);
lean_dec_ref_known(v_a_1730_, 1);
v___x_1739_ = lean_unbox(v_val_1738_);
lean_dec(v_val_1738_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; lean_object* v___x_1742_; 
lean_dec_ref(v_arg_1276_);
v___x_1740_ = lean_box(0);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 0, v___x_1740_);
v___x_1742_ = v___x_1732_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
else
{
lean_object* v___x_1744_; 
lean_del_object(v___x_1732_);
lean_inc_ref(v_arg_1276_);
v___x_1744_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_1276_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
if (lean_obj_tag(v_a_1745_) == 0)
{
lean_dec_ref(v_arg_1276_);
return v___x_1744_;
}
else
{
lean_object* v_val_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_inc_ref(v_a_1745_);
lean_dec_ref_known(v___x_1744_, 1);
v_val_1746_ = lean_ctor_get(v_a_1745_, 0);
lean_inc(v_val_1746_);
lean_dec_ref_known(v_a_1745_, 1);
v___x_1747_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50));
v___x_1748_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(v___x_1747_, v_arg_1276_, v_val_1746_, v___f_1266_, v_a_1257_);
return v___x_1748_;
}
}
else
{
lean_dec_ref(v_arg_1276_);
return v___x_1744_;
}
}
}
}
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_dec_ref(v_arg_1276_);
v_a_1750_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1729_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1729_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
}
else
{
lean_object* v___x_1758_; 
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_arg_1282_);
lean_inc_ref(v_arg_1279_);
v___x_1758_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst(v_arg_1276_, v_arg_1279_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1813_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1813_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1813_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
if (lean_obj_tag(v_a_1759_) == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1765_; 
lean_dec_ref(v_arg_1279_);
v___x_1763_ = lean_box(0);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1763_);
v___x_1765_ = v___x_1761_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
else
{
lean_object* v_val_1767_; uint8_t v___x_1768_; 
v_val_1767_ = lean_ctor_get(v_a_1759_, 0);
lean_inc(v_val_1767_);
lean_dec_ref_known(v_a_1759_, 1);
v___x_1768_ = lean_unbox(v_val_1767_);
lean_dec(v_val_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1771_; 
lean_dec_ref(v_arg_1279_);
v___x_1769_ = lean_box(0);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1769_);
v___x_1771_ = v___x_1761_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
else
{
lean_object* v___x_1773_; 
lean_del_object(v___x_1761_);
v___x_1773_ = l_Lean_Meta_getNatValue_x3f(v_arg_1279_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
lean_dec_ref(v_arg_1279_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1804_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1776_ = v___x_1773_;
v_isShared_1777_ = v_isSharedCheck_1804_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1773_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1804_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
if (lean_obj_tag(v_a_1774_) == 1)
{
lean_object* v_val_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1799_; 
v_val_1778_ = lean_ctor_get(v_a_1774_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_a_1774_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1780_ = v_a_1774_;
v_isShared_1781_ = v_isSharedCheck_1799_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_val_1778_);
lean_dec(v_a_1774_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1799_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v_u_1782_; lean_object* v_type_1783_; lean_object* v_fieldInst_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1794_; 
v_u_1782_ = lean_ctor_get(v_a_1257_, 0);
v_type_1783_ = lean_ctor_get(v_a_1257_, 1);
v_fieldInst_1784_ = lean_ctor_get(v_a_1257_, 2);
v___x_1785_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52));
v___x_1786_ = lean_box(0);
lean_inc(v_u_1782_);
v___x_1787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1787_, 0, v_u_1782_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = l_Lean_mkConst(v___x_1785_, v___x_1787_);
lean_inc(v_val_1778_);
v___x_1789_ = l_Lean_mkNatLit(v_val_1778_);
lean_inc_ref(v_fieldInst_1784_);
lean_inc_ref(v_type_1783_);
v___x_1790_ = l_Lean_mkApp3(v___x_1788_, v_type_1783_, v_fieldInst_1784_, v___x_1789_);
v___x_1791_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval_spec__0(v_val_1778_);
v___x_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1791_);
lean_ctor_set(v___x_1792_, 1, v___x_1790_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1792_);
v___x_1794_ = v___x_1780_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1792_);
v___x_1794_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1796_; 
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1794_);
v___x_1796_ = v___x_1776_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v___x_1794_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1802_; 
lean_dec(v_a_1774_);
v___x_1800_ = lean_box(0);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 0, v___x_1800_);
v___x_1802_ = v___x_1776_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
v_a_1805_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1773_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1773_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1821_; 
lean_dec_ref(v_arg_1279_);
v_a_1814_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1758_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1758_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1819_; 
if (v_isShared_1817_ == 0)
{
v___x_1819_ = v___x_1816_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v_a_1814_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
}
}
else
{
lean_object* v___x_1822_; 
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_arg_1282_);
v___x_1822_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNatCastInst(v_arg_1279_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1877_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1825_ = v___x_1822_;
v_isShared_1826_ = v_isSharedCheck_1877_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1822_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1877_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
if (lean_obj_tag(v_a_1823_) == 0)
{
lean_object* v___x_1827_; lean_object* v___x_1829_; 
lean_dec_ref(v_arg_1276_);
v___x_1827_ = lean_box(0);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1827_);
v___x_1829_ = v___x_1825_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
else
{
lean_object* v_val_1831_; uint8_t v___x_1832_; 
v_val_1831_ = lean_ctor_get(v_a_1823_, 0);
lean_inc(v_val_1831_);
lean_dec_ref_known(v_a_1823_, 1);
v___x_1832_ = lean_unbox(v_val_1831_);
lean_dec(v_val_1831_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1835_; 
lean_dec_ref(v_arg_1276_);
v___x_1833_ = lean_box(0);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1833_);
v___x_1835_ = v___x_1825_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
else
{
lean_object* v___x_1837_; 
lean_del_object(v___x_1825_);
v___x_1837_ = l_Lean_Meta_getNatValue_x3f(v_arg_1276_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
lean_dec_ref(v_arg_1276_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1868_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1840_ = v___x_1837_;
v_isShared_1841_ = v_isSharedCheck_1868_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1837_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1868_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
if (lean_obj_tag(v_a_1838_) == 1)
{
lean_object* v_val_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1863_; 
v_val_1842_ = lean_ctor_get(v_a_1838_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_a_1838_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1844_ = v_a_1838_;
v_isShared_1845_ = v_isSharedCheck_1863_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_val_1842_);
lean_dec(v_a_1838_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1863_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v_u_1846_; lean_object* v_type_1847_; lean_object* v_fieldInst_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1858_; 
v_u_1846_ = lean_ctor_get(v_a_1257_, 0);
v_type_1847_ = lean_ctor_get(v_a_1257_, 1);
v_fieldInst_1848_ = lean_ctor_get(v_a_1257_, 2);
v___x_1849_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54));
v___x_1850_ = lean_box(0);
lean_inc(v_u_1846_);
v___x_1851_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1851_, 0, v_u_1846_);
lean_ctor_set(v___x_1851_, 1, v___x_1850_);
v___x_1852_ = l_Lean_mkConst(v___x_1849_, v___x_1851_);
lean_inc(v_val_1842_);
v___x_1853_ = l_Lean_mkNatLit(v_val_1842_);
lean_inc_ref(v_fieldInst_1848_);
lean_inc_ref(v_type_1847_);
v___x_1854_ = l_Lean_mkApp3(v___x_1852_, v_type_1847_, v_fieldInst_1848_, v___x_1853_);
v___x_1855_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval_spec__0(v_val_1842_);
v___x_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
lean_ctor_set(v___x_1856_, 1, v___x_1854_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1856_);
v___x_1858_ = v___x_1844_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1860_; 
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1858_);
v___x_1860_ = v___x_1840_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1866_; 
lean_dec(v_a_1838_);
v___x_1864_ = lean_box(0);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1864_);
v___x_1866_ = v___x_1840_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___x_1864_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
v_a_1869_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1837_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1837_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_dec_ref(v_arg_1276_);
v_a_1878_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1822_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1822_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
}
else
{
lean_object* v___x_1886_; 
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_arg_1282_);
v___x_1886_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isIntCastInst(v_arg_1279_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1953_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1889_ = v___x_1886_;
v_isShared_1890_ = v_isSharedCheck_1953_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_a_1887_);
lean_dec(v___x_1886_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1953_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
if (lean_obj_tag(v_a_1887_) == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
lean_dec_ref(v_arg_1276_);
v___x_1891_ = lean_box(0);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v___x_1891_);
v___x_1893_ = v___x_1889_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
else
{
lean_object* v_val_1895_; uint8_t v___x_1896_; 
v_val_1895_ = lean_ctor_get(v_a_1887_, 0);
lean_inc(v_val_1895_);
lean_dec_ref_known(v_a_1887_, 1);
v___x_1896_ = lean_unbox(v_val_1895_);
lean_dec(v_val_1895_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
lean_dec_ref(v_arg_1276_);
v___x_1897_ = lean_box(0);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 0, v___x_1897_);
v___x_1899_ = v___x_1889_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
else
{
lean_object* v___x_1901_; 
lean_del_object(v___x_1889_);
v___x_1901_ = l_Lean_Meta_getIntValue_x3f(v_arg_1276_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1944_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1904_ = v___x_1901_;
v_isShared_1905_ = v_isSharedCheck_1944_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1901_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1944_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
if (lean_obj_tag(v_a_1902_) == 1)
{
lean_object* v_val_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1939_; 
v_val_1906_ = lean_ctor_get(v_a_1902_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v_a_1902_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1908_ = v_a_1902_;
v_isShared_1909_ = v_isSharedCheck_1939_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_val_1906_);
lean_dec(v_a_1902_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1939_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v_u_1910_; lean_object* v_type_1911_; lean_object* v_fieldInst_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___y_1918_; lean_object* v___x_1928_; uint8_t v___x_1929_; 
v_u_1910_ = lean_ctor_get(v_a_1257_, 0);
v_type_1911_ = lean_ctor_get(v_a_1257_, 1);
v_fieldInst_1912_ = lean_ctor_get(v_a_1257_, 2);
v___x_1913_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56));
v___x_1914_ = lean_box(0);
lean_inc(v_u_1910_);
v___x_1915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1915_, 0, v_u_1910_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = l_Lean_mkConst(v___x_1913_, v___x_1915_);
v___x_1928_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37);
v___x_1929_ = lean_int_dec_le(v___x_1928_, v_val_1906_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1930_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38);
v___x_1931_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41);
v___x_1932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44);
v___x_1933_ = lean_int_neg(v_val_1906_);
v___x_1934_ = l_Int_toNat(v___x_1933_);
lean_dec(v___x_1933_);
v___x_1935_ = l_Lean_instToExprInt_mkNat(v___x_1934_);
v___x_1936_ = l_Lean_mkApp3(v___x_1930_, v___x_1931_, v___x_1932_, v___x_1935_);
v___y_1918_ = v___x_1936_;
goto v___jp_1917_;
}
else
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1937_ = l_Int_toNat(v_val_1906_);
v___x_1938_ = l_Lean_instToExprInt_mkNat(v___x_1937_);
v___y_1918_ = v___x_1938_;
goto v___jp_1917_;
}
v___jp_1917_:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1923_; 
lean_inc_ref(v_fieldInst_1912_);
lean_inc_ref(v_type_1911_);
v___x_1919_ = l_Lean_mkApp3(v___x_1916_, v_type_1911_, v_fieldInst_1912_, v___y_1918_);
v___x_1920_ = l_Rat_ofInt(v_val_1906_);
v___x_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1920_);
lean_ctor_set(v___x_1921_, 1, v___x_1919_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v___x_1921_);
v___x_1923_ = v___x_1908_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1925_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1923_);
v___x_1925_ = v___x_1904_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
else
{
lean_object* v___x_1940_; lean_object* v___x_1942_; 
lean_dec(v_a_1902_);
v___x_1940_ = lean_box(0);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1940_);
v___x_1942_ = v___x_1904_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v___x_1940_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
v_a_1945_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1901_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1901_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec_ref(v_arg_1276_);
v_a_1954_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1886_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1886_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
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
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
v_a_1962_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1272_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1272_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
v___jp_1263_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1264_ = lean_box(0);
v___x_1265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
return v___x_1265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___boxed(lean_object* v_e_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_e_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_);
lean_dec(v_a_1975_);
lean_dec_ref(v_a_1974_);
lean_dec(v_a_1973_);
lean_dec_ref(v_a_1972_);
lean_dec_ref(v_a_1971_);
return v_res_1977_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(lean_object* v_e_1978_){
_start:
{
lean_object* v_a_1980_; lean_object* v_b_1981_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v___x_1984_ = l_Lean_Expr_cleanupAnnotations(v_e_1978_);
v___x_1985_ = l_Lean_Expr_isApp(v___x_1984_);
if (v___x_1985_ == 0)
{
lean_dec_ref(v___x_1984_);
return v___x_1985_;
}
else
{
lean_object* v_arg_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
v_arg_1986_ = lean_ctor_get(v___x_1984_, 1);
lean_inc_ref(v_arg_1986_);
v___x_1987_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1984_);
v___x_1988_ = l_Lean_Expr_isApp(v___x_1987_);
if (v___x_1988_ == 0)
{
lean_dec_ref(v___x_1987_);
lean_dec_ref(v_arg_1986_);
return v___x_1988_;
}
else
{
lean_object* v_arg_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v_arg_1989_ = lean_ctor_get(v___x_1987_, 1);
lean_inc_ref(v_arg_1989_);
v___x_1990_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1987_);
v___x_1991_ = l_Lean_Expr_isApp(v___x_1990_);
if (v___x_1991_ == 0)
{
lean_dec_ref(v___x_1990_);
lean_dec_ref(v_arg_1989_);
lean_dec_ref(v_arg_1986_);
return v___x_1991_;
}
else
{
lean_object* v___x_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v___x_1992_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1990_);
v___x_1993_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1));
v___x_1994_ = l_Lean_Expr_isConstOf(v___x_1992_, v___x_1993_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1));
v___x_1996_ = l_Lean_Expr_isConstOf(v___x_1992_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; uint8_t v___x_1998_; 
v___x_1997_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7));
v___x_1998_ = l_Lean_Expr_isConstOf(v___x_1992_, v___x_1997_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; uint8_t v___x_2000_; 
v___x_1999_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10));
v___x_2000_ = l_Lean_Expr_isConstOf(v___x_1992_, v___x_1999_);
if (v___x_2000_ == 0)
{
lean_object* v___x_2001_; uint8_t v___x_2002_; 
v___x_2001_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13));
v___x_2002_ = l_Lean_Expr_isConstOf(v___x_1992_, v___x_2001_);
if (v___x_2002_ == 0)
{
uint8_t v___x_2003_; 
v___x_2003_ = l_Lean_Expr_isApp(v___x_1992_);
if (v___x_2003_ == 0)
{
lean_dec_ref(v___x_1992_);
lean_dec_ref(v_arg_1989_);
lean_dec_ref(v_arg_1986_);
return v___x_2003_;
}
else
{
lean_object* v___x_2004_; uint8_t v___x_2005_; 
v___x_2004_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1992_);
v___x_2005_ = l_Lean_Expr_isApp(v___x_2004_);
if (v___x_2005_ == 0)
{
lean_dec_ref(v___x_2004_);
lean_dec_ref(v_arg_1989_);
lean_dec_ref(v_arg_1986_);
return v___x_2005_;
}
else
{
lean_object* v___x_2006_; uint8_t v___x_2007_; 
v___x_2006_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2004_);
v___x_2007_ = l_Lean_Expr_isApp(v___x_2006_);
if (v___x_2007_ == 0)
{
lean_dec_ref(v___x_2006_);
lean_dec_ref(v_arg_1989_);
lean_dec_ref(v_arg_1986_);
return v___x_2007_;
}
else
{
lean_object* v___x_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; 
v___x_2008_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2006_);
v___x_2009_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16));
v___x_2010_ = l_Lean_Expr_isConstOf(v___x_2008_, v___x_2009_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2));
v___x_2012_ = l_Lean_Expr_isConstOf(v___x_2008_, v___x_2011_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2013_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19));
v___x_2014_ = l_Lean_Expr_isConstOf(v___x_2008_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2015_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__22));
v___x_2016_ = l_Lean_Expr_isConstOf(v___x_2008_, v___x_2015_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__25));
v___x_2018_ = l_Lean_Expr_isConstOf(v___x_2008_, v___x_2017_);
lean_dec_ref(v___x_2008_);
if (v___x_2018_ == 0)
{
lean_dec_ref(v_arg_1989_);
lean_dec_ref(v_arg_1986_);
return v___x_2018_;
}
else
{
v_a_1980_ = v_arg_1989_;
v_b_1981_ = v_arg_1986_;
goto v___jp_1979_;
}
}
else
{
lean_dec_ref(v___x_2008_);
v_a_1980_ = v_arg_1989_;
v_b_1981_ = v_arg_1986_;
goto v___jp_1979_;
}
}
else
{
lean_dec_ref(v___x_2008_);
v_a_1980_ = v_arg_1989_;
v_b_1981_ = v_arg_1986_;
goto v___jp_1979_;
}
}
else
{
lean_dec_ref(v___x_2008_);
v_a_1980_ = v_arg_1989_;
v_b_1981_ = v_arg_1986_;
goto v___jp_1979_;
}
}
else
{
lean_dec_ref(v___x_2008_);
v_a_1980_ = v_arg_1989_;
v_b_1981_ = v_arg_1986_;
goto v___jp_1979_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1992_);
lean_dec_ref(v_arg_1989_);
v_e_1978_ = v_arg_1986_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_1992_);
lean_dec_ref(v_arg_1989_);
v_e_1978_ = v_arg_1986_;
goto _start;
}
}
else
{
lean_dec_ref(v___x_1992_);
lean_dec_ref(v_arg_1989_);
lean_dec_ref(v_arg_1986_);
return v___x_1998_;
}
}
else
{
lean_dec_ref(v___x_1992_);
lean_dec_ref(v_arg_1989_);
lean_dec_ref(v_arg_1986_);
return v___x_1996_;
}
}
else
{
lean_dec_ref(v___x_1992_);
lean_dec_ref(v_arg_1989_);
lean_dec_ref(v_arg_1986_);
return v___x_1994_;
}
}
}
}
v___jp_1979_:
{
uint8_t v___x_1982_; 
v___x_1982_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(v_a_1980_);
if (v___x_1982_ == 0)
{
lean_dec_ref(v_b_1981_);
return v___x_1982_;
}
else
{
v_e_1978_ = v_b_1981_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable___boxed(lean_object* v_e_2021_){
_start:
{
uint8_t v_res_2022_; lean_object* v_r_2023_; 
v_res_2022_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(v_e_2021_);
v_r_2023_ = lean_box(v_res_2022_);
return v_r_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalFieldExpr_x3f(lean_object* v_e_2024_, lean_object* v_type_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_){
_start:
{
uint8_t v___x_2031_; 
lean_inc_ref(v_e_2024_);
v___x_2031_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(v_e_2024_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
lean_dec_ref(v_type_2025_);
lean_dec_ref(v_e_2024_);
v___x_2032_ = lean_box(0);
v___x_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
return v___x_2033_;
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___boxed), 7, 1);
lean_closure_set(v___x_2034_, 0, v_e_2024_);
v___x_2035_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg(v_type_2025_, v___x_2034_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
return v___x_2035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalFieldExpr_x3f___boxed(lean_object* v_e_2036_, lean_object* v_type_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_Meta_Grind_Arith_evalFieldExpr_x3f(v_e_2036_, v_type_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_);
lean_dec(v_a_2041_);
lean_dec_ref(v_a_2040_);
lean_dec(v_a_2039_);
lean_dec_ref(v_a_2038_);
return v_res_2043_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = lean_unsigned_to_nat(1u);
v___x_2045_ = lean_nat_to_int(v___x_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0(lean_object* v_e_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v___x_2074_; 
lean_inc_ref(v_e_2067_);
v___x_2074_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_e_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2307_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2077_ = v___x_2074_;
v_isShared_2078_ = v_isSharedCheck_2307_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2307_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
if (lean_obj_tag(v_a_2075_) == 0)
{
lean_object* v___x_2079_; lean_object* v___x_2081_; 
lean_dec_ref(v_e_2067_);
v___x_2079_ = lean_box(0);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2079_);
v___x_2081_ = v___x_2077_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
else
{
lean_object* v_val_2083_; lean_object* v_fst_2084_; lean_object* v_snd_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2306_; 
lean_del_object(v___x_2077_);
v_val_2083_ = lean_ctor_get(v_a_2075_, 0);
lean_inc(v_val_2083_);
lean_dec_ref_known(v_a_2075_, 1);
v_fst_2084_ = lean_ctor_get(v_val_2083_, 0);
v_snd_2085_ = lean_ctor_get(v_val_2083_, 1);
v_isSharedCheck_2306_ = !lean_is_exclusive(v_val_2083_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2087_ = v_val_2083_;
v_isShared_2088_ = v_isSharedCheck_2306_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_snd_2085_);
lean_inc(v_fst_2084_);
lean_dec(v_val_2083_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2306_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v_num_2089_; lean_object* v_den_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2305_; 
v_num_2089_ = lean_ctor_get(v_fst_2084_, 0);
v_den_2090_ = lean_ctor_get(v_fst_2084_, 1);
v_isSharedCheck_2305_ = !lean_is_exclusive(v_fst_2084_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2092_ = v_fst_2084_;
v_isShared_2093_ = v_isSharedCheck_2305_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_den_2090_);
lean_inc(v_num_2089_);
lean_dec(v_fst_2084_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2305_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; uint8_t v___x_2095_; 
v___x_2094_ = lean_unsigned_to_nat(1u);
v___x_2095_ = lean_nat_dec_eq(v_den_2090_, v___x_2094_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; uint8_t v___x_2097_; 
v___x_2096_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__0);
v___x_2097_ = lean_int_dec_eq(v_num_2089_, v___x_2096_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; 
v___x_2098_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast(v_num_2089_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v_val_2100_; lean_object* v___x_2101_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref_known(v___x_2098_, 1);
v_val_2100_ = lean_ctor_get(v_a_2099_, 0);
lean_inc(v_val_2100_);
lean_dec(v_a_2099_);
lean_inc(v_den_2090_);
v___x_2101_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast(v_den_2090_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2101_) == 0)
{
lean_object* v_a_2102_; lean_object* v_val_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2175_; 
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref_known(v___x_2101_, 1);
v_val_2103_ = lean_ctor_get(v_a_2102_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v_a_2102_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2105_ = v_a_2102_;
v_isShared_2106_ = v_isSharedCheck_2175_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_val_2103_);
lean_dec(v_a_2102_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2175_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10));
v___x_2108_ = lean_mk_empty_array_with_capacity(v___x_2094_);
v___x_2109_ = lean_array_push(v___x_2108_, v_val_2103_);
v___x_2110_ = l_Lean_Meta_mkAppM(v___x_2107_, v___x_2109_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___x_2112_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref_known(v___x_2110_, 1);
v___x_2112_ = l_Lean_Meta_mkMul(v_val_2100_, v_a_2111_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2158_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2158_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2158_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v_u_2117_; lean_object* v_type_2118_; lean_object* v_fieldInst_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2123_; 
v_u_2117_ = lean_ctor_get(v___y_2068_, 0);
v_type_2118_ = lean_ctor_get(v___y_2068_, 1);
v_fieldInst_2119_ = lean_ctor_get(v___y_2068_, 2);
v___x_2120_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2));
v___x_2121_ = lean_box(0);
lean_inc(v_u_2117_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set_tag(v___x_2092_, 1);
lean_ctor_set(v___x_2092_, 1, v___x_2121_);
lean_ctor_set(v___x_2092_, 0, v_u_2117_);
v___x_2123_ = v___x_2092_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_u_2117_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v___x_2121_);
v___x_2123_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___y_2133_; lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2124_ = l_Lean_mkConst(v___x_2120_, v___x_2123_);
v___x_2125_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_2126_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_2127_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_2128_ = l_Lean_instToExprRat_mkInt(v_num_2089_);
lean_inc(v_den_2090_);
v___x_2129_ = lean_nat_to_int(v_den_2090_);
v___x_2130_ = l_Lean_instToExprRat_mkInt(v___x_2129_);
lean_dec(v___x_2129_);
v___x_2131_ = l_Lean_mkApp6(v___x_2125_, v___x_2126_, v___x_2126_, v___x_2126_, v___x_2127_, v___x_2128_, v___x_2130_);
v___x_2146_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37);
v___x_2147_ = lean_int_dec_le(v___x_2146_, v_num_2089_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2148_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38);
v___x_2149_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41);
v___x_2150_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44);
v___x_2151_ = lean_int_neg(v_num_2089_);
lean_dec(v_num_2089_);
v___x_2152_ = l_Int_toNat(v___x_2151_);
lean_dec(v___x_2151_);
v___x_2153_ = l_Lean_instToExprInt_mkNat(v___x_2152_);
v___x_2154_ = l_Lean_mkApp3(v___x_2148_, v___x_2149_, v___x_2150_, v___x_2153_);
v___y_2133_ = v___x_2154_;
goto v___jp_2132_;
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = l_Int_toNat(v_num_2089_);
lean_dec(v_num_2089_);
v___x_2156_ = l_Lean_instToExprInt_mkNat(v___x_2155_);
v___y_2133_ = v___x_2156_;
goto v___jp_2132_;
}
v___jp_2132_:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2138_; 
v___x_2134_ = l_Lean_mkNatLit(v_den_2090_);
v___x_2135_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_fieldInst_2119_);
lean_inc_ref(v_type_2118_);
v___x_2136_ = l_Lean_mkApp8(v___x_2124_, v_type_2118_, v_fieldInst_2119_, v_e_2067_, v___x_2131_, v___y_2133_, v___x_2134_, v___x_2135_, v_snd_2085_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 1, v___x_2136_);
lean_ctor_set(v___x_2087_, 0, v_a_2113_);
v___x_2138_ = v___x_2087_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2113_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2140_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v___x_2138_);
v___x_2140_ = v___x_2105_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
lean_object* v___x_2142_; 
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2140_);
v___x_2142_ = v___x_2115_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_del_object(v___x_2105_);
lean_del_object(v___x_2092_);
lean_dec(v_den_2090_);
lean_dec(v_num_2089_);
lean_del_object(v___x_2087_);
lean_dec(v_snd_2085_);
lean_dec_ref(v_e_2067_);
v_a_2159_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2112_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2112_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_del_object(v___x_2105_);
lean_dec(v_val_2100_);
lean_del_object(v___x_2092_);
lean_dec(v_den_2090_);
lean_dec(v_num_2089_);
lean_del_object(v___x_2087_);
lean_dec(v_snd_2085_);
lean_dec_ref(v_e_2067_);
v_a_2167_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2110_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2110_);
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
}
else
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
lean_dec(v_val_2100_);
lean_del_object(v___x_2092_);
lean_dec(v_den_2090_);
lean_dec(v_num_2089_);
lean_del_object(v___x_2087_);
lean_dec(v_snd_2085_);
lean_dec_ref(v_e_2067_);
v_a_2176_ = lean_ctor_get(v___x_2101_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___x_2101_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2101_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_del_object(v___x_2092_);
lean_dec(v_den_2090_);
lean_dec(v_num_2089_);
lean_del_object(v___x_2087_);
lean_dec(v_snd_2085_);
lean_dec_ref(v_e_2067_);
v_a_2184_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2098_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2098_);
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
lean_object* v___x_2192_; 
lean_inc(v_den_2090_);
v___x_2192_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast(v_den_2090_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v_val_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2243_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2192_, 1);
v_val_2194_ = lean_ctor_get(v_a_2193_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v_a_2193_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2196_ = v_a_2193_;
v_isShared_2197_ = v_isSharedCheck_2243_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_val_2194_);
lean_dec(v_a_2193_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2243_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2198_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10));
v___x_2199_ = lean_mk_empty_array_with_capacity(v___x_2094_);
v___x_2200_ = lean_array_push(v___x_2199_, v_val_2194_);
v___x_2201_ = l_Lean_Meta_mkAppM(v___x_2198_, v___x_2200_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2234_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2204_ = v___x_2201_;
v_isShared_2205_ = v_isSharedCheck_2234_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2201_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2234_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v_u_2206_; lean_object* v_type_2207_; lean_object* v_fieldInst_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2212_; 
v_u_2206_ = lean_ctor_get(v___y_2068_, 0);
v_type_2207_ = lean_ctor_get(v___y_2068_, 1);
v_fieldInst_2208_ = lean_ctor_get(v___y_2068_, 2);
v___x_2209_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4));
v___x_2210_ = lean_box(0);
lean_inc(v_u_2206_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set_tag(v___x_2092_, 1);
lean_ctor_set(v___x_2092_, 1, v___x_2210_);
lean_ctor_set(v___x_2092_, 0, v_u_2206_);
v___x_2212_ = v___x_2092_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v_u_2206_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2213_ = l_Lean_mkConst(v___x_2209_, v___x_2212_);
v___x_2214_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
v___x_2215_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
v___x_2216_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
v___x_2217_ = l_Lean_instToExprRat_mkInt(v_num_2089_);
lean_dec(v_num_2089_);
lean_inc(v_den_2090_);
v___x_2218_ = lean_nat_to_int(v_den_2090_);
v___x_2219_ = l_Lean_instToExprRat_mkInt(v___x_2218_);
lean_dec(v___x_2218_);
v___x_2220_ = l_Lean_mkApp6(v___x_2214_, v___x_2215_, v___x_2215_, v___x_2215_, v___x_2216_, v___x_2217_, v___x_2219_);
v___x_2221_ = l_Lean_mkNatLit(v_den_2090_);
v___x_2222_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_fieldInst_2208_);
lean_inc_ref(v_type_2207_);
v___x_2223_ = l_Lean_mkApp7(v___x_2213_, v_type_2207_, v_fieldInst_2208_, v_e_2067_, v___x_2220_, v___x_2221_, v___x_2222_, v_snd_2085_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 1, v___x_2223_);
lean_ctor_set(v___x_2087_, 0, v_a_2202_);
v___x_2225_ = v___x_2087_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2202_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2227_; 
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 0, v___x_2225_);
v___x_2227_ = v___x_2196_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2229_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2227_);
v___x_2229_ = v___x_2204_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
}
}
else
{
lean_object* v_a_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
lean_del_object(v___x_2196_);
lean_del_object(v___x_2092_);
lean_dec(v_den_2090_);
lean_dec(v_num_2089_);
lean_del_object(v___x_2087_);
lean_dec(v_snd_2085_);
lean_dec_ref(v_e_2067_);
v_a_2235_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2237_ = v___x_2201_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_a_2235_);
lean_dec(v___x_2201_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
}
else
{
lean_object* v_a_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2251_; 
lean_del_object(v___x_2092_);
lean_dec(v_den_2090_);
lean_dec(v_num_2089_);
lean_del_object(v___x_2087_);
lean_dec(v_snd_2085_);
lean_dec_ref(v_e_2067_);
v_a_2244_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2251_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2251_ == 0)
{
v___x_2246_ = v___x_2192_;
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_a_2244_);
lean_dec(v___x_2192_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2251_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2249_; 
if (v_isShared_2247_ == 0)
{
v___x_2249_ = v___x_2246_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_a_2244_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
else
{
lean_object* v___x_2252_; 
lean_dec(v_den_2090_);
v___x_2252_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast(v_num_2089_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2296_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2255_ = v___x_2252_;
v_isShared_2256_ = v_isSharedCheck_2296_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2296_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v_val_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2295_; 
v_val_2257_ = lean_ctor_get(v_a_2253_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v_a_2253_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2259_ = v_a_2253_;
v_isShared_2260_ = v_isSharedCheck_2295_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_val_2257_);
lean_dec(v_a_2253_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2295_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v_u_2261_; lean_object* v_type_2262_; lean_object* v_fieldInst_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2267_; 
v_u_2261_ = lean_ctor_get(v___y_2068_, 0);
v_type_2262_ = lean_ctor_get(v___y_2068_, 1);
v_fieldInst_2263_ = lean_ctor_get(v___y_2068_, 2);
v___x_2264_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6));
v___x_2265_ = lean_box(0);
lean_inc(v_u_2261_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set_tag(v___x_2092_, 1);
lean_ctor_set(v___x_2092_, 1, v___x_2265_);
lean_ctor_set(v___x_2092_, 0, v_u_2261_);
v___x_2267_ = v___x_2092_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_u_2261_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v___x_2265_);
v___x_2267_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___y_2271_; lean_object* v___x_2283_; uint8_t v___x_2284_; 
v___x_2268_ = l_Lean_mkConst(v___x_2264_, v___x_2267_);
v___x_2269_ = l_Lean_instToExprRat_mkInt(v_num_2089_);
v___x_2283_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37);
v___x_2284_ = lean_int_dec_le(v___x_2283_, v_num_2089_);
if (v___x_2284_ == 0)
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2285_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38);
v___x_2286_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41);
v___x_2287_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44, &l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44);
v___x_2288_ = lean_int_neg(v_num_2089_);
lean_dec(v_num_2089_);
v___x_2289_ = l_Int_toNat(v___x_2288_);
lean_dec(v___x_2288_);
v___x_2290_ = l_Lean_instToExprInt_mkNat(v___x_2289_);
v___x_2291_ = l_Lean_mkApp3(v___x_2285_, v___x_2286_, v___x_2287_, v___x_2290_);
v___y_2271_ = v___x_2291_;
goto v___jp_2270_;
}
else
{
lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2292_ = l_Int_toNat(v_num_2089_);
lean_dec(v_num_2089_);
v___x_2293_ = l_Lean_instToExprInt_mkNat(v___x_2292_);
v___y_2271_ = v___x_2293_;
goto v___jp_2270_;
}
v___jp_2270_:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2275_; 
v___x_2272_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v_fieldInst_2263_);
lean_inc_ref(v_type_2262_);
v___x_2273_ = l_Lean_mkApp7(v___x_2268_, v_type_2262_, v_fieldInst_2263_, v_e_2067_, v___x_2269_, v___y_2271_, v___x_2272_, v_snd_2085_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 1, v___x_2273_);
lean_ctor_set(v___x_2087_, 0, v_val_2257_);
v___x_2275_ = v___x_2087_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_val_2257_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v___x_2273_);
v___x_2275_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
lean_object* v___x_2277_; 
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2275_);
v___x_2277_ = v___x_2259_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
lean_object* v___x_2279_; 
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v___x_2277_);
v___x_2279_ = v___x_2255_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2277_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
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
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_del_object(v___x_2092_);
lean_dec(v_num_2089_);
lean_del_object(v___x_2087_);
lean_dec(v_snd_2085_);
lean_dec_ref(v_e_2067_);
v_a_2297_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2252_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2252_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
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
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec_ref(v_e_2067_);
v_a_2308_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2074_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2074_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___boxed(lean_object* v_e_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0(v_e_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec_ref(v___y_2317_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f(lean_object* v_e_2324_, lean_object* v_type_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_){
_start:
{
uint8_t v___x_2331_; 
lean_inc_ref(v_e_2324_);
v___x_2331_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(v_e_2324_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
lean_dec_ref(v_type_2325_);
lean_dec_ref(v_e_2324_);
v___x_2332_ = lean_box(0);
v___x_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
return v___x_2333_;
}
else
{
lean_object* v___f_2334_; lean_object* v___x_2335_; 
v___f_2334_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2334_, 0, v_e_2324_);
v___x_2335_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg(v_type_2325_, v___f_2334_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_);
return v___x_2335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___boxed(lean_object* v_e_2336_, lean_object* v_type_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Lean_Meta_Grind_Arith_normFieldExpr_x3f(v_e_2336_, v_type_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
lean_dec(v_a_2341_);
lean_dec_ref(v_a_2340_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2338_);
return v_res_2343_;
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

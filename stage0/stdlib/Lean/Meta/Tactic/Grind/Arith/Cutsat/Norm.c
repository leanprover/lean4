// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util public import Lean.Meta.IntInstTesters
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
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHSubInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstNegInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_mk_var(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHSubInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstNegInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__8(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__3_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__4_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__6_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__7_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__9_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__10_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__12_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__13_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__14_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExprWith___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExprWith___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExprWith___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExprWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExprWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00Lean_Meta_Grind_Arith_Cutsat_toLinearExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00Lean_Meta_Grind_Arith_Cutsat_toLinearExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__0(lean_object* v_toPure_1_, lean_object* v_toVar_2_, lean_object* v_e_3_, lean_object* v_generation_4_, lean_object* v_____do__lift_5_){
_start:
{
if (lean_obj_tag(v_____do__lift_5_) == 1)
{
lean_object* v_val_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_14_; 
lean_dec(v_generation_4_);
lean_dec_ref(v_e_3_);
lean_dec(v_toVar_2_);
v_val_6_ = lean_ctor_get(v_____do__lift_5_, 0);
v_isSharedCheck_14_ = !lean_is_exclusive(v_____do__lift_5_);
if (v_isSharedCheck_14_ == 0)
{
v___x_8_ = v_____do__lift_5_;
v_isShared_9_ = v_isSharedCheck_14_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_val_6_);
lean_dec(v_____do__lift_5_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_14_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_11_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set_tag(v___x_8_, 0);
v___x_11_ = v___x_8_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v_val_6_);
v___x_11_ = v_reuseFailAlloc_13_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
lean_object* v___x_12_; 
v___x_12_ = lean_apply_2(v_toPure_1_, lean_box(0), v___x_11_);
return v___x_12_;
}
}
}
else
{
lean_object* v___x_15_; 
lean_dec(v_____do__lift_5_);
lean_dec(v_toPure_1_);
v___x_15_ = lean_apply_2(v_toVar_2_, v_e_3_, v_generation_4_);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__1(lean_object* v_toPure_16_, lean_object* v_____do__lift_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_18_, 0, v_____do__lift_17_);
v___x_19_ = lean_apply_2(v_toPure_16_, lean_box(0), v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__2(lean_object* v_____do__lift_20_, lean_object* v_toPure_21_, lean_object* v_____do__lift_22_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_23_, 0, v_____do__lift_20_);
lean_ctor_set(v___x_23_, 1, v_____do__lift_22_);
v___x_24_ = lean_apply_2(v_toPure_21_, lean_box(0), v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__15(lean_object* v___f_25_, lean_object* v_t_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_apply_1(v___f_25_, v_t_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__5(lean_object* v_____do__lift_28_, lean_object* v_toPure_29_, lean_object* v_____do__lift_30_){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_31_, 0, v_____do__lift_28_);
lean_ctor_set(v___x_31_, 1, v_____do__lift_30_);
v___x_32_ = lean_apply_2(v_toPure_29_, lean_box(0), v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__10(lean_object* v_val_33_, lean_object* v_toPure_34_, lean_object* v_____do__lift_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_36_, 0, v_val_33_);
lean_ctor_set(v___x_36_, 1, v_____do__lift_35_);
v___x_37_ = lean_apply_2(v_toPure_34_, lean_box(0), v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__12(lean_object* v_toVar_38_, lean_object* v_e_39_, lean_object* v_generation_40_, lean_object* v_arg_41_, lean_object* v_inst_42_, lean_object* v_toBind_43_, lean_object* v___f_44_, uint8_t v_____do__lift_45_){
_start:
{
if (v_____do__lift_45_ == 0)
{
lean_object* v___x_46_; 
lean_dec(v___f_44_);
lean_dec(v_toBind_43_);
lean_dec(v_inst_42_);
lean_dec_ref(v_arg_41_);
v___x_46_ = lean_apply_2(v_toVar_38_, v_e_39_, v_generation_40_);
return v___x_46_;
}
else
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
lean_dec(v_generation_40_);
lean_dec_ref(v_e_39_);
lean_dec(v_toVar_38_);
v___x_47_ = lean_alloc_closure((void*)(l_Lean_Meta_getIntValue_x3f___boxed), 6, 1);
lean_closure_set(v___x_47_, 0, v_arg_41_);
v___x_48_ = lean_apply_2(v_inst_42_, lean_box(0), v___x_47_);
v___x_49_ = lean_apply_4(v_toBind_43_, lean_box(0), lean_box(0), v___x_48_, v___f_44_);
return v___x_49_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__12___boxed(lean_object* v_toVar_50_, lean_object* v_e_51_, lean_object* v_generation_52_, lean_object* v_arg_53_, lean_object* v_inst_54_, lean_object* v_toBind_55_, lean_object* v___f_56_, lean_object* v_____do__lift_57_){
_start:
{
uint8_t v_____do__lift_1119__boxed_58_; lean_object* v_res_59_; 
v_____do__lift_1119__boxed_58_ = lean_unbox(v_____do__lift_57_);
v_res_59_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__12(v_toVar_50_, v_e_51_, v_generation_52_, v_arg_53_, v_inst_54_, v_toBind_55_, v___f_56_, v_____do__lift_1119__boxed_58_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__8(lean_object* v_val_60_, lean_object* v_toPure_61_, lean_object* v_____do__lift_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_63_, 0, v_____do__lift_62_);
lean_ctor_set(v___x_63_, 1, v_val_60_);
v___x_64_ = lean_apply_2(v_toPure_61_, lean_box(0), v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__4(lean_object* v_toVar_90_, lean_object* v_e_91_, lean_object* v_generation_92_, lean_object* v_toPure_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_arg_96_, lean_object* v_toBind_97_, lean_object* v_arg_98_, uint8_t v_____do__lift_99_){
_start:
{
if (v_____do__lift_99_ == 0)
{
lean_object* v___x_100_; 
lean_dec_ref(v_arg_98_);
lean_dec(v_toBind_97_);
lean_dec_ref(v_arg_96_);
lean_dec(v_inst_95_);
lean_dec_ref(v_inst_94_);
lean_dec(v_toPure_93_);
v___x_100_ = lean_apply_2(v_toVar_90_, v_e_91_, v_generation_92_);
return v___x_100_;
}
else
{
lean_object* v___x_101_; lean_object* v___f_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
lean_dec(v_generation_92_);
lean_dec_ref(v_e_91_);
v___x_101_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_97_);
lean_inc(v_toVar_90_);
lean_inc(v_inst_95_);
lean_inc_ref(v_inst_94_);
v___f_102_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__3), 8, 7);
lean_closure_set(v___f_102_, 0, v_toPure_93_);
lean_closure_set(v___f_102_, 1, v_inst_94_);
lean_closure_set(v___f_102_, 2, v_inst_95_);
lean_closure_set(v___f_102_, 3, v_toVar_90_);
lean_closure_set(v___f_102_, 4, v_arg_96_);
lean_closure_set(v___f_102_, 5, v___x_101_);
lean_closure_set(v___f_102_, 6, v_toBind_97_);
v___x_103_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg(v_inst_94_, v_inst_95_, v_toVar_90_, v_arg_98_, v___x_101_);
v___x_104_ = lean_apply_4(v_toBind_97_, lean_box(0), lean_box(0), v___x_103_, v___f_102_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__4___boxed(lean_object* v_toVar_105_, lean_object* v_e_106_, lean_object* v_generation_107_, lean_object* v_toPure_108_, lean_object* v_inst_109_, lean_object* v_inst_110_, lean_object* v_arg_111_, lean_object* v_toBind_112_, lean_object* v_arg_113_, lean_object* v_____do__lift_114_){
_start:
{
uint8_t v_____do__lift_1198__boxed_115_; lean_object* v_res_116_; 
v_____do__lift_1198__boxed_115_ = lean_unbox(v_____do__lift_114_);
v_res_116_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__4(v_toVar_105_, v_e_106_, v_generation_107_, v_toPure_108_, v_inst_109_, v_inst_110_, v_arg_111_, v_toBind_112_, v_arg_113_, v_____do__lift_1198__boxed_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__6(lean_object* v_toPure_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_toVar_120_, lean_object* v_arg_121_, lean_object* v___x_122_, lean_object* v_toBind_123_, lean_object* v_____do__lift_124_){
_start:
{
lean_object* v___f_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___f_125_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__5), 3, 2);
lean_closure_set(v___f_125_, 0, v_____do__lift_124_);
lean_closure_set(v___f_125_, 1, v_toPure_117_);
v___x_126_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg(v_inst_118_, v_inst_119_, v_toVar_120_, v_arg_121_, v___x_122_);
v___x_127_ = lean_apply_4(v_toBind_123_, lean_box(0), lean_box(0), v___x_126_, v___f_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__7(lean_object* v_toVar_128_, lean_object* v_e_129_, lean_object* v_generation_130_, lean_object* v_toPure_131_, lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_arg_134_, lean_object* v_toBind_135_, lean_object* v_arg_136_, uint8_t v_____do__lift_137_){
_start:
{
if (v_____do__lift_137_ == 0)
{
lean_object* v___x_138_; 
lean_dec_ref(v_arg_136_);
lean_dec(v_toBind_135_);
lean_dec_ref(v_arg_134_);
lean_dec(v_inst_133_);
lean_dec_ref(v_inst_132_);
lean_dec(v_toPure_131_);
v___x_138_ = lean_apply_2(v_toVar_128_, v_e_129_, v_generation_130_);
return v___x_138_;
}
else
{
lean_object* v___x_139_; lean_object* v___f_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
lean_dec(v_generation_130_);
lean_dec_ref(v_e_129_);
v___x_139_ = lean_unsigned_to_nat(0u);
lean_inc(v_toBind_135_);
lean_inc(v_toVar_128_);
lean_inc(v_inst_133_);
lean_inc_ref(v_inst_132_);
v___f_140_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__6), 8, 7);
lean_closure_set(v___f_140_, 0, v_toPure_131_);
lean_closure_set(v___f_140_, 1, v_inst_132_);
lean_closure_set(v___f_140_, 2, v_inst_133_);
lean_closure_set(v___f_140_, 3, v_toVar_128_);
lean_closure_set(v___f_140_, 4, v_arg_134_);
lean_closure_set(v___f_140_, 5, v___x_139_);
lean_closure_set(v___f_140_, 6, v_toBind_135_);
v___x_141_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg(v_inst_132_, v_inst_133_, v_toVar_128_, v_arg_136_, v___x_139_);
v___x_142_ = lean_apply_4(v_toBind_135_, lean_box(0), lean_box(0), v___x_141_, v___f_140_);
return v___x_142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__7___boxed(lean_object* v_toVar_143_, lean_object* v_e_144_, lean_object* v_generation_145_, lean_object* v_toPure_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_arg_149_, lean_object* v_toBind_150_, lean_object* v_arg_151_, lean_object* v_____do__lift_152_){
_start:
{
uint8_t v_____do__lift_1208__boxed_153_; lean_object* v_res_154_; 
v_____do__lift_1208__boxed_153_ = lean_unbox(v_____do__lift_152_);
v_res_154_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__7(v_toVar_143_, v_e_144_, v_generation_145_, v_toPure_146_, v_inst_147_, v_inst_148_, v_arg_149_, v_toBind_150_, v_arg_151_, v_____do__lift_1208__boxed_153_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__9(lean_object* v_toVar_155_, lean_object* v_e_156_, lean_object* v_generation_157_, lean_object* v_toPure_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_arg_161_, lean_object* v_toBind_162_, lean_object* v_____do__lift_163_){
_start:
{
if (lean_obj_tag(v_____do__lift_163_) == 0)
{
lean_object* v___x_164_; 
lean_dec(v_toBind_162_);
lean_dec_ref(v_arg_161_);
lean_dec(v_inst_160_);
lean_dec_ref(v_inst_159_);
lean_dec(v_toPure_158_);
v___x_164_ = lean_apply_2(v_toVar_155_, v_e_156_, v_generation_157_);
return v___x_164_;
}
else
{
lean_object* v_val_165_; lean_object* v___f_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec(v_generation_157_);
lean_dec_ref(v_e_156_);
v_val_165_ = lean_ctor_get(v_____do__lift_163_, 0);
lean_inc(v_val_165_);
lean_dec_ref_known(v_____do__lift_163_, 1);
v___f_166_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__8), 3, 2);
lean_closure_set(v___f_166_, 0, v_val_165_);
lean_closure_set(v___f_166_, 1, v_toPure_158_);
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg(v_inst_159_, v_inst_160_, v_toVar_155_, v_arg_161_, v___x_167_);
v___x_169_ = lean_apply_4(v_toBind_162_, lean_box(0), lean_box(0), v___x_168_, v___f_166_);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__11(lean_object* v_arg_170_, lean_object* v_inst_171_, lean_object* v_toBind_172_, lean_object* v___f_173_, lean_object* v_toPure_174_, lean_object* v_inst_175_, lean_object* v_toVar_176_, lean_object* v_____do__lift_177_){
_start:
{
if (lean_obj_tag(v_____do__lift_177_) == 0)
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec(v_toVar_176_);
lean_dec_ref(v_inst_175_);
lean_dec(v_toPure_174_);
v___x_178_ = lean_alloc_closure((void*)(l_Lean_Meta_getIntValue_x3f___boxed), 6, 1);
lean_closure_set(v___x_178_, 0, v_arg_170_);
v___x_179_ = lean_apply_2(v_inst_171_, lean_box(0), v___x_178_);
v___x_180_ = lean_apply_4(v_toBind_172_, lean_box(0), lean_box(0), v___x_179_, v___f_173_);
return v___x_180_;
}
else
{
lean_object* v_val_181_; lean_object* v___f_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
lean_dec(v___f_173_);
v_val_181_ = lean_ctor_get(v_____do__lift_177_, 0);
lean_inc(v_val_181_);
lean_dec_ref_known(v_____do__lift_177_, 1);
v___f_182_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__10), 3, 2);
lean_closure_set(v___f_182_, 0, v_val_181_);
lean_closure_set(v___f_182_, 1, v_toPure_174_);
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg(v_inst_175_, v_inst_171_, v_toVar_176_, v_arg_170_, v___x_183_);
v___x_185_ = lean_apply_4(v_toBind_172_, lean_box(0), lean_box(0), v___x_184_, v___f_182_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__13(lean_object* v_toVar_186_, lean_object* v_e_187_, lean_object* v_generation_188_, lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_arg_191_, lean_object* v_toBind_192_, lean_object* v___f_193_, uint8_t v_____do__lift_194_){
_start:
{
if (v_____do__lift_194_ == 0)
{
lean_object* v___x_195_; 
lean_dec(v___f_193_);
lean_dec(v_toBind_192_);
lean_dec_ref(v_arg_191_);
lean_dec(v_inst_190_);
lean_dec_ref(v_inst_189_);
v___x_195_ = lean_apply_2(v_toVar_186_, v_e_187_, v_generation_188_);
return v___x_195_;
}
else
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
lean_dec(v_generation_188_);
lean_dec_ref(v_e_187_);
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg(v_inst_189_, v_inst_190_, v_toVar_186_, v_arg_191_, v___x_196_);
v___x_198_ = lean_apply_4(v_toBind_192_, lean_box(0), lean_box(0), v___x_197_, v___f_193_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__13___boxed(lean_object* v_toVar_199_, lean_object* v_e_200_, lean_object* v_generation_201_, lean_object* v_inst_202_, lean_object* v_inst_203_, lean_object* v_arg_204_, lean_object* v_toBind_205_, lean_object* v___f_206_, lean_object* v_____do__lift_207_){
_start:
{
uint8_t v_____do__lift_1189__boxed_208_; lean_object* v_res_209_; 
v_____do__lift_1189__boxed_208_ = lean_unbox(v_____do__lift_207_);
v_res_209_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__13(v_toVar_199_, v_e_200_, v_generation_201_, v_inst_202_, v_inst_203_, v_arg_204_, v_toBind_205_, v___f_206_, v_____do__lift_1189__boxed_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14(lean_object* v_toVar_210_, lean_object* v_e_211_, lean_object* v_generation_212_, lean_object* v_toPure_213_, lean_object* v_inst_214_, lean_object* v_inst_215_, lean_object* v_toBind_216_, lean_object* v___f_217_, lean_object* v___f_218_, lean_object* v_t_219_){
_start:
{
lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_220_ = l_Lean_Expr_cleanupAnnotations(v_t_219_);
v___x_221_ = l_Lean_Expr_isApp(v___x_220_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; 
lean_dec_ref(v___x_220_);
lean_dec(v___f_218_);
lean_dec(v___f_217_);
lean_dec(v_toBind_216_);
lean_dec(v_inst_215_);
lean_dec_ref(v_inst_214_);
lean_dec(v_toPure_213_);
v___x_222_ = lean_apply_2(v_toVar_210_, v_e_211_, v_generation_212_);
return v___x_222_;
}
else
{
lean_object* v___x_223_; uint8_t v___x_224_; 
v___x_223_ = l_Lean_Expr_appFnCleanup___redArg(v___x_220_);
v___x_224_ = l_Lean_Expr_isApp(v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; 
lean_dec_ref(v___x_223_);
lean_dec_ref(v___x_220_);
lean_dec(v___f_218_);
lean_dec(v___f_217_);
lean_dec(v_toBind_216_);
lean_dec(v_inst_215_);
lean_dec_ref(v_inst_214_);
lean_dec(v_toPure_213_);
v___x_225_ = lean_apply_2(v_toVar_210_, v_e_211_, v_generation_212_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_226_ = l_Lean_Expr_appFnCleanup___redArg(v___x_223_);
v___x_227_ = l_Lean_Expr_isApp(v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; 
lean_dec_ref(v___x_226_);
lean_dec_ref(v___x_223_);
lean_dec_ref(v___x_220_);
lean_dec(v___f_218_);
lean_dec(v___f_217_);
lean_dec(v_toBind_216_);
lean_dec(v_inst_215_);
lean_dec_ref(v_inst_214_);
lean_dec(v_toPure_213_);
v___x_228_ = lean_apply_2(v_toVar_210_, v_e_211_, v_generation_212_);
return v___x_228_;
}
else
{
lean_object* v_arg_229_; lean_object* v_arg_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v_arg_229_ = lean_ctor_get(v___x_220_, 1);
lean_inc_ref(v_arg_229_);
lean_dec_ref(v___x_220_);
v_arg_230_ = lean_ctor_get(v___x_223_, 1);
lean_inc_ref(v_arg_230_);
lean_dec_ref(v___x_223_);
v___x_231_ = l_Lean_Expr_appFnCleanup___redArg(v___x_226_);
v___x_232_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__2));
v___x_233_ = l_Lean_Expr_isConstOf(v___x_231_, v___x_232_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; uint8_t v___x_235_; 
lean_dec(v___f_218_);
v___x_234_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__5));
v___x_235_ = l_Lean_Expr_isConstOf(v___x_231_, v___x_234_);
if (v___x_235_ == 0)
{
uint8_t v___x_236_; 
lean_dec(v___f_217_);
v___x_236_ = l_Lean_Expr_isApp(v___x_231_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; 
lean_dec_ref(v___x_231_);
lean_dec_ref(v_arg_230_);
lean_dec_ref(v_arg_229_);
lean_dec_ref(v___x_226_);
lean_dec(v_toBind_216_);
lean_dec(v_inst_215_);
lean_dec_ref(v_inst_214_);
lean_dec(v_toPure_213_);
v___x_237_ = lean_apply_2(v_toVar_210_, v_e_211_, v_generation_212_);
return v___x_237_;
}
else
{
lean_object* v___x_238_; uint8_t v___x_239_; 
v___x_238_ = l_Lean_Expr_appFnCleanup___redArg(v___x_231_);
lean_dec_ref(v___x_231_);
v___x_239_ = l_Lean_Expr_isApp(v___x_238_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; 
lean_dec_ref(v___x_238_);
lean_dec_ref(v_arg_230_);
lean_dec_ref(v_arg_229_);
lean_dec_ref(v___x_226_);
lean_dec(v_toBind_216_);
lean_dec(v_inst_215_);
lean_dec_ref(v_inst_214_);
lean_dec(v_toPure_213_);
v___x_240_ = lean_apply_2(v_toVar_210_, v_e_211_, v_generation_212_);
return v___x_240_;
}
else
{
lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_241_ = l_Lean_Expr_appFnCleanup___redArg(v___x_238_);
lean_dec_ref(v___x_238_);
v___x_242_ = l_Lean_Expr_isApp(v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; 
lean_dec_ref(v___x_241_);
lean_dec_ref(v_arg_230_);
lean_dec_ref(v_arg_229_);
lean_dec_ref(v___x_226_);
lean_dec(v_toBind_216_);
lean_dec(v_inst_215_);
lean_dec_ref(v_inst_214_);
lean_dec(v_toPure_213_);
v___x_243_ = lean_apply_2(v_toVar_210_, v_e_211_, v_generation_212_);
return v___x_243_;
}
else
{
lean_object* v_arg_244_; lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v_arg_244_ = lean_ctor_get(v___x_226_, 1);
lean_inc_ref(v_arg_244_);
lean_dec_ref(v___x_226_);
v___x_245_ = l_Lean_Expr_appFnCleanup___redArg(v___x_241_);
lean_dec_ref(v___x_241_);
v___x_246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__8));
v___x_247_ = l_Lean_Expr_isConstOf(v___x_245_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_248_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__11));
v___x_249_ = l_Lean_Expr_isConstOf(v___x_245_, v___x_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__14));
v___x_251_ = l_Lean_Expr_isConstOf(v___x_245_, v___x_250_);
lean_dec_ref(v___x_245_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
lean_dec_ref(v_arg_244_);
lean_dec_ref(v_arg_230_);
lean_dec_ref(v_arg_229_);
lean_dec(v_toBind_216_);
lean_dec(v_inst_215_);
lean_dec_ref(v_inst_214_);
lean_dec(v_toPure_213_);
v___x_252_ = lean_apply_2(v_toVar_210_, v_e_211_, v_generation_212_);
return v___x_252_;
}
else
{
lean_object* v___f_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
lean_inc(v_toBind_216_);
lean_inc(v_inst_215_);
v___f_253_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_253_, 0, v_toVar_210_);
lean_closure_set(v___f_253_, 1, v_e_211_);
lean_closure_set(v___f_253_, 2, v_generation_212_);
lean_closure_set(v___f_253_, 3, v_toPure_213_);
lean_closure_set(v___f_253_, 4, v_inst_214_);
lean_closure_set(v___f_253_, 5, v_inst_215_);
lean_closure_set(v___f_253_, 6, v_arg_229_);
lean_closure_set(v___f_253_, 7, v_toBind_216_);
lean_closure_set(v___f_253_, 8, v_arg_230_);
v___x_254_ = lean_alloc_closure((void*)(l_Lean_Meta_Structural_isInstHAddInt___boxed), 6, 1);
lean_closure_set(v___x_254_, 0, v_arg_244_);
v___x_255_ = lean_apply_2(v_inst_215_, lean_box(0), v___x_254_);
v___x_256_ = lean_apply_4(v_toBind_216_, lean_box(0), lean_box(0), v___x_255_, v___f_253_);
return v___x_256_;
}
}
else
{
lean_object* v___f_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec_ref(v___x_245_);
lean_inc(v_toBind_216_);
lean_inc(v_inst_215_);
v___f_257_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__7___boxed), 10, 9);
lean_closure_set(v___f_257_, 0, v_toVar_210_);
lean_closure_set(v___f_257_, 1, v_e_211_);
lean_closure_set(v___f_257_, 2, v_generation_212_);
lean_closure_set(v___f_257_, 3, v_toPure_213_);
lean_closure_set(v___f_257_, 4, v_inst_214_);
lean_closure_set(v___f_257_, 5, v_inst_215_);
lean_closure_set(v___f_257_, 6, v_arg_229_);
lean_closure_set(v___f_257_, 7, v_toBind_216_);
lean_closure_set(v___f_257_, 8, v_arg_230_);
v___x_258_ = lean_alloc_closure((void*)(l_Lean_Meta_Structural_isInstHSubInt___boxed), 6, 1);
lean_closure_set(v___x_258_, 0, v_arg_244_);
v___x_259_ = lean_apply_2(v_inst_215_, lean_box(0), v___x_258_);
v___x_260_ = lean_apply_4(v_toBind_216_, lean_box(0), lean_box(0), v___x_259_, v___f_257_);
return v___x_260_;
}
}
else
{
lean_object* v___f_261_; lean_object* v___f_262_; lean_object* v___f_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec_ref(v___x_245_);
lean_inc_n(v_toBind_216_, 3);
lean_inc_ref(v_arg_230_);
lean_inc_n(v_inst_215_, 3);
lean_inc_ref(v_inst_214_);
lean_inc(v_toPure_213_);
lean_inc(v_generation_212_);
lean_inc_ref(v_e_211_);
lean_inc_n(v_toVar_210_, 2);
v___f_261_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__9), 9, 8);
lean_closure_set(v___f_261_, 0, v_toVar_210_);
lean_closure_set(v___f_261_, 1, v_e_211_);
lean_closure_set(v___f_261_, 2, v_generation_212_);
lean_closure_set(v___f_261_, 3, v_toPure_213_);
lean_closure_set(v___f_261_, 4, v_inst_214_);
lean_closure_set(v___f_261_, 5, v_inst_215_);
lean_closure_set(v___f_261_, 6, v_arg_230_);
lean_closure_set(v___f_261_, 7, v_toBind_216_);
v___f_262_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__11), 8, 7);
lean_closure_set(v___f_262_, 0, v_arg_229_);
lean_closure_set(v___f_262_, 1, v_inst_215_);
lean_closure_set(v___f_262_, 2, v_toBind_216_);
lean_closure_set(v___f_262_, 3, v___f_261_);
lean_closure_set(v___f_262_, 4, v_toPure_213_);
lean_closure_set(v___f_262_, 5, v_inst_214_);
lean_closure_set(v___f_262_, 6, v_toVar_210_);
v___f_263_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__12___boxed), 8, 7);
lean_closure_set(v___f_263_, 0, v_toVar_210_);
lean_closure_set(v___f_263_, 1, v_e_211_);
lean_closure_set(v___f_263_, 2, v_generation_212_);
lean_closure_set(v___f_263_, 3, v_arg_230_);
lean_closure_set(v___f_263_, 4, v_inst_215_);
lean_closure_set(v___f_263_, 5, v_toBind_216_);
lean_closure_set(v___f_263_, 6, v___f_262_);
v___x_264_ = lean_alloc_closure((void*)(l_Lean_Meta_Structural_isInstHMulInt___boxed), 6, 1);
lean_closure_set(v___x_264_, 0, v_arg_244_);
v___x_265_ = lean_apply_2(v_inst_215_, lean_box(0), v___x_264_);
v___x_266_ = lean_apply_4(v_toBind_216_, lean_box(0), lean_box(0), v___x_265_, v___f_263_);
return v___x_266_;
}
}
}
}
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
lean_dec_ref(v___x_231_);
lean_dec_ref(v_arg_230_);
lean_dec_ref(v_arg_229_);
lean_dec_ref(v___x_226_);
lean_dec_ref(v_inst_214_);
lean_dec(v_toPure_213_);
lean_dec(v_generation_212_);
lean_dec(v_toVar_210_);
v___x_267_ = lean_alloc_closure((void*)(l_Lean_Meta_getIntValue_x3f___boxed), 6, 1);
lean_closure_set(v___x_267_, 0, v_e_211_);
v___x_268_ = lean_apply_2(v_inst_215_, lean_box(0), v___x_267_);
v___x_269_ = lean_apply_4(v_toBind_216_, lean_box(0), lean_box(0), v___x_268_, v___f_217_);
return v___x_269_;
}
}
else
{
lean_object* v___f_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec_ref(v___x_231_);
lean_dec_ref(v___x_226_);
lean_dec(v___f_217_);
lean_dec(v_toPure_213_);
lean_inc(v_toBind_216_);
lean_inc(v_inst_215_);
v___f_270_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__13___boxed), 9, 8);
lean_closure_set(v___f_270_, 0, v_toVar_210_);
lean_closure_set(v___f_270_, 1, v_e_211_);
lean_closure_set(v___f_270_, 2, v_generation_212_);
lean_closure_set(v___f_270_, 3, v_inst_214_);
lean_closure_set(v___f_270_, 4, v_inst_215_);
lean_closure_set(v___f_270_, 5, v_arg_229_);
lean_closure_set(v___f_270_, 6, v_toBind_216_);
lean_closure_set(v___f_270_, 7, v___f_218_);
v___x_271_ = lean_alloc_closure((void*)(l_Lean_Meta_Structural_isInstNegInt___boxed), 6, 1);
lean_closure_set(v___x_271_, 0, v_arg_230_);
v___x_272_ = lean_apply_2(v_inst_215_, lean_box(0), v___x_271_);
v___x_273_ = lean_apply_4(v_toBind_216_, lean_box(0), lean_box(0), v___x_272_, v___f_270_);
return v___x_273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___boxed(lean_object* v_toVar_274_, lean_object* v_e_275_, lean_object* v_generation_276_, lean_object* v_toPure_277_, lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_toBind_280_, lean_object* v___f_281_, lean_object* v___f_282_, lean_object* v_t_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14(v_toVar_274_, v_e_275_, v_generation_276_, v_toPure_277_, v_inst_278_, v_inst_279_, v_toBind_280_, v___f_281_, v___f_282_, v_t_283_);
lean_dec_ref(v_t_283_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg(lean_object* v_inst_285_, lean_object* v_inst_286_, lean_object* v_toVar_287_, lean_object* v_e_288_, lean_object* v_generation_289_){
_start:
{
lean_object* v_toApplicative_290_; lean_object* v_toBind_291_; lean_object* v_toPure_292_; lean_object* v___f_293_; lean_object* v___f_294_; lean_object* v___f_295_; uint8_t v___x_296_; 
v_toApplicative_290_ = lean_ctor_get(v_inst_285_, 0);
v_toBind_291_ = lean_ctor_get(v_inst_285_, 1);
lean_inc_n(v_toBind_291_, 2);
v_toPure_292_ = lean_ctor_get(v_toApplicative_290_, 1);
lean_inc_n(v_toPure_292_, 4);
lean_inc(v_generation_289_);
lean_inc_ref_n(v_e_288_, 2);
lean_inc(v_toVar_287_);
v___f_293_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__0), 5, 4);
lean_closure_set(v___f_293_, 0, v_toPure_292_);
lean_closure_set(v___f_293_, 1, v_toVar_287_);
lean_closure_set(v___f_293_, 2, v_e_288_);
lean_closure_set(v___f_293_, 3, v_generation_289_);
v___f_294_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__1), 2, 1);
lean_closure_set(v___f_294_, 0, v_toPure_292_);
lean_inc(v_inst_286_);
v___f_295_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___boxed), 10, 9);
lean_closure_set(v___f_295_, 0, v_toVar_287_);
lean_closure_set(v___f_295_, 1, v_e_288_);
lean_closure_set(v___f_295_, 2, v_generation_289_);
lean_closure_set(v___f_295_, 3, v_toPure_292_);
lean_closure_set(v___f_295_, 4, v_inst_285_);
lean_closure_set(v___f_295_, 5, v_inst_286_);
lean_closure_set(v___f_295_, 6, v_toBind_291_);
lean_closure_set(v___f_295_, 7, v___f_293_);
lean_closure_set(v___f_295_, 8, v___f_294_);
v___x_296_ = l_Lean_Expr_hasExprMVar(v_e_288_);
if (v___x_296_ == 0)
{
lean_object* v___f_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec(v_inst_286_);
v___f_297_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__15), 2, 1);
lean_closure_set(v___f_297_, 0, v___f_295_);
v___x_298_ = lean_apply_2(v_toPure_292_, lean_box(0), v_e_288_);
v___x_299_ = lean_apply_4(v_toBind_291_, lean_box(0), lean_box(0), v___x_298_, v___f_297_);
return v___x_299_;
}
else
{
lean_object* v___f_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec(v_toPure_292_);
v___f_300_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__15), 2, 1);
lean_closure_set(v___f_300_, 0, v___f_295_);
v___x_301_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateMVarsIfMVarApp___boxed), 6, 1);
lean_closure_set(v___x_301_, 0, v_e_288_);
v___x_302_ = lean_apply_2(v_inst_286_, lean_box(0), v___x_301_);
v___x_303_ = lean_apply_4(v_toBind_291_, lean_box(0), lean_box(0), v___x_302_, v___f_300_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__3(lean_object* v_toPure_304_, lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_toVar_307_, lean_object* v_arg_308_, lean_object* v___x_309_, lean_object* v_toBind_310_, lean_object* v_____do__lift_311_){
_start:
{
lean_object* v___f_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___f_312_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__2), 3, 2);
lean_closure_set(v___f_312_, 0, v_____do__lift_311_);
lean_closure_set(v___f_312_, 1, v_toPure_304_);
v___x_313_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg(v_inst_305_, v_inst_306_, v_toVar_307_, v_arg_308_, v___x_309_);
v___x_314_ = lean_apply_4(v_toBind_310_, lean_box(0), lean_box(0), v___x_313_, v___f_312_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux(lean_object* v_m_315_, lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_toVar_318_, lean_object* v_e_319_, lean_object* v_generation_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg(v_inst_316_, v_inst_317_, v_toVar_318_, v_e_319_, v_generation_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExprWith___redArg___lam__0(lean_object* v_toPure_322_, lean_object* v_____do__lift_323_){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v_____do__lift_323_);
v___x_325_ = lean_apply_2(v_toPure_322_, lean_box(0), v___x_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExprWith___redArg___lam__1(lean_object* v_toVar_326_, lean_object* v_toBind_327_, lean_object* v___f_328_, lean_object* v_e_329_, lean_object* v_x_330_){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_apply_1(v_toVar_326_, v_e_329_);
v___x_332_ = lean_apply_4(v_toBind_327_, lean_box(0), lean_box(0), v___x_331_, v___f_328_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExprWith___redArg___lam__1___boxed(lean_object* v_toVar_333_, lean_object* v_toBind_334_, lean_object* v___f_335_, lean_object* v_e_336_, lean_object* v_x_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExprWith___redArg___lam__1(v_toVar_333_, v_toBind_334_, v___f_335_, v_e_336_, v_x_337_);
lean_dec(v_x_337_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExprWith___redArg(lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_toVar_341_, lean_object* v_e_342_){
_start:
{
lean_object* v_toApplicative_343_; lean_object* v_toBind_344_; lean_object* v_toPure_345_; lean_object* v___f_346_; lean_object* v___f_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_toApplicative_343_ = lean_ctor_get(v_inst_339_, 0);
v_toBind_344_ = lean_ctor_get(v_inst_339_, 1);
v_toPure_345_ = lean_ctor_get(v_toApplicative_343_, 1);
lean_inc(v_toPure_345_);
v___f_346_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExprWith___redArg___lam__0), 2, 1);
lean_closure_set(v___f_346_, 0, v_toPure_345_);
lean_inc(v_toBind_344_);
v___f_347_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExprWith___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_347_, 0, v_toVar_341_);
lean_closure_set(v___f_347_, 1, v_toBind_344_);
lean_closure_set(v___f_347_, 2, v___f_346_);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg(v_inst_339_, v_inst_340_, v___f_347_, v_e_342_, v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExprWith(lean_object* v_m_350_, lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_toVar_353_, lean_object* v_e_354_){
_start:
{
lean_object* v_toApplicative_355_; lean_object* v_toBind_356_; lean_object* v_toPure_357_; lean_object* v___f_358_; lean_object* v___f_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_toApplicative_355_ = lean_ctor_get(v_inst_351_, 0);
v_toBind_356_ = lean_ctor_get(v_inst_351_, 1);
v_toPure_357_ = lean_ctor_get(v_toApplicative_355_, 1);
lean_inc(v_toPure_357_);
v___f_358_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExprWith___redArg___lam__0), 2, 1);
lean_closure_set(v___f_358_, 0, v_toPure_357_);
lean_inc(v_toBind_356_);
v___f_359_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExprWith___redArg___lam__1___boxed), 5, 3);
lean_closure_set(v___f_359_, 0, v_toVar_353_);
lean_closure_set(v___f_359_, 1, v_toBind_356_);
lean_closure_set(v___f_359_, 2, v___f_358_);
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg(v_inst_351_, v_inst_352_, v___f_359_, v_e_354_, v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00Lean_Meta_Grind_Arith_Cutsat_toLinearExpr_spec__0(lean_object* v_e_362_, lean_object* v_generation_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_atom_376_; lean_object* v_gen_377_; lean_object* v___y_378_; lean_object* v___y_379_; lean_object* v___y_380_; lean_object* v___y_381_; lean_object* v___y_382_; lean_object* v___y_383_; lean_object* v___y_384_; lean_object* v___y_385_; lean_object* v___y_386_; lean_object* v___y_387_; lean_object* v_t_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_460_; lean_object* v___y_461_; lean_object* v___y_462_; lean_object* v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; lean_object* v___y_466_; uint8_t v___x_643_; 
v___x_643_ = l_Lean_Expr_hasExprMVar(v_e_362_);
if (v___x_643_ == 0)
{
lean_inc_ref(v_e_362_);
v_t_456_ = v_e_362_;
v___y_457_ = v___y_364_;
v___y_458_ = v___y_365_;
v___y_459_ = v___y_366_;
v___y_460_ = v___y_367_;
v___y_461_ = v___y_368_;
v___y_462_ = v___y_369_;
v___y_463_ = v___y_370_;
v___y_464_ = v___y_371_;
v___y_465_ = v___y_372_;
v___y_466_ = v___y_373_;
goto v___jp_455_;
}
else
{
lean_object* v___x_644_; 
lean_inc_ref(v_e_362_);
v___x_644_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_362_, v___y_371_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_644_, 1);
v_t_456_ = v_a_645_;
v___y_457_ = v___y_364_;
v___y_458_ = v___y_365_;
v___y_459_ = v___y_366_;
v___y_460_ = v___y_367_;
v___y_461_ = v___y_368_;
v___y_462_ = v___y_369_;
v___y_463_ = v___y_370_;
v___y_464_ = v___y_371_;
v___y_465_ = v___y_372_;
v___y_466_ = v___y_373_;
goto v___jp_455_;
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec(v_generation_363_);
lean_dec_ref(v_e_362_);
v_a_646_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_644_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_644_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
v___jp_375_:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_Meta_Sym_shareCommon(v_atom_376_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_390_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
lean_dec_ref_known(v___x_388_, 1);
v___x_390_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_389_, v___y_378_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; uint8_t v___x_392_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
lean_dec_ref_known(v___x_390_, 1);
v___x_392_ = lean_unbox(v_a_391_);
lean_dec(v_a_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_box(0);
lean_inc(v___y_387_);
lean_inc_ref(v___y_386_);
lean_inc(v___y_385_);
lean_inc_ref(v___y_384_);
lean_inc(v___y_383_);
lean_inc_ref(v___y_382_);
lean_inc(v___y_381_);
lean_inc_ref(v___y_380_);
lean_inc(v___y_379_);
lean_inc(v___y_378_);
lean_inc(v_a_389_);
v___x_394_ = lean_grind_internalize(v_a_389_, v_gen_377_, v___x_393_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v___x_395_; 
lean_dec_ref_known(v___x_394_, 1);
lean_inc(v___y_387_);
lean_inc_ref(v___y_386_);
lean_inc(v___y_385_);
lean_inc_ref(v___y_384_);
lean_inc(v___y_383_);
lean_inc_ref(v___y_382_);
lean_inc(v___y_381_);
lean_inc_ref(v___y_380_);
lean_inc(v___y_379_);
lean_inc(v___y_378_);
v___x_395_ = lean_grind_cutsat_mk_var(v_a_389_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
if (lean_obj_tag(v___x_395_) == 0)
{
lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_404_; 
v_a_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_404_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_400_, 0, v_a_396_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_400_);
v___x_402_ = v___x_398_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
v_a_405_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_395_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_395_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec(v_a_389_);
v_a_413_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_394_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_394_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
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
else
{
lean_object* v___x_421_; 
lean_dec(v_gen_377_);
lean_inc(v___y_387_);
lean_inc_ref(v___y_386_);
lean_inc(v___y_385_);
lean_inc_ref(v___y_384_);
lean_inc(v___y_383_);
lean_inc_ref(v___y_382_);
lean_inc(v___y_381_);
lean_inc_ref(v___y_380_);
lean_inc(v___y_379_);
lean_inc(v___y_378_);
v___x_421_ = lean_grind_cutsat_mk_var(v_a_389_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_430_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_430_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_430_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_430_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_426_, 0, v_a_422_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 0, v___x_426_);
v___x_428_ = v___x_424_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
v_a_431_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_421_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_421_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
}
else
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec(v_a_389_);
lean_dec(v_gen_377_);
v_a_439_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_390_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_390_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec(v_gen_377_);
v_a_447_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_388_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_388_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
v___jp_455_:
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = l_Lean_Expr_cleanupAnnotations(v_t_456_);
lean_dec_ref(v_t_456_);
v___x_468_ = l_Lean_Expr_isApp(v___x_467_);
if (v___x_468_ == 0)
{
lean_dec_ref(v___x_467_);
v_atom_376_ = v_e_362_;
v_gen_377_ = v_generation_363_;
v___y_378_ = v___y_457_;
v___y_379_ = v___y_458_;
v___y_380_ = v___y_459_;
v___y_381_ = v___y_460_;
v___y_382_ = v___y_461_;
v___y_383_ = v___y_462_;
v___y_384_ = v___y_463_;
v___y_385_ = v___y_464_;
v___y_386_ = v___y_465_;
v___y_387_ = v___y_466_;
goto v___jp_375_;
}
else
{
lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_469_ = l_Lean_Expr_appFnCleanup___redArg(v___x_467_);
v___x_470_ = l_Lean_Expr_isApp(v___x_469_);
if (v___x_470_ == 0)
{
lean_dec_ref(v___x_469_);
lean_dec_ref(v___x_467_);
v_atom_376_ = v_e_362_;
v_gen_377_ = v_generation_363_;
v___y_378_ = v___y_457_;
v___y_379_ = v___y_458_;
v___y_380_ = v___y_459_;
v___y_381_ = v___y_460_;
v___y_382_ = v___y_461_;
v___y_383_ = v___y_462_;
v___y_384_ = v___y_463_;
v___y_385_ = v___y_464_;
v___y_386_ = v___y_465_;
v___y_387_ = v___y_466_;
goto v___jp_375_;
}
else
{
lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_471_ = l_Lean_Expr_appFnCleanup___redArg(v___x_469_);
v___x_472_ = l_Lean_Expr_isApp(v___x_471_);
if (v___x_472_ == 0)
{
lean_dec_ref(v___x_471_);
lean_dec_ref(v___x_469_);
lean_dec_ref(v___x_467_);
v_atom_376_ = v_e_362_;
v_gen_377_ = v_generation_363_;
v___y_378_ = v___y_457_;
v___y_379_ = v___y_458_;
v___y_380_ = v___y_459_;
v___y_381_ = v___y_460_;
v___y_382_ = v___y_461_;
v___y_383_ = v___y_462_;
v___y_384_ = v___y_463_;
v___y_385_ = v___y_464_;
v___y_386_ = v___y_465_;
v___y_387_ = v___y_466_;
goto v___jp_375_;
}
else
{
lean_object* v_arg_473_; lean_object* v_arg_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v_arg_473_ = lean_ctor_get(v___x_467_, 1);
lean_inc_ref(v_arg_473_);
lean_dec_ref(v___x_467_);
v_arg_474_ = lean_ctor_get(v___x_469_, 1);
lean_inc_ref(v_arg_474_);
lean_dec_ref(v___x_469_);
v___x_475_ = l_Lean_Expr_appFnCleanup___redArg(v___x_471_);
v___x_476_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__2));
v___x_477_ = l_Lean_Expr_isConstOf(v___x_475_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__5));
v___x_479_ = l_Lean_Expr_isConstOf(v___x_475_, v___x_478_);
if (v___x_479_ == 0)
{
uint8_t v___x_480_; 
v___x_480_ = l_Lean_Expr_isApp(v___x_475_);
if (v___x_480_ == 0)
{
lean_dec_ref(v___x_475_);
lean_dec_ref(v_arg_474_);
lean_dec_ref(v_arg_473_);
lean_dec_ref(v___x_471_);
v_atom_376_ = v_e_362_;
v_gen_377_ = v_generation_363_;
v___y_378_ = v___y_457_;
v___y_379_ = v___y_458_;
v___y_380_ = v___y_459_;
v___y_381_ = v___y_460_;
v___y_382_ = v___y_461_;
v___y_383_ = v___y_462_;
v___y_384_ = v___y_463_;
v___y_385_ = v___y_464_;
v___y_386_ = v___y_465_;
v___y_387_ = v___y_466_;
goto v___jp_375_;
}
else
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = l_Lean_Expr_appFnCleanup___redArg(v___x_475_);
lean_dec_ref(v___x_475_);
v___x_482_ = l_Lean_Expr_isApp(v___x_481_);
if (v___x_482_ == 0)
{
lean_dec_ref(v___x_481_);
lean_dec_ref(v_arg_474_);
lean_dec_ref(v_arg_473_);
lean_dec_ref(v___x_471_);
v_atom_376_ = v_e_362_;
v_gen_377_ = v_generation_363_;
v___y_378_ = v___y_457_;
v___y_379_ = v___y_458_;
v___y_380_ = v___y_459_;
v___y_381_ = v___y_460_;
v___y_382_ = v___y_461_;
v___y_383_ = v___y_462_;
v___y_384_ = v___y_463_;
v___y_385_ = v___y_464_;
v___y_386_ = v___y_465_;
v___y_387_ = v___y_466_;
goto v___jp_375_;
}
else
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = l_Lean_Expr_appFnCleanup___redArg(v___x_481_);
lean_dec_ref(v___x_481_);
v___x_484_ = l_Lean_Expr_isApp(v___x_483_);
if (v___x_484_ == 0)
{
lean_dec_ref(v___x_483_);
lean_dec_ref(v_arg_474_);
lean_dec_ref(v_arg_473_);
lean_dec_ref(v___x_471_);
v_atom_376_ = v_e_362_;
v_gen_377_ = v_generation_363_;
v___y_378_ = v___y_457_;
v___y_379_ = v___y_458_;
v___y_380_ = v___y_459_;
v___y_381_ = v___y_460_;
v___y_382_ = v___y_461_;
v___y_383_ = v___y_462_;
v___y_384_ = v___y_463_;
v___y_385_ = v___y_464_;
v___y_386_ = v___y_465_;
v___y_387_ = v___y_466_;
goto v___jp_375_;
}
else
{
lean_object* v_arg_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_arg_485_ = lean_ctor_get(v___x_471_, 1);
lean_inc_ref(v_arg_485_);
lean_dec_ref(v___x_471_);
v___x_486_ = l_Lean_Expr_appFnCleanup___redArg(v___x_483_);
lean_dec_ref(v___x_483_);
v___x_487_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__8));
v___x_488_ = l_Lean_Expr_isConstOf(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__11));
v___x_490_ = l_Lean_Expr_isConstOf(v___x_486_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_491_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___redArg___lam__14___closed__14));
v___x_492_ = l_Lean_Expr_isConstOf(v___x_486_, v___x_491_);
lean_dec_ref(v___x_486_);
if (v___x_492_ == 0)
{
lean_dec_ref(v_arg_485_);
lean_dec_ref(v_arg_474_);
lean_dec_ref(v_arg_473_);
v_atom_376_ = v_e_362_;
v_gen_377_ = v_generation_363_;
v___y_378_ = v___y_457_;
v___y_379_ = v___y_458_;
v___y_380_ = v___y_459_;
v___y_381_ = v___y_460_;
v___y_382_ = v___y_461_;
v___y_383_ = v___y_462_;
v___y_384_ = v___y_463_;
v___y_385_ = v___y_464_;
v___y_386_ = v___y_465_;
v___y_387_ = v___y_466_;
goto v___jp_375_;
}
else
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_485_, v___y_464_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; uint8_t v___x_495_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v___x_493_, 1);
v___x_495_ = lean_unbox(v_a_494_);
lean_dec(v_a_494_);
if (v___x_495_ == 0)
{
lean_dec_ref(v_arg_474_);
lean_dec_ref(v_arg_473_);
v_atom_376_ = v_e_362_;
v_gen_377_ = v_generation_363_;
v___y_378_ = v___y_457_;
v___y_379_ = v___y_458_;
v___y_380_ = v___y_459_;
v___y_381_ = v___y_460_;
v___y_382_ = v___y_461_;
v___y_383_ = v___y_462_;
v___y_384_ = v___y_463_;
v___y_385_ = v___y_464_;
v___y_386_ = v___y_465_;
v___y_387_ = v___y_466_;
goto v___jp_375_;
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec(v_generation_363_);
lean_dec_ref(v_e_362_);
v___x_496_ = lean_unsigned_to_nat(0u);
v___x_497_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00Lean_Meta_Grind_Arith_Cutsat_toLinearExpr_spec__0(v_arg_474_, v___x_496_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_499_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref_known(v___x_497_, 1);
v___x_499_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00Lean_Meta_Grind_Arith_Cutsat_toLinearExpr_spec__0(v_arg_473_, v___x_496_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_508_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_508_ == 0)
{
v___x_502_ = v___x_499_;
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_499_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_508_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_504_, 0, v_a_498_);
lean_ctor_set(v___x_504_, 1, v_a_500_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_504_);
v___x_506_ = v___x_502_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
else
{
lean_dec(v_a_498_);
return v___x_499_;
}
}
else
{
lean_dec_ref(v_arg_473_);
return v___x_497_;
}
}
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec_ref(v_arg_474_);
lean_dec_ref(v_arg_473_);
lean_dec(v_generation_363_);
lean_dec_ref(v_e_362_);
v_a_509_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_493_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_493_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
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
else
{
lean_object* v___x_517_; 
lean_dec_ref(v___x_486_);
v___x_517_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_arg_485_, v___y_464_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; uint8_t v___x_519_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref_known(v___x_517_, 1);
v___x_519_ = lean_unbox(v_a_518_);
lean_dec(v_a_518_);
if (v___x_519_ == 0)
{
lean_dec_ref(v_arg_474_);
lean_dec_ref(v_arg_473_);
v_atom_376_ = v_e_362_;
v_gen_377_ = v_generation_363_;
v___y_378_ = v___y_457_;
v___y_379_ = v___y_458_;
v___y_380_ = v___y_459_;
v___y_381_ = v___y_460_;
v___y_382_ = v___y_461_;
v___y_383_ = v___y_462_;
v___y_384_ = v___y_463_;
v___y_385_ = v___y_464_;
v___y_386_ = v___y_465_;
v___y_387_ = v___y_466_;
goto v___jp_375_;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec(v_generation_363_);
lean_dec_ref(v_e_362_);
v___x_520_ = lean_unsigned_to_nat(0u);
v___x_521_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00Lean_Meta_Grind_Arith_Cutsat_toLinearExpr_spec__0(v_arg_474_, v___x_520_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref_known(v___x_521_, 1);
v___x_523_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00Lean_Meta_Grind_Arith_Cutsat_toLinearExpr_spec__0(v_arg_473_, v___x_520_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_532_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_532_ == 0)
{
v___x_526_ = v___x_523_;
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___x_523_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_532_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_528_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_528_, 0, v_a_522_);
lean_ctor_set(v___x_528_, 1, v_a_524_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_528_);
v___x_530_ = v___x_526_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
else
{
lean_dec(v_a_522_);
return v___x_523_;
}
}
else
{
lean_dec_ref(v_arg_473_);
return v___x_521_;
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec_ref(v_arg_474_);
lean_dec_ref(v_arg_473_);
lean_dec(v_generation_363_);
lean_dec_ref(v_e_362_);
v_a_533_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_517_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_517_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
else
{
lean_object* v___x_541_; 
lean_dec_ref(v___x_486_);
v___x_541_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_485_, v___y_464_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; uint8_t v___x_543_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref_known(v___x_541_, 1);
v___x_543_ = lean_unbox(v_a_542_);
lean_dec(v_a_542_);
if (v___x_543_ == 0)
{
lean_dec_ref(v_arg_474_);
lean_dec_ref(v_arg_473_);
v_atom_376_ = v_e_362_;
v_gen_377_ = v_generation_363_;
v___y_378_ = v___y_457_;
v___y_379_ = v___y_458_;
v___y_380_ = v___y_459_;
v___y_381_ = v___y_460_;
v___y_382_ = v___y_461_;
v___y_383_ = v___y_462_;
v___y_384_ = v___y_463_;
v___y_385_ = v___y_464_;
v___y_386_ = v___y_465_;
v___y_387_ = v___y_466_;
goto v___jp_375_;
}
else
{
lean_object* v___x_544_; 
lean_inc_ref(v_arg_474_);
v___x_544_ = l_Lean_Meta_getIntValue_x3f(v_arg_474_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v_a_545_; 
v_a_545_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v___x_544_, 1);
if (lean_obj_tag(v_a_545_) == 0)
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Meta_getIntValue_x3f(v_arg_473_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_a_547_);
lean_dec_ref_known(v___x_546_, 1);
if (lean_obj_tag(v_a_547_) == 0)
{
lean_dec_ref(v_arg_474_);
v_atom_376_ = v_e_362_;
v_gen_377_ = v_generation_363_;
v___y_378_ = v___y_457_;
v___y_379_ = v___y_458_;
v___y_380_ = v___y_459_;
v___y_381_ = v___y_460_;
v___y_382_ = v___y_461_;
v___y_383_ = v___y_462_;
v___y_384_ = v___y_463_;
v___y_385_ = v___y_464_;
v___y_386_ = v___y_465_;
v___y_387_ = v___y_466_;
goto v___jp_375_;
}
else
{
lean_object* v_val_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
lean_dec(v_generation_363_);
lean_dec_ref(v_e_362_);
v_val_548_ = lean_ctor_get(v_a_547_, 0);
lean_inc(v_val_548_);
lean_dec_ref_known(v_a_547_, 1);
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00Lean_Meta_Grind_Arith_Cutsat_toLinearExpr_spec__0(v_arg_474_, v___x_549_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_559_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_559_ == 0)
{
v___x_553_ = v___x_550_;
v_isShared_554_ = v_isSharedCheck_559_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_550_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_559_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v___x_557_; 
v___x_555_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_555_, 0, v_a_551_);
lean_ctor_set(v___x_555_, 1, v_val_548_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_555_);
v___x_557_ = v___x_553_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_555_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
else
{
lean_dec(v_val_548_);
return v___x_550_;
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec_ref(v_arg_474_);
lean_dec(v_generation_363_);
lean_dec_ref(v_e_362_);
v_a_560_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_546_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_546_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
else
{
lean_object* v_val_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec_ref(v_arg_474_);
lean_dec(v_generation_363_);
lean_dec_ref(v_e_362_);
v_val_568_ = lean_ctor_get(v_a_545_, 0);
lean_inc(v_val_568_);
lean_dec_ref_known(v_a_545_, 1);
v___x_569_ = lean_unsigned_to_nat(0u);
v___x_570_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00Lean_Meta_Grind_Arith_Cutsat_toLinearExpr_spec__0(v_arg_473_, v___x_569_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_579_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_579_ == 0)
{
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_579_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_575_, 0, v_val_568_);
lean_ctor_set(v___x_575_, 1, v_a_571_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_575_);
v___x_577_ = v___x_573_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
else
{
lean_dec(v_val_568_);
return v___x_570_;
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref(v_arg_474_);
lean_dec_ref(v_arg_473_);
lean_dec(v_generation_363_);
lean_dec_ref(v_e_362_);
v_a_580_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_544_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_544_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec_ref(v_arg_474_);
lean_dec_ref(v_arg_473_);
lean_dec(v_generation_363_);
lean_dec_ref(v_e_362_);
v_a_588_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_541_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_541_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
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
lean_object* v___x_596_; 
lean_dec_ref(v___x_475_);
lean_dec_ref(v_arg_474_);
lean_dec_ref(v_arg_473_);
lean_dec_ref(v___x_471_);
lean_inc_ref(v_e_362_);
v___x_596_ = l_Lean_Meta_getIntValue_x3f(v_e_362_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_612_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_612_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_612_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_612_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
if (lean_obj_tag(v_a_597_) == 1)
{
lean_object* v_val_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_611_; 
lean_dec(v_generation_363_);
lean_dec_ref(v_e_362_);
v_val_601_ = lean_ctor_get(v_a_597_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v_a_597_);
if (v_isSharedCheck_611_ == 0)
{
v___x_603_ = v_a_597_;
v_isShared_604_ = v_isSharedCheck_611_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_val_601_);
lean_dec(v_a_597_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_611_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set_tag(v___x_603_, 0);
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_val_601_);
v___x_606_ = v_reuseFailAlloc_610_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_608_; 
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_606_);
v___x_608_ = v___x_599_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
else
{
lean_del_object(v___x_599_);
lean_dec(v_a_597_);
v_atom_376_ = v_e_362_;
v_gen_377_ = v_generation_363_;
v___y_378_ = v___y_457_;
v___y_379_ = v___y_458_;
v___y_380_ = v___y_459_;
v___y_381_ = v___y_460_;
v___y_382_ = v___y_461_;
v___y_383_ = v___y_462_;
v___y_384_ = v___y_463_;
v___y_385_ = v___y_464_;
v___y_386_ = v___y_465_;
v___y_387_ = v___y_466_;
goto v___jp_375_;
}
}
}
else
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_dec(v_generation_363_);
lean_dec_ref(v_e_362_);
v_a_613_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_596_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_596_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
else
{
lean_object* v___x_621_; 
lean_dec_ref(v___x_475_);
lean_dec_ref(v___x_471_);
v___x_621_ = l_Lean_Meta_Structural_isInstNegInt___redArg(v_arg_474_, v___y_464_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; uint8_t v___x_623_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_622_);
lean_dec_ref_known(v___x_621_, 1);
v___x_623_ = lean_unbox(v_a_622_);
lean_dec(v_a_622_);
if (v___x_623_ == 0)
{
lean_dec_ref(v_arg_473_);
v_atom_376_ = v_e_362_;
v_gen_377_ = v_generation_363_;
v___y_378_ = v___y_457_;
v___y_379_ = v___y_458_;
v___y_380_ = v___y_459_;
v___y_381_ = v___y_460_;
v___y_382_ = v___y_461_;
v___y_383_ = v___y_462_;
v___y_384_ = v___y_463_;
v___y_385_ = v___y_464_;
v___y_386_ = v___y_465_;
v___y_387_ = v___y_466_;
goto v___jp_375_;
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec(v_generation_363_);
lean_dec_ref(v_e_362_);
v___x_624_ = lean_unsigned_to_nat(0u);
v___x_625_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00Lean_Meta_Grind_Arith_Cutsat_toLinearExpr_spec__0(v_arg_473_, v___x_624_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_634_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_634_ == 0)
{
v___x_628_ = v___x_625_;
v_isShared_629_ = v_isSharedCheck_634_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_625_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_634_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_630_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_630_, 0, v_a_626_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_630_);
v___x_632_ = v___x_628_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_630_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
else
{
return v___x_625_;
}
}
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_dec_ref(v_arg_473_);
lean_dec(v_generation_363_);
lean_dec_ref(v_e_362_);
v_a_635_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_621_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_621_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00Lean_Meta_Grind_Arith_Cutsat_toLinearExpr_spec__0___boxed(lean_object* v_e_654_, lean_object* v_generation_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00Lean_Meta_Grind_Arith_Cutsat_toLinearExpr_spec__0(v_e_654_, v_generation_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec(v___y_656_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object* v_e_668_, lean_object* v_generation_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm_0__Lean_Meta_Grind_Arith_Cutsat_toLinearExprAux___at___00Lean_Meta_Grind_Arith_Cutsat_toLinearExpr_spec__0(v_e_668_, v_generation_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___boxed(lean_object* v_e_682_, lean_object* v_generation_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_e_682_, v_generation_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
lean_dec(v_a_691_);
lean_dec_ref(v_a_690_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec(v_a_684_);
return v_res_695_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: Lean.Meta.Sym.Simp.ControlFlow
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InferType import Lean.Meta.Sym.Simp.App import Lean.Meta.WHNF import Lean.Meta.AppBuilder import Init.Sym.Lemmas
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getBoundedAppFn(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFn(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkEqRefl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ite_false"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(217, 231, 214, 152, 207, 100, 121, 38)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ite_true"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(28, 219, 17, 217, 43, 100, 109, 98)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ite_cond_congr"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(149, 115, 5, 135, 85, 70, 205, 95)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ite_cond_eq_false"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__13 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(4, 35, 104, 204, 105, 138, 171, 217)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ite_cond_eq_true"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__15 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(217, 214, 153, 207, 191, 74, 245, 103)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__16 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_false"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 21, 178, 198, 97, 164, 246, 137)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "dite_false"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(78, 119, 178, 178, 249, 126, 188, 7)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "dite_true"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__13 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(65, 218, 189, 96, 14, 237, 238, 210)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__15 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__16 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__17 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mpr_prop"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__18 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__17_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(169, 177, 76, 157, 211, 15, 217, 219)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__19 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__19_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mpr_not"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__22 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__17_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__22_value),LEAN_SCALAR_PTR_LITERAL(121, 56, 250, 51, 9, 123, 141, 181)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__23 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__23_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "dite_cond_congr"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__25 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26_value_aux_1),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__25_value),LEAN_SCALAR_PTR_LITERAL(72, 238, 116, 219, 106, 19, 52, 46)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "dite_cond_eq_false"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27_value),LEAN_SCALAR_PTR_LITERAL(153, 159, 146, 90, 178, 85, 98, 212)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__28 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__28_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "dite_cond_eq_true"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29_value),LEAN_SCALAR_PTR_LITERAL(13, 104, 142, 126, 111, 138, 152, 2)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__30 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__30_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "cond_false"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(98, 92, 93, 112, 12, 94, 108, 230)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "cond_true"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(159, 102, 104, 109, 28, 196, 37, 90)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__5_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "cond_cond_congr"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(41, 228, 101, 80, 96, 119, 204, 25)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "cond_cond_eq_false"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 151, 22, 186, 118, 232, 224)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "cond_cond_eq_true"};
static const lean_object* l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(52, 237, 153, 45, 203, 196, 217, 147)}};
static const lean_object* l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpCond___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpCond___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpCond___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpControl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpControl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(lean_object* v_f_1_, lean_object* v_a_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___y_11_; lean_object* v___x_14_; uint8_t v_debug_15_; 
v___x_14_ = lean_st_ref_get(v___y_4_);
v_debug_15_ = lean_ctor_get_uint8(v___x_14_, sizeof(void*)*7);
lean_dec(v___x_14_);
if (v_debug_15_ == 0)
{
lean_dec(v___y_8_);
lean_dec_ref(v___y_7_);
lean_dec(v___y_6_);
lean_dec_ref(v___y_5_);
lean_dec_ref(v___y_3_);
v___y_11_ = v___y_4_;
goto v___jp_10_;
}
else
{
lean_object* v___x_16_; 
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc_ref(v___y_3_);
lean_inc_ref(v_f_1_);
v___x_16_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_1_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_16_) == 0)
{
lean_object* v___x_17_; 
lean_dec_ref(v___x_16_);
lean_inc(v___y_4_);
lean_inc_ref(v_a_2_);
v___x_17_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_dec_ref(v___x_17_);
v___y_11_ = v___y_4_;
goto v___jp_10_;
}
else
{
lean_object* v_a_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_25_; 
lean_dec(v___y_4_);
lean_dec_ref(v_a_2_);
lean_dec_ref(v_f_1_);
v_a_18_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_25_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_25_ == 0)
{
v___x_20_ = v___x_17_;
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_a_18_);
lean_dec(v___x_17_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_25_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_23_; 
if (v_isShared_21_ == 0)
{
v___x_23_ = v___x_20_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v_a_18_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
else
{
lean_object* v_a_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_33_; 
lean_dec(v___y_8_);
lean_dec_ref(v___y_7_);
lean_dec(v___y_6_);
lean_dec_ref(v___y_5_);
lean_dec(v___y_4_);
lean_dec_ref(v___y_3_);
lean_dec_ref(v_a_2_);
lean_dec_ref(v_f_1_);
v_a_26_ = lean_ctor_get(v___x_16_, 0);
v_isSharedCheck_33_ = !lean_is_exclusive(v___x_16_);
if (v_isSharedCheck_33_ == 0)
{
v___x_28_ = v___x_16_;
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_a_26_);
lean_dec(v___x_16_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_31_; 
if (v_isShared_29_ == 0)
{
v___x_31_ = v___x_28_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_a_26_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
}
v___jp_10_:
{
lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_12_ = l_Lean_Expr_app___override(v_f_1_, v_a_2_);
v___x_13_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_12_, v___y_11_);
lean_dec(v___y_11_);
return v___x_13_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg___boxed(lean_object* v_f_34_, lean_object* v_a_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(v_f_34_, v_a_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1(lean_object* v_f_44_, lean_object* v_a_u2081_45_, lean_object* v_a_u2082_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v___x_57_; 
lean_inc(v___y_55_);
lean_inc_ref(v___y_54_);
lean_inc(v___y_53_);
lean_inc_ref(v___y_52_);
lean_inc(v___y_51_);
lean_inc_ref(v___y_50_);
v___x_57_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(v_f_44_, v_a_u2081_45_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_object* v_a_58_; lean_object* v___x_59_; 
v_a_58_ = lean_ctor_get(v___x_57_, 0);
lean_inc(v_a_58_);
lean_dec_ref(v___x_57_);
v___x_59_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(v_a_58_, v_a_u2082_46_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
return v___x_59_;
}
else
{
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec_ref(v_a_u2082_46_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1___boxed(lean_object* v_f_60_, lean_object* v_a_u2081_61_, lean_object* v_a_u2082_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1(v_f_60_, v_a_u2081_61_, v_a_u2082_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(lean_object* v_f_74_, lean_object* v_a_u2081_75_, lean_object* v_a_u2082_76_, lean_object* v_a_u2083_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_88_; 
lean_inc(v___y_86_);
lean_inc_ref(v___y_85_);
lean_inc(v___y_84_);
lean_inc_ref(v___y_83_);
lean_inc(v___y_82_);
lean_inc_ref(v___y_81_);
v___x_88_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1(v_f_74_, v_a_u2081_75_, v_a_u2082_76_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_90_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_a_89_);
lean_dec_ref(v___x_88_);
v___x_90_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(v_a_89_, v_a_u2083_77_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
return v___x_90_;
}
else
{
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec_ref(v_a_u2083_77_);
return v___x_88_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0___boxed(lean_object* v_f_91_, lean_object* v_a_u2081_92_, lean_object* v_a_u2082_93_, lean_object* v_a_u2083_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(v_f_91_, v_a_u2081_92_, v_a_u2082_93_, v_a_u2083_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(lean_object* v_f_106_, lean_object* v_a_u2081_107_, lean_object* v_a_u2082_108_, lean_object* v_a_u2083_109_, lean_object* v_a_u2084_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v___x_121_; 
lean_inc(v___y_119_);
lean_inc_ref(v___y_118_);
lean_inc(v___y_117_);
lean_inc_ref(v___y_116_);
lean_inc(v___y_115_);
lean_inc_ref(v___y_114_);
v___x_121_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(v_f_106_, v_a_u2081_107_, v_a_u2082_108_, v_a_u2083_109_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; lean_object* v___x_123_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_a_122_);
lean_dec_ref(v___x_121_);
v___x_123_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(v_a_122_, v_a_u2084_110_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
return v___x_123_;
}
else
{
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec_ref(v_a_u2084_110_);
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0___boxed(lean_object* v_f_124_, lean_object* v_a_u2081_125_, lean_object* v_a_u2082_126_, lean_object* v_a_u2083_127_, lean_object* v_a_u2084_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(v_f_124_, v_a_u2081_125_, v_a_u2082_126_, v_a_u2083_127_, v_a_u2084_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
return v_res_139_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = lean_box(0);
v___x_153_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__7));
v___x_154_ = l_Lean_mkConst(v___x_153_, v___x_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0(uint8_t v___x_168_, lean_object* v_e_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v___x_183_; uint8_t v___x_184_; 
lean_inc_ref(v_e_169_);
v___x_183_ = l_Lean_Expr_cleanupAnnotations(v_e_169_);
v___x_184_ = l_Lean_Expr_isApp(v___x_183_);
if (v___x_184_ == 0)
{
lean_dec_ref(v___x_183_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v_e_169_);
goto v___jp_180_;
}
else
{
lean_object* v_arg_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v_arg_185_ = lean_ctor_get(v___x_183_, 1);
lean_inc_ref(v_arg_185_);
v___x_186_ = l_Lean_Expr_appFnCleanup___redArg(v___x_183_);
v___x_187_ = l_Lean_Expr_isApp(v___x_186_);
if (v___x_187_ == 0)
{
lean_dec_ref(v___x_186_);
lean_dec_ref(v_arg_185_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v_e_169_);
goto v___jp_180_;
}
else
{
lean_object* v_arg_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v_arg_188_ = lean_ctor_get(v___x_186_, 1);
lean_inc_ref(v_arg_188_);
v___x_189_ = l_Lean_Expr_appFnCleanup___redArg(v___x_186_);
v___x_190_ = l_Lean_Expr_isApp(v___x_189_);
if (v___x_190_ == 0)
{
lean_dec_ref(v___x_189_);
lean_dec_ref(v_arg_188_);
lean_dec_ref(v_arg_185_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v_e_169_);
goto v___jp_180_;
}
else
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = l_Lean_Expr_appFnCleanup___redArg(v___x_189_);
v___x_192_ = l_Lean_Expr_isApp(v___x_191_);
if (v___x_192_ == 0)
{
lean_dec_ref(v___x_191_);
lean_dec_ref(v_arg_188_);
lean_dec_ref(v_arg_185_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v_e_169_);
goto v___jp_180_;
}
else
{
lean_object* v_arg_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v_arg_193_ = lean_ctor_get(v___x_191_, 1);
lean_inc_ref(v_arg_193_);
v___x_194_ = l_Lean_Expr_appFnCleanup___redArg(v___x_191_);
v___x_195_ = l_Lean_Expr_isApp(v___x_194_);
if (v___x_195_ == 0)
{
lean_dec_ref(v___x_194_);
lean_dec_ref(v_arg_193_);
lean_dec_ref(v_arg_188_);
lean_dec_ref(v_arg_185_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v_e_169_);
goto v___jp_180_;
}
else
{
lean_object* v_arg_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_arg_196_ = lean_ctor_get(v___x_194_, 1);
lean_inc_ref(v_arg_196_);
v___x_197_ = l_Lean_Expr_appFnCleanup___redArg(v___x_194_);
v___x_198_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__1));
v___x_199_ = l_Lean_Expr_isConstOf(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
lean_dec_ref(v___x_197_);
lean_dec_ref(v_arg_196_);
lean_dec_ref(v_arg_193_);
lean_dec_ref(v_arg_188_);
lean_dec_ref(v_arg_185_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v_e_169_);
goto v___jp_180_;
}
else
{
lean_object* v___x_200_; 
lean_inc(v___y_178_);
lean_inc_ref(v___y_177_);
lean_inc(v___y_176_);
lean_inc_ref(v___y_175_);
lean_inc(v___y_174_);
lean_inc_ref(v___y_173_);
lean_inc(v___y_172_);
lean_inc_ref(v___y_171_);
lean_inc(v___y_170_);
lean_inc_ref(v_arg_193_);
v___x_200_ = lean_sym_simp(v_arg_193_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
lean_dec_ref(v___x_200_);
if (lean_obj_tag(v_a_201_) == 0)
{
lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_258_; 
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v_e_169_);
v_isSharedCheck_258_ = !lean_is_exclusive(v_a_201_);
if (v_isSharedCheck_258_ == 0)
{
v___x_203_ = v_a_201_;
v_isShared_204_ = v_isSharedCheck_258_;
goto v_resetjp_202_;
}
else
{
lean_dec(v_a_201_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_258_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_193_, v___y_173_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_249_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_249_ == 0)
{
v___x_208_ = v___x_205_;
v_isShared_209_ = v_isSharedCheck_249_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_249_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
uint8_t v___x_210_; 
v___x_210_ = lean_unbox(v_a_206_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; 
lean_del_object(v___x_208_);
v___x_211_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_193_, v___y_173_);
lean_dec_ref(v___y_173_);
lean_dec_ref(v_arg_193_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_232_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_232_ == 0)
{
v___x_214_ = v___x_211_;
v_isShared_215_ = v_isSharedCheck_232_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_232_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
uint8_t v___x_216_; 
v___x_216_ = lean_unbox(v_a_212_);
lean_dec(v_a_212_);
if (v___x_216_ == 0)
{
lean_object* v___x_218_; 
lean_dec(v_a_206_);
lean_dec_ref(v___x_197_);
lean_dec_ref(v_arg_196_);
lean_dec_ref(v_arg_188_);
lean_dec_ref(v_arg_185_);
if (v_isShared_204_ == 0)
{
v___x_218_ = v___x_203_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 0, 1);
v___x_218_ = v_reuseFailAlloc_222_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_220_; 
lean_ctor_set_uint8(v___x_218_, 0, v___x_199_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_218_);
v___x_220_ = v___x_214_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; lean_object* v___x_230_; 
lean_del_object(v___x_203_);
v___x_223_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__3));
v___x_224_ = l_Lean_Expr_constLevels_x21(v___x_197_);
lean_dec_ref(v___x_197_);
v___x_225_ = l_Lean_mkConst(v___x_223_, v___x_224_);
lean_inc_ref(v_arg_185_);
v___x_226_ = l_Lean_mkApp3(v___x_225_, v_arg_196_, v_arg_188_, v_arg_185_);
v___x_227_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_227_, 0, v_arg_185_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = lean_unbox(v_a_206_);
lean_dec(v_a_206_);
lean_ctor_set_uint8(v___x_227_, sizeof(void*)*2, v___x_228_);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_227_);
v___x_230_ = v___x_214_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_227_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec(v_a_206_);
lean_del_object(v___x_203_);
lean_dec_ref(v___x_197_);
lean_dec_ref(v_arg_196_);
lean_dec_ref(v_arg_188_);
lean_dec_ref(v_arg_185_);
v_a_233_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_211_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_211_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
else
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
lean_dec(v_a_206_);
lean_del_object(v___x_203_);
lean_dec_ref(v_arg_193_);
lean_dec_ref(v___y_173_);
v___x_241_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__5));
v___x_242_ = l_Lean_Expr_constLevels_x21(v___x_197_);
lean_dec_ref(v___x_197_);
v___x_243_ = l_Lean_mkConst(v___x_241_, v___x_242_);
lean_inc_ref(v_arg_188_);
v___x_244_ = l_Lean_mkApp3(v___x_243_, v_arg_196_, v_arg_188_, v_arg_185_);
v___x_245_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_245_, 0, v_arg_188_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*2, v___x_168_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_245_);
v___x_247_ = v___x_208_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
lean_del_object(v___x_203_);
lean_dec_ref(v___x_197_);
lean_dec_ref(v_arg_196_);
lean_dec_ref(v_arg_193_);
lean_dec_ref(v_arg_188_);
lean_dec_ref(v_arg_185_);
lean_dec_ref(v___y_173_);
v_a_250_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_205_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_205_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
}
else
{
lean_object* v_e_x27_259_; lean_object* v_proof_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_371_; 
lean_dec_ref(v___x_197_);
lean_dec_ref(v_arg_196_);
lean_dec_ref(v_arg_193_);
v_e_x27_259_ = lean_ctor_get(v_a_201_, 0);
v_proof_260_ = lean_ctor_get(v_a_201_, 1);
v_isSharedCheck_371_ = !lean_is_exclusive(v_a_201_);
if (v_isSharedCheck_371_ == 0)
{
v___x_262_ = v_a_201_;
v_isShared_263_ = v_isSharedCheck_371_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_proof_260_);
lean_inc(v_e_x27_259_);
lean_dec(v_a_201_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_371_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; 
v___x_264_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_259_, v___y_173_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_362_; 
v_a_265_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_362_ == 0)
{
v___x_267_ = v___x_264_;
v_isShared_268_ = v_isSharedCheck_362_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_264_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_362_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
uint8_t v___x_269_; 
v___x_269_ = lean_unbox(v_a_265_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; 
lean_del_object(v___x_267_);
v___x_270_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_259_, v___y_173_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_344_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_344_ == 0)
{
v___x_273_ = v___x_270_;
v_isShared_274_ = v_isSharedCheck_344_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_270_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_344_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
uint8_t v___x_275_; 
v___x_275_ = lean_unbox(v_a_271_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
lean_del_object(v___x_273_);
lean_dec(v_a_265_);
v___x_276_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8, &l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8_once, _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8);
lean_inc_ref(v_e_x27_259_);
v___x_277_ = l_Lean_Expr_app___override(v___x_276_, v_e_x27_259_);
v___x_278_ = lean_box(0);
lean_inc(v___y_178_);
lean_inc_ref(v___y_177_);
lean_inc(v___y_176_);
lean_inc_ref(v___y_175_);
v___x_279_ = l_Lean_Meta_trySynthInstance(v___x_277_, v___x_278_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_325_; 
v_a_280_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_325_ == 0)
{
v___x_282_ = v___x_279_;
v_isShared_283_ = v_isSharedCheck_325_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_325_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
if (lean_obj_tag(v_a_280_) == 1)
{
lean_object* v_a_284_; lean_object* v___x_285_; 
lean_del_object(v___x_282_);
lean_dec(v_a_271_);
v_a_284_ = lean_ctor_get(v_a_280_, 0);
lean_inc(v_a_284_);
lean_dec_ref(v_a_280_);
v___x_285_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_284_, v___y_174_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_a_286_);
lean_dec_ref(v___x_285_);
v___x_287_ = lean_unsigned_to_nat(4u);
v___x_288_ = l_Lean_Expr_getBoundedAppFn(v___x_287_, v_e_169_);
lean_inc(v_a_286_);
lean_inc_ref(v_e_x27_259_);
v___x_289_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(v___x_288_, v_e_x27_259_, v_a_286_, v_arg_188_, v_arg_185_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_303_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_303_ == 0)
{
v___x_292_ = v___x_289_;
v_isShared_293_ = v_isSharedCheck_303_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_289_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_303_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_294_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12));
v___x_295_ = l_Lean_Expr_replaceFn(v_e_169_, v___x_294_);
v___x_296_ = l_Lean_mkApp3(v___x_295_, v_e_x27_259_, v_a_286_, v_proof_260_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___x_296_);
lean_ctor_set(v___x_262_, 0, v_a_290_);
v___x_298_ = v___x_262_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_290_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v___x_296_);
v___x_298_ = v_reuseFailAlloc_302_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_300_; 
lean_ctor_set_uint8(v___x_298_, sizeof(void*)*2, v___x_199_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 0, v___x_298_);
v___x_300_ = v___x_292_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
else
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_dec(v_a_286_);
lean_del_object(v___x_262_);
lean_dec_ref(v_proof_260_);
lean_dec_ref(v_e_x27_259_);
lean_dec_ref(v_e_169_);
v_a_304_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_289_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_289_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
lean_del_object(v___x_262_);
lean_dec_ref(v_proof_260_);
lean_dec_ref(v_e_x27_259_);
lean_dec_ref(v_arg_188_);
lean_dec_ref(v_arg_185_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v_e_169_);
v_a_312_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_285_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_285_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
else
{
lean_object* v___x_320_; uint8_t v___x_321_; lean_object* v___x_323_; 
lean_dec(v_a_280_);
lean_del_object(v___x_262_);
lean_dec_ref(v_proof_260_);
lean_dec_ref(v_e_x27_259_);
lean_dec_ref(v_arg_188_);
lean_dec_ref(v_arg_185_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v_e_169_);
v___x_320_ = lean_alloc_ctor(0, 0, 1);
v___x_321_ = lean_unbox(v_a_271_);
lean_dec(v_a_271_);
lean_ctor_set_uint8(v___x_320_, 0, v___x_321_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 0, v___x_320_);
v___x_323_ = v___x_282_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_320_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_dec(v_a_271_);
lean_del_object(v___x_262_);
lean_dec_ref(v_proof_260_);
lean_dec_ref(v_e_x27_259_);
lean_dec_ref(v_arg_188_);
lean_dec_ref(v_arg_185_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v_e_169_);
v_a_326_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_279_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_279_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
lean_dec(v_a_271_);
lean_dec_ref(v_e_x27_259_);
lean_dec_ref(v_arg_188_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
v___x_334_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__14));
v___x_335_ = l_Lean_Expr_replaceFn(v_e_169_, v___x_334_);
v___x_336_ = l_Lean_Expr_app___override(v___x_335_, v_proof_260_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___x_336_);
lean_ctor_set(v___x_262_, 0, v_arg_185_);
v___x_338_ = v___x_262_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_arg_185_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v___x_336_);
v___x_338_ = v_reuseFailAlloc_343_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
uint8_t v___x_339_; lean_object* v___x_341_; 
v___x_339_ = lean_unbox(v_a_265_);
lean_dec(v_a_265_);
lean_ctor_set_uint8(v___x_338_, sizeof(void*)*2, v___x_339_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_338_);
v___x_341_ = v___x_273_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_338_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec(v_a_265_);
lean_del_object(v___x_262_);
lean_dec_ref(v_proof_260_);
lean_dec_ref(v_e_x27_259_);
lean_dec_ref(v_arg_188_);
lean_dec_ref(v_arg_185_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v_e_169_);
v_a_345_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_270_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_270_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_357_; 
lean_dec(v_a_265_);
lean_dec_ref(v_e_x27_259_);
lean_dec_ref(v_arg_185_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
v___x_353_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__16));
v___x_354_ = l_Lean_Expr_replaceFn(v_e_169_, v___x_353_);
v___x_355_ = l_Lean_Expr_app___override(v___x_354_, v_proof_260_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___x_355_);
lean_ctor_set(v___x_262_, 0, v_arg_188_);
v___x_357_ = v___x_262_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_arg_188_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v___x_355_);
v___x_357_ = v_reuseFailAlloc_361_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_359_; 
lean_ctor_set_uint8(v___x_357_, sizeof(void*)*2, v___x_168_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 0, v___x_357_);
v___x_359_ = v___x_267_;
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
}
}
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
lean_del_object(v___x_262_);
lean_dec_ref(v_proof_260_);
lean_dec_ref(v_e_x27_259_);
lean_dec_ref(v_arg_188_);
lean_dec_ref(v_arg_185_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v_e_169_);
v_a_363_ = lean_ctor_get(v___x_264_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_264_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_264_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_264_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_197_);
lean_dec_ref(v_arg_196_);
lean_dec_ref(v_arg_193_);
lean_dec_ref(v_arg_188_);
lean_dec_ref(v_arg_185_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v_e_169_);
return v___x_200_;
}
}
}
}
}
}
}
v___jp_180_:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_181_, 0, v___x_168_);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___boxed(lean_object* v___x_372_, lean_object* v_e_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
uint8_t v___x_21847__boxed_384_; lean_object* v_res_385_; 
v___x_21847__boxed_384_ = lean_unbox(v___x_372_);
v_res_385_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0(v___x_21847__boxed_384_, v_e_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte(lean_object* v_e_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_){
_start:
{
lean_object* v_numArgs_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v_numArgs_397_ = l_Lean_Expr_getAppNumArgs(v_e_386_);
v___x_398_ = lean_unsigned_to_nat(5u);
v___x_399_ = lean_nat_dec_lt(v_numArgs_397_, v___x_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___f_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_400_ = lean_box(v___x_399_);
v___f_401_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___boxed), 12, 1);
lean_closure_set(v___f_401_, 0, v___x_400_);
v___x_402_ = lean_nat_sub(v_numArgs_397_, v___x_398_);
lean_dec(v_numArgs_397_);
v___x_403_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_386_, v___x_402_, v___f_401_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_);
lean_dec(v___x_402_);
return v___x_403_;
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec(v_numArgs_397_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_e_386_);
v___x_404_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_404_, 0, v___x_399_);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___boxed(lean_object* v_e_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte(v_e_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1(lean_object* v_f_418_, lean_object* v_a_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(v_f_418_, v_a_419_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___boxed(lean_object* v_f_431_, lean_object* v_a_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1(v_f_431_, v_a_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
return v_res_443_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = lean_box(0);
v___x_451_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__3));
v___x_452_ = l_Lean_mkConst(v___x_451_, v___x_450_);
return v___x_452_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_453_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4, &l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4);
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = lean_mk_empty_array_with_capacity(v___x_454_);
v___x_456_ = lean_array_push(v___x_455_, v___x_453_);
return v___x_456_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_box(0);
v___x_466_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__10));
v___x_467_ = l_Lean_mkConst(v___x_466_, v___x_465_);
return v___x_467_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_468_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11, &l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11_once, _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11);
v___x_469_ = lean_unsigned_to_nat(1u);
v___x_470_ = lean_mk_empty_array_with_capacity(v___x_469_);
v___x_471_ = lean_array_push(v___x_470_, v___x_468_);
return v___x_471_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = lean_box(0);
v___x_484_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__19));
v___x_485_ = l_Lean_mkConst(v___x_484_, v___x_483_);
return v___x_485_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = l_Lean_mkBVar(v___x_486_);
return v___x_487_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_492_ = lean_box(0);
v___x_493_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__23));
v___x_494_ = l_Lean_mkConst(v___x_493_, v___x_492_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0(uint8_t v___x_506_, lean_object* v_e_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v___x_521_; uint8_t v___x_522_; 
lean_inc_ref(v_e_507_);
v___x_521_ = l_Lean_Expr_cleanupAnnotations(v_e_507_);
v___x_522_ = l_Lean_Expr_isApp(v___x_521_);
if (v___x_522_ == 0)
{
lean_dec_ref(v___x_521_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v_e_507_);
goto v___jp_518_;
}
else
{
lean_object* v_arg_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v_arg_523_ = lean_ctor_get(v___x_521_, 1);
lean_inc_ref(v_arg_523_);
v___x_524_ = l_Lean_Expr_appFnCleanup___redArg(v___x_521_);
v___x_525_ = l_Lean_Expr_isApp(v___x_524_);
if (v___x_525_ == 0)
{
lean_dec_ref(v___x_524_);
lean_dec_ref(v_arg_523_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v_e_507_);
goto v___jp_518_;
}
else
{
lean_object* v_arg_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v_arg_526_ = lean_ctor_get(v___x_524_, 1);
lean_inc_ref(v_arg_526_);
v___x_527_ = l_Lean_Expr_appFnCleanup___redArg(v___x_524_);
v___x_528_ = l_Lean_Expr_isApp(v___x_527_);
if (v___x_528_ == 0)
{
lean_dec_ref(v___x_527_);
lean_dec_ref(v_arg_526_);
lean_dec_ref(v_arg_523_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v_e_507_);
goto v___jp_518_;
}
else
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = l_Lean_Expr_appFnCleanup___redArg(v___x_527_);
v___x_530_ = l_Lean_Expr_isApp(v___x_529_);
if (v___x_530_ == 0)
{
lean_dec_ref(v___x_529_);
lean_dec_ref(v_arg_526_);
lean_dec_ref(v_arg_523_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v_e_507_);
goto v___jp_518_;
}
else
{
lean_object* v_arg_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v_arg_531_ = lean_ctor_get(v___x_529_, 1);
lean_inc_ref(v_arg_531_);
v___x_532_ = l_Lean_Expr_appFnCleanup___redArg(v___x_529_);
v___x_533_ = l_Lean_Expr_isApp(v___x_532_);
if (v___x_533_ == 0)
{
lean_dec_ref(v___x_532_);
lean_dec_ref(v_arg_531_);
lean_dec_ref(v_arg_526_);
lean_dec_ref(v_arg_523_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v_e_507_);
goto v___jp_518_;
}
else
{
lean_object* v_arg_534_; lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v_arg_534_ = lean_ctor_get(v___x_532_, 1);
lean_inc_ref(v_arg_534_);
v___x_535_ = l_Lean_Expr_appFnCleanup___redArg(v___x_532_);
v___x_536_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__1));
v___x_537_ = l_Lean_Expr_isConstOf(v___x_535_, v___x_536_);
if (v___x_537_ == 0)
{
lean_dec_ref(v___x_535_);
lean_dec_ref(v_arg_534_);
lean_dec_ref(v_arg_531_);
lean_dec_ref(v_arg_526_);
lean_dec_ref(v_arg_523_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v_e_507_);
goto v___jp_518_;
}
else
{
lean_object* v___x_538_; 
lean_inc(v___y_516_);
lean_inc_ref(v___y_515_);
lean_inc(v___y_514_);
lean_inc_ref(v___y_513_);
lean_inc(v___y_512_);
lean_inc_ref(v___y_511_);
lean_inc(v___y_510_);
lean_inc_ref(v___y_509_);
lean_inc(v___y_508_);
lean_inc_ref(v_arg_531_);
v___x_538_ = lean_sym_simp(v_arg_531_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref(v___x_538_);
if (lean_obj_tag(v_a_539_) == 0)
{
lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_626_; 
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v_e_507_);
v_isSharedCheck_626_ = !lean_is_exclusive(v_a_539_);
if (v_isSharedCheck_626_ == 0)
{
v___x_541_ = v_a_539_;
v_isShared_542_ = v_isSharedCheck_626_;
goto v_resetjp_540_;
}
else
{
lean_dec(v_a_539_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_626_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_531_, v___y_511_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; uint8_t v___x_545_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_544_);
lean_dec_ref(v___x_543_);
v___x_545_ = lean_unbox(v_a_544_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_531_, v___y_511_);
lean_dec_ref(v___y_511_);
lean_dec_ref(v_arg_531_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_585_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_585_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_585_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_585_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
uint8_t v___x_551_; 
v___x_551_ = lean_unbox(v_a_547_);
lean_dec(v_a_547_);
if (v___x_551_ == 0)
{
lean_object* v___x_553_; 
lean_dec(v_a_544_);
lean_dec_ref(v___x_535_);
lean_dec_ref(v_arg_534_);
lean_dec_ref(v_arg_526_);
lean_dec_ref(v_arg_523_);
lean_dec(v___y_512_);
if (v_isShared_542_ == 0)
{
v___x_553_ = v___x_541_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 0, 1);
v___x_553_ = v_reuseFailAlloc_557_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_555_; 
lean_ctor_set_uint8(v___x_553_, 0, v___x_537_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 0, v___x_553_);
v___x_555_ = v___x_549_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
else
{
lean_object* v___x_558_; uint8_t v___x_559_; uint8_t v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
lean_del_object(v___x_549_);
lean_del_object(v___x_541_);
v___x_558_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5, &l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5_once, _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5);
v___x_559_ = lean_unbox(v_a_544_);
v___x_560_ = lean_unbox(v_a_544_);
lean_inc_ref(v_arg_523_);
v___x_561_ = l_Lean_Expr_betaRev(v_arg_523_, v___x_558_, v___x_559_, v___x_560_);
v___x_562_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_561_, v___y_512_);
lean_dec(v___y_512_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_576_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_576_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_576_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_576_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; lean_object* v___x_574_; 
v___x_567_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__7));
v___x_568_ = l_Lean_Expr_constLevels_x21(v___x_535_);
lean_dec_ref(v___x_535_);
v___x_569_ = l_Lean_mkConst(v___x_567_, v___x_568_);
v___x_570_ = l_Lean_mkApp3(v___x_569_, v_arg_534_, v_arg_526_, v_arg_523_);
v___x_571_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_571_, 0, v_a_563_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = lean_unbox(v_a_544_);
lean_dec(v_a_544_);
lean_ctor_set_uint8(v___x_571_, sizeof(void*)*2, v___x_572_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_571_);
v___x_574_ = v___x_565_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_571_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec(v_a_544_);
lean_dec_ref(v___x_535_);
lean_dec_ref(v_arg_534_);
lean_dec_ref(v_arg_526_);
lean_dec_ref(v_arg_523_);
v_a_577_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_562_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_562_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec(v_a_544_);
lean_del_object(v___x_541_);
lean_dec_ref(v___x_535_);
lean_dec_ref(v_arg_534_);
lean_dec_ref(v_arg_526_);
lean_dec_ref(v_arg_523_);
lean_dec(v___y_512_);
v_a_586_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_546_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_546_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec(v_a_544_);
lean_del_object(v___x_541_);
lean_dec_ref(v_arg_531_);
lean_dec_ref(v___y_511_);
v___x_594_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12, &l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12_once, _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12);
lean_inc_ref(v_arg_526_);
v___x_595_ = l_Lean_Expr_betaRev(v_arg_526_, v___x_594_, v___x_506_, v___x_506_);
v___x_596_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_595_, v___y_512_);
lean_dec(v___y_512_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_609_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_609_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_609_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_609_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_601_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__14));
v___x_602_ = l_Lean_Expr_constLevels_x21(v___x_535_);
lean_dec_ref(v___x_535_);
v___x_603_ = l_Lean_mkConst(v___x_601_, v___x_602_);
v___x_604_ = l_Lean_mkApp3(v___x_603_, v_arg_534_, v_arg_526_, v_arg_523_);
v___x_605_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_605_, 0, v_a_597_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*2, v___x_506_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_605_);
v___x_607_ = v___x_599_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec_ref(v___x_535_);
lean_dec_ref(v_arg_534_);
lean_dec_ref(v_arg_526_);
lean_dec_ref(v_arg_523_);
v_a_610_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_596_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_596_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
lean_del_object(v___x_541_);
lean_dec_ref(v___x_535_);
lean_dec_ref(v_arg_534_);
lean_dec_ref(v_arg_531_);
lean_dec_ref(v_arg_526_);
lean_dec_ref(v_arg_523_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
v_a_618_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_543_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_543_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
else
{
lean_object* v_e_x27_627_; lean_object* v_proof_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_841_; 
lean_dec_ref(v___x_535_);
lean_dec_ref(v_arg_534_);
v_e_x27_627_ = lean_ctor_get(v_a_539_, 0);
v_proof_628_ = lean_ctor_get(v_a_539_, 1);
v_isSharedCheck_841_ = !lean_is_exclusive(v_a_539_);
if (v_isSharedCheck_841_ == 0)
{
v___x_630_ = v_a_539_;
v_isShared_631_ = v_isSharedCheck_841_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_proof_628_);
lean_inc(v_e_x27_627_);
lean_dec(v_a_539_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_841_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_627_, v___y_511_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; uint8_t v___x_634_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref(v___x_632_);
v___x_634_ = lean_unbox(v_a_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_627_, v___y_511_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; uint8_t v___x_637_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref(v___x_635_);
v___x_637_ = lean_unbox(v_a_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec(v_a_633_);
v___x_638_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8, &l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8_once, _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8);
lean_inc_ref(v_e_x27_627_);
v___x_639_ = l_Lean_Expr_app___override(v___x_638_, v_e_x27_627_);
v___x_640_ = lean_box(0);
lean_inc(v___y_516_);
lean_inc_ref(v___y_515_);
lean_inc(v___y_514_);
lean_inc_ref(v___y_513_);
v___x_641_ = l_Lean_Meta_trySynthInstance(v___x_639_, v___x_640_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_737_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_737_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_737_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_737_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
if (lean_obj_tag(v_a_642_) == 1)
{
lean_object* v_a_646_; lean_object* v___x_647_; 
lean_del_object(v___x_644_);
v_a_646_ = lean_ctor_get(v_a_642_, 0);
lean_inc(v_a_646_);
lean_dec_ref(v_a_642_);
v___x_647_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_646_, v___y_512_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_649_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref(v___x_647_);
v___x_649_ = l_Lean_Meta_Sym_shareCommon___redArg(v_proof_628_, v___y_512_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_651_; uint8_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; uint8_t v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref(v___x_649_);
v___x_651_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__16));
v___x_652_ = 0;
v___x_653_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20, &l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20_once, _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20);
v___x_654_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21, &l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21_once, _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21);
lean_inc(v_a_650_);
lean_inc_ref(v_e_x27_627_);
lean_inc_ref(v_arg_531_);
v___x_655_ = l_Lean_mkApp4(v___x_653_, v_arg_531_, v_e_x27_627_, v_a_650_, v___x_654_);
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = lean_mk_empty_array_with_capacity(v___x_656_);
lean_inc_ref(v___x_657_);
v___x_658_ = lean_array_push(v___x_657_, v___x_655_);
v___x_659_ = lean_unbox(v_a_636_);
v___x_660_ = lean_unbox(v_a_636_);
v___x_661_ = l_Lean_Expr_betaRev(v_arg_526_, v___x_658_, v___x_659_, v___x_660_);
lean_dec_ref(v___x_658_);
lean_inc_ref(v_e_x27_627_);
v___x_662_ = l_Lean_mkLambda(v___x_651_, v___x_652_, v_e_x27_627_, v___x_661_);
v___x_663_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_662_, v___y_512_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; uint8_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_a_664_);
lean_dec_ref(v___x_663_);
lean_inc_ref(v_e_x27_627_);
v___x_665_ = l_Lean_mkNot(v_e_x27_627_);
v___x_666_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24, &l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24_once, _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24);
lean_inc(v_a_650_);
lean_inc_ref(v_e_x27_627_);
v___x_667_ = l_Lean_mkApp4(v___x_666_, v_arg_531_, v_e_x27_627_, v_a_650_, v___x_654_);
v___x_668_ = lean_array_push(v___x_657_, v___x_667_);
v___x_669_ = lean_unbox(v_a_636_);
v___x_670_ = lean_unbox(v_a_636_);
lean_dec(v_a_636_);
v___x_671_ = l_Lean_Expr_betaRev(v_arg_523_, v___x_668_, v___x_669_, v___x_670_);
lean_dec_ref(v___x_668_);
v___x_672_ = l_Lean_mkLambda(v___x_651_, v___x_652_, v___x_665_, v___x_671_);
v___x_673_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_672_, v___y_512_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref(v___x_673_);
v___x_675_ = lean_unsigned_to_nat(4u);
v___x_676_ = l_Lean_Expr_getBoundedAppFn(v___x_675_, v_e_507_);
lean_inc(v_a_648_);
lean_inc_ref(v_e_x27_627_);
v___x_677_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(v___x_676_, v_e_x27_627_, v_a_648_, v_a_664_, v_a_674_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_691_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_691_ == 0)
{
v___x_680_ = v___x_677_;
v_isShared_681_ = v_isSharedCheck_691_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_677_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_691_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_682_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26));
v___x_683_ = l_Lean_Expr_replaceFn(v_e_507_, v___x_682_);
v___x_684_ = l_Lean_mkApp3(v___x_683_, v_e_x27_627_, v_a_648_, v_a_650_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___x_684_);
lean_ctor_set(v___x_630_, 0, v_a_678_);
v___x_686_ = v___x_630_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_678_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v___x_684_);
v___x_686_ = v_reuseFailAlloc_690_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_688_; 
lean_ctor_set_uint8(v___x_686_, sizeof(void*)*2, v___x_537_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_686_);
v___x_688_ = v___x_680_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_686_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_dec(v_a_650_);
lean_dec(v_a_648_);
lean_del_object(v___x_630_);
lean_dec_ref(v_e_x27_627_);
lean_dec_ref(v_e_507_);
v_a_692_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_677_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_677_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_dec(v_a_664_);
lean_dec(v_a_650_);
lean_dec(v_a_648_);
lean_del_object(v___x_630_);
lean_dec_ref(v_e_x27_627_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v_e_507_);
v_a_700_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_673_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_673_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec_ref(v___x_657_);
lean_dec(v_a_650_);
lean_dec(v_a_648_);
lean_dec(v_a_636_);
lean_del_object(v___x_630_);
lean_dec_ref(v_e_x27_627_);
lean_dec_ref(v_arg_531_);
lean_dec_ref(v_arg_523_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v_e_507_);
v_a_708_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_663_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_663_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec(v_a_648_);
lean_dec(v_a_636_);
lean_del_object(v___x_630_);
lean_dec_ref(v_e_x27_627_);
lean_dec_ref(v_arg_531_);
lean_dec_ref(v_arg_526_);
lean_dec_ref(v_arg_523_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v_e_507_);
v_a_716_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_649_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_649_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v_a_636_);
lean_del_object(v___x_630_);
lean_dec_ref(v_proof_628_);
lean_dec_ref(v_e_x27_627_);
lean_dec_ref(v_arg_531_);
lean_dec_ref(v_arg_526_);
lean_dec_ref(v_arg_523_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v_e_507_);
v_a_724_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_647_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_647_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
else
{
lean_object* v___x_732_; uint8_t v___x_733_; lean_object* v___x_735_; 
lean_dec(v_a_642_);
lean_del_object(v___x_630_);
lean_dec_ref(v_proof_628_);
lean_dec_ref(v_e_x27_627_);
lean_dec_ref(v_arg_531_);
lean_dec_ref(v_arg_526_);
lean_dec_ref(v_arg_523_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v_e_507_);
v___x_732_ = lean_alloc_ctor(0, 0, 1);
v___x_733_ = lean_unbox(v_a_636_);
lean_dec(v_a_636_);
lean_ctor_set_uint8(v___x_732_, 0, v___x_733_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v___x_732_);
v___x_735_ = v___x_644_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_732_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec(v_a_636_);
lean_del_object(v___x_630_);
lean_dec_ref(v_proof_628_);
lean_dec_ref(v_e_x27_627_);
lean_dec_ref(v_arg_531_);
lean_dec_ref(v_arg_526_);
lean_dec_ref(v_arg_523_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v_e_507_);
v_a_738_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_641_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_641_);
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
else
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec(v_a_636_);
lean_dec_ref(v_e_x27_627_);
lean_dec_ref(v_arg_526_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_inc_ref(v_proof_628_);
v___x_746_ = l_Lean_Meta_mkOfEqFalseCore(v_arg_531_, v_proof_628_);
v___x_747_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_746_, v___y_512_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; uint8_t v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref(v___x_747_);
v___x_749_ = lean_unsigned_to_nat(1u);
v___x_750_ = lean_mk_empty_array_with_capacity(v___x_749_);
v___x_751_ = lean_array_push(v___x_750_, v_a_748_);
v___x_752_ = lean_unbox(v_a_633_);
v___x_753_ = lean_unbox(v_a_633_);
v___x_754_ = l_Lean_Expr_betaRev(v_arg_523_, v___x_751_, v___x_752_, v___x_753_);
lean_dec_ref(v___x_751_);
v___x_755_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_754_, v___y_512_);
lean_dec(v___y_512_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_770_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_770_ == 0)
{
v___x_758_ = v___x_755_;
v_isShared_759_ = v_isSharedCheck_770_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_755_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_770_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_760_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__28));
v___x_761_ = l_Lean_Expr_replaceFn(v_e_507_, v___x_760_);
v___x_762_ = l_Lean_Expr_app___override(v___x_761_, v_proof_628_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___x_762_);
lean_ctor_set(v___x_630_, 0, v_a_756_);
v___x_764_ = v___x_630_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_756_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_762_);
v___x_764_ = v_reuseFailAlloc_769_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
uint8_t v___x_765_; lean_object* v___x_767_; 
v___x_765_ = lean_unbox(v_a_633_);
lean_dec(v_a_633_);
lean_ctor_set_uint8(v___x_764_, sizeof(void*)*2, v___x_765_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_764_);
v___x_767_ = v___x_758_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v___x_764_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec(v_a_633_);
lean_del_object(v___x_630_);
lean_dec_ref(v_proof_628_);
lean_dec_ref(v_e_507_);
v_a_771_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_755_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_755_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec(v_a_633_);
lean_del_object(v___x_630_);
lean_dec_ref(v_proof_628_);
lean_dec_ref(v_arg_523_);
lean_dec(v___y_512_);
lean_dec_ref(v_e_507_);
v_a_779_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_747_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_747_);
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
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec(v_a_633_);
lean_del_object(v___x_630_);
lean_dec_ref(v_proof_628_);
lean_dec_ref(v_e_x27_627_);
lean_dec_ref(v_arg_531_);
lean_dec_ref(v_arg_526_);
lean_dec_ref(v_arg_523_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v_e_507_);
v_a_787_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_635_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_635_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; 
lean_dec(v_a_633_);
lean_dec_ref(v_e_x27_627_);
lean_dec_ref(v_arg_523_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_inc_ref(v_proof_628_);
v___x_795_ = l_Lean_Meta_mkOfEqTrueCore(v_arg_531_, v_proof_628_);
v___x_796_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_795_, v___y_512_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref(v___x_796_);
v___x_798_ = lean_unsigned_to_nat(1u);
v___x_799_ = lean_mk_empty_array_with_capacity(v___x_798_);
v___x_800_ = lean_array_push(v___x_799_, v_a_797_);
v___x_801_ = l_Lean_Expr_betaRev(v_arg_526_, v___x_800_, v___x_506_, v___x_506_);
lean_dec_ref(v___x_800_);
v___x_802_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_801_, v___y_512_);
lean_dec(v___y_512_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_816_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_816_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_816_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_816_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_807_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__30));
v___x_808_ = l_Lean_Expr_replaceFn(v_e_507_, v___x_807_);
v___x_809_ = l_Lean_Expr_app___override(v___x_808_, v_proof_628_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___x_809_);
lean_ctor_set(v___x_630_, 0, v_a_803_);
v___x_811_ = v___x_630_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_803_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v___x_809_);
v___x_811_ = v_reuseFailAlloc_815_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_813_; 
lean_ctor_set_uint8(v___x_811_, sizeof(void*)*2, v___x_506_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_811_);
v___x_813_ = v___x_805_;
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
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_del_object(v___x_630_);
lean_dec_ref(v_proof_628_);
lean_dec_ref(v_e_507_);
v_a_817_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_802_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_802_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_del_object(v___x_630_);
lean_dec_ref(v_proof_628_);
lean_dec_ref(v_arg_526_);
lean_dec(v___y_512_);
lean_dec_ref(v_e_507_);
v_a_825_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_796_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_796_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_del_object(v___x_630_);
lean_dec_ref(v_proof_628_);
lean_dec_ref(v_e_x27_627_);
lean_dec_ref(v_arg_531_);
lean_dec_ref(v_arg_526_);
lean_dec_ref(v_arg_523_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v_e_507_);
v_a_833_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_632_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_632_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_535_);
lean_dec_ref(v_arg_534_);
lean_dec_ref(v_arg_531_);
lean_dec_ref(v_arg_526_);
lean_dec_ref(v_arg_523_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v_e_507_);
return v___x_538_;
}
}
}
}
}
}
}
v___jp_518_:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_519_, 0, v___x_506_);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___boxed(lean_object* v___x_842_, lean_object* v_e_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
uint8_t v___x_37915__boxed_854_; lean_object* v_res_855_; 
v___x_37915__boxed_854_ = lean_unbox(v___x_842_);
v_res_855_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0(v___x_37915__boxed_854_, v_e_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte(lean_object* v_e_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_numArgs_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v_numArgs_867_ = l_Lean_Expr_getAppNumArgs(v_e_856_);
v___x_868_ = lean_unsigned_to_nat(5u);
v___x_869_ = lean_nat_dec_lt(v_numArgs_867_, v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; lean_object* v___f_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_870_ = lean_box(v___x_869_);
v___f_871_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___boxed), 12, 1);
lean_closure_set(v___f_871_, 0, v___x_870_);
v___x_872_ = lean_nat_sub(v_numArgs_867_, v___x_868_);
lean_dec(v_numArgs_867_);
v___x_873_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_856_, v___x_872_, v___f_871_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
lean_dec(v___x_872_);
return v___x_873_;
}
else
{
lean_object* v___x_874_; lean_object* v___x_875_; 
lean_dec(v_numArgs_867_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_e_856_);
v___x_874_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_874_, 0, v___x_869_);
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___boxed(lean_object* v_e_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte(v_e_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpCond___lam__0(uint8_t v___x_912_, lean_object* v_e_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_927_; uint8_t v___x_928_; 
lean_inc_ref(v_e_913_);
v___x_927_ = l_Lean_Expr_cleanupAnnotations(v_e_913_);
v___x_928_ = l_Lean_Expr_isApp(v___x_927_);
if (v___x_928_ == 0)
{
lean_dec_ref(v___x_927_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v_e_913_);
goto v___jp_924_;
}
else
{
lean_object* v_arg_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v_arg_929_ = lean_ctor_get(v___x_927_, 1);
lean_inc_ref(v_arg_929_);
v___x_930_ = l_Lean_Expr_appFnCleanup___redArg(v___x_927_);
v___x_931_ = l_Lean_Expr_isApp(v___x_930_);
if (v___x_931_ == 0)
{
lean_dec_ref(v___x_930_);
lean_dec_ref(v_arg_929_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v_e_913_);
goto v___jp_924_;
}
else
{
lean_object* v_arg_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
v_arg_932_ = lean_ctor_get(v___x_930_, 1);
lean_inc_ref(v_arg_932_);
v___x_933_ = l_Lean_Expr_appFnCleanup___redArg(v___x_930_);
v___x_934_ = l_Lean_Expr_isApp(v___x_933_);
if (v___x_934_ == 0)
{
lean_dec_ref(v___x_933_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v_e_913_);
goto v___jp_924_;
}
else
{
lean_object* v_arg_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v_arg_935_ = lean_ctor_get(v___x_933_, 1);
lean_inc_ref(v_arg_935_);
v___x_936_ = l_Lean_Expr_appFnCleanup___redArg(v___x_933_);
v___x_937_ = l_Lean_Expr_isApp(v___x_936_);
if (v___x_937_ == 0)
{
lean_dec_ref(v___x_936_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v_e_913_);
goto v___jp_924_;
}
else
{
lean_object* v_arg_938_; lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v_arg_938_ = lean_ctor_get(v___x_936_, 1);
lean_inc_ref(v_arg_938_);
v___x_939_ = l_Lean_Expr_appFnCleanup___redArg(v___x_936_);
v___x_940_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__1));
v___x_941_ = l_Lean_Expr_isConstOf(v___x_939_, v___x_940_);
if (v___x_941_ == 0)
{
lean_dec_ref(v___x_939_);
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v_e_913_);
goto v___jp_924_;
}
else
{
lean_object* v___x_942_; 
lean_inc(v___y_922_);
lean_inc_ref(v___y_921_);
lean_inc(v___y_920_);
lean_inc_ref(v___y_919_);
lean_inc(v___y_918_);
lean_inc_ref(v___y_917_);
lean_inc(v___y_916_);
lean_inc_ref(v___y_915_);
lean_inc(v___y_914_);
lean_inc_ref(v_arg_935_);
v___x_942_ = lean_sym_simp(v_arg_935_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref(v___x_942_);
if (lean_obj_tag(v_a_943_) == 0)
{
lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_999_; 
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v_e_913_);
v_isSharedCheck_999_ = !lean_is_exclusive(v_a_943_);
if (v_isSharedCheck_999_ == 0)
{
v___x_945_ = v_a_943_;
v_isShared_946_ = v_isSharedCheck_999_;
goto v_resetjp_944_;
}
else
{
lean_dec(v_a_943_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_999_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_917_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_990_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_990_ == 0)
{
v___x_950_ = v___x_947_;
v_isShared_951_ = v_isSharedCheck_990_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_947_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_990_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
uint8_t v___x_952_; 
v___x_952_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_935_, v_a_948_);
lean_dec(v_a_948_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
lean_del_object(v___x_950_);
v___x_953_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_917_);
lean_dec_ref(v___y_917_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_973_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_973_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_973_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_973_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
uint8_t v___x_958_; 
v___x_958_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_935_, v_a_954_);
lean_dec(v_a_954_);
lean_dec_ref(v_arg_935_);
if (v___x_958_ == 0)
{
lean_object* v___x_960_; 
lean_dec_ref(v___x_939_);
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
if (v_isShared_946_ == 0)
{
v___x_960_ = v___x_945_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 0, 1);
v___x_960_ = v_reuseFailAlloc_964_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_962_; 
lean_ctor_set_uint8(v___x_960_, 0, v___x_941_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_960_);
v___x_962_ = v___x_956_;
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
else
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
lean_del_object(v___x_945_);
v___x_965_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__3));
v___x_966_ = l_Lean_Expr_constLevels_x21(v___x_939_);
lean_dec_ref(v___x_939_);
v___x_967_ = l_Lean_mkConst(v___x_965_, v___x_966_);
lean_inc_ref(v_arg_929_);
v___x_968_ = l_Lean_mkApp3(v___x_967_, v_arg_938_, v_arg_932_, v_arg_929_);
v___x_969_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_969_, 0, v_arg_929_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
lean_ctor_set_uint8(v___x_969_, sizeof(void*)*2, v___x_952_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_969_);
v___x_971_ = v___x_956_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_del_object(v___x_945_);
lean_dec_ref(v___x_939_);
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
v_a_974_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_953_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_953_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
else
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
lean_del_object(v___x_945_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v___y_917_);
v___x_982_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__5));
v___x_983_ = l_Lean_Expr_constLevels_x21(v___x_939_);
lean_dec_ref(v___x_939_);
v___x_984_ = l_Lean_mkConst(v___x_982_, v___x_983_);
lean_inc_ref(v_arg_932_);
v___x_985_ = l_Lean_mkApp3(v___x_984_, v_arg_938_, v_arg_932_, v_arg_929_);
v___x_986_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_986_, 0, v_arg_932_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
lean_ctor_set_uint8(v___x_986_, sizeof(void*)*2, v___x_912_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v___x_986_);
v___x_988_ = v___x_950_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_del_object(v___x_945_);
lean_dec_ref(v___x_939_);
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
lean_dec_ref(v___y_917_);
v_a_991_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_947_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_947_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
else
{
lean_object* v_e_x27_1000_; lean_object* v_proof_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1078_; 
lean_dec_ref(v___x_939_);
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_arg_935_);
v_e_x27_1000_ = lean_ctor_get(v_a_943_, 0);
v_proof_1001_ = lean_ctor_get(v_a_943_, 1);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_a_943_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1003_ = v_a_943_;
v_isShared_1004_ = v_isSharedCheck_1078_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_proof_1001_);
lean_inc(v_e_x27_1000_);
lean_dec(v_a_943_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1078_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_917_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1069_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1008_ = v___x_1005_;
v_isShared_1009_ = v_isSharedCheck_1069_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_1005_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1069_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
uint8_t v___x_1010_; 
v___x_1010_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_x27_1000_, v_a_1006_);
lean_dec(v_a_1006_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; 
lean_del_object(v___x_1008_);
v___x_1011_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_917_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1051_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1014_ = v___x_1011_;
v_isShared_1015_ = v_isSharedCheck_1051_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1051_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
uint8_t v___x_1016_; 
v___x_1016_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_x27_1000_, v_a_1012_);
lean_dec(v_a_1012_);
if (v___x_1016_ == 0)
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
lean_del_object(v___x_1014_);
v___x_1017_ = lean_unsigned_to_nat(3u);
v___x_1018_ = l_Lean_Expr_getBoundedAppFn(v___x_1017_, v_e_913_);
lean_inc_ref(v_e_x27_1000_);
v___x_1019_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(v___x_1018_, v_e_x27_1000_, v_arg_932_, v_arg_929_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1033_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1033_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1033_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1024_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7));
v___x_1025_ = l_Lean_Expr_replaceFn(v_e_913_, v___x_1024_);
v___x_1026_ = l_Lean_mkAppB(v___x_1025_, v_e_x27_1000_, v_proof_1001_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 1, v___x_1026_);
lean_ctor_set(v___x_1003_, 0, v_a_1020_);
v___x_1028_ = v___x_1003_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1020_);
lean_ctor_set(v_reuseFailAlloc_1032_, 1, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1030_; 
lean_ctor_set_uint8(v___x_1028_, sizeof(void*)*2, v___x_941_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1028_);
v___x_1030_ = v___x_1022_;
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
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_del_object(v___x_1003_);
lean_dec_ref(v_proof_1001_);
lean_dec_ref(v_e_x27_1000_);
lean_dec_ref(v_e_913_);
v_a_1034_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1019_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1019_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1046_; 
lean_dec_ref(v_e_x27_1000_);
lean_dec_ref(v_arg_932_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
v___x_1042_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9));
v___x_1043_ = l_Lean_Expr_replaceFn(v_e_913_, v___x_1042_);
v___x_1044_ = l_Lean_Expr_app___override(v___x_1043_, v_proof_1001_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 1, v___x_1044_);
lean_ctor_set(v___x_1003_, 0, v_arg_929_);
v___x_1046_ = v___x_1003_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_arg_929_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
lean_object* v___x_1048_; 
lean_ctor_set_uint8(v___x_1046_, sizeof(void*)*2, v___x_1010_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1046_);
v___x_1048_ = v___x_1014_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_del_object(v___x_1003_);
lean_dec_ref(v_proof_1001_);
lean_dec_ref(v_e_x27_1000_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v_e_913_);
v_a_1052_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1011_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1011_);
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
else
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
lean_dec_ref(v_e_x27_1000_);
lean_dec_ref(v_arg_929_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
v___x_1060_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11));
v___x_1061_ = l_Lean_Expr_replaceFn(v_e_913_, v___x_1060_);
v___x_1062_ = l_Lean_Expr_app___override(v___x_1061_, v_proof_1001_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 1, v___x_1062_);
lean_ctor_set(v___x_1003_, 0, v_arg_932_);
v___x_1064_ = v___x_1003_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_arg_932_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
lean_object* v___x_1066_; 
lean_ctor_set_uint8(v___x_1064_, sizeof(void*)*2, v___x_912_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1064_);
v___x_1066_ = v___x_1008_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_del_object(v___x_1003_);
lean_dec_ref(v_proof_1001_);
lean_dec_ref(v_e_x27_1000_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v_e_913_);
v_a_1070_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1005_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1005_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_939_);
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v_e_913_);
return v___x_942_;
}
}
}
}
}
}
v___jp_924_:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_925_, 0, v___x_912_);
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
return v___x_926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpCond___lam__0___boxed(lean_object* v___x_1079_, lean_object* v_e_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
uint8_t v___x_14597__boxed_1091_; lean_object* v_res_1092_; 
v___x_14597__boxed_1091_ = lean_unbox(v___x_1079_);
v_res_1092_ = l_Lean_Meta_Sym_Simp_simpCond___lam__0(v___x_14597__boxed_1091_, v_e_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpCond(lean_object* v_e_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_numArgs_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v_numArgs_1104_ = l_Lean_Expr_getAppNumArgs(v_e_1093_);
v___x_1105_ = lean_unsigned_to_nat(4u);
v___x_1106_ = lean_nat_dec_lt(v_numArgs_1104_, v___x_1105_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; lean_object* v___f_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1107_ = lean_box(v___x_1106_);
v___f_1108_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpCond___lam__0___boxed), 12, 1);
lean_closure_set(v___f_1108_, 0, v___x_1107_);
v___x_1109_ = lean_nat_sub(v_numArgs_1104_, v___x_1105_);
lean_dec(v_numArgs_1104_);
v___x_1110_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_1093_, v___x_1109_, v___f_1108_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
lean_dec(v___x_1109_);
return v___x_1110_;
}
else
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
lean_dec(v_numArgs_1104_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec(v_a_1098_);
lean_dec_ref(v_a_1097_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec_ref(v_e_1093_);
v___x_1111_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1111_, 0, v___x_1106_);
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpCond___boxed(lean_object* v_e_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_Meta_Sym_Simp_simpCond(v_e_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg(lean_object* v_declName_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___x_1128_; lean_object* v_env_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1128_ = lean_st_ref_get(v___y_1126_);
v_env_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc_ref(v_env_1129_);
lean_dec(v___x_1128_);
v___x_1130_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_1129_, v_declName_1125_);
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg___boxed(lean_object* v_declName_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg(v_declName_1132_, v___y_1133_);
lean_dec(v___y_1133_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0(lean_object* v_declName_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg(v_declName_1136_, v___y_1145_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___boxed(lean_object* v_declName_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0(v_declName_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch(lean_object* v_declName_1164_, lean_object* v_e_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_){
_start:
{
lean_object* v___x_1176_; 
lean_inc(v_a_1174_);
lean_inc_ref(v_a_1173_);
lean_inc(v_a_1172_);
lean_inc_ref(v_a_1171_);
lean_inc_ref(v_e_1165_);
v___x_1176_ = l_Lean_Meta_reduceRecMatcher_x3f(v_e_1165_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
lean_dec_ref(v___x_1176_);
if (lean_obj_tag(v_a_1177_) == 1)
{
lean_object* v_val_1178_; lean_object* v___x_1179_; 
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_e_1165_);
lean_dec(v_declName_1164_);
v_val_1178_ = lean_ctor_get(v_a_1177_, 0);
lean_inc(v_val_1178_);
lean_dec_ref(v_a_1177_);
lean_inc(v_val_1178_);
v___x_1179_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_val_1178_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
lean_dec(v_a_1170_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1189_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1182_ = v___x_1179_;
v_isShared_1183_ = v_isSharedCheck_1189_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1179_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1189_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
uint8_t v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1184_ = 0;
v___x_1185_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_1185_, 0, v_val_1178_);
lean_ctor_set(v___x_1185_, 1, v_a_1180_);
lean_ctor_set_uint8(v___x_1185_, sizeof(void*)*2, v___x_1184_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1185_);
v___x_1187_ = v___x_1182_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_dec(v_val_1178_);
v_a_1190_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1179_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1179_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
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
else
{
lean_object* v___x_1198_; lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1224_; 
lean_dec(v_a_1177_);
v___x_1198_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg(v_declName_1164_, v_a_1174_);
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1224_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1224_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
if (lean_obj_tag(v_a_1199_) == 1)
{
lean_object* v_val_1203_; lean_object* v_numParams_1204_; lean_object* v_numDiscrs_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_del_object(v___x_1201_);
v_val_1203_ = lean_ctor_get(v_a_1199_, 0);
lean_inc(v_val_1203_);
lean_dec_ref(v_a_1199_);
v_numParams_1204_ = lean_ctor_get(v_val_1203_, 0);
lean_inc(v_numParams_1204_);
v_numDiscrs_1205_ = lean_ctor_get(v_val_1203_, 1);
lean_inc(v_numDiscrs_1205_);
lean_dec(v_val_1203_);
v___x_1206_ = lean_unsigned_to_nat(1u);
v___x_1207_ = lean_nat_add(v_numParams_1204_, v___x_1206_);
lean_dec(v_numParams_1204_);
v___x_1208_ = lean_nat_add(v___x_1207_, v_numDiscrs_1205_);
lean_dec(v_numDiscrs_1205_);
v___x_1209_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_e_1165_, v___x_1207_, v___x_1208_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_);
lean_dec(v___x_1208_);
lean_dec(v___x_1207_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
if (lean_obj_tag(v_a_1210_) == 1)
{
lean_dec_ref(v_a_1210_);
return v___x_1209_;
}
else
{
lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1218_; 
lean_dec(v_a_1210_);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; 
v_unused_1219_ = lean_ctor_get(v___x_1209_, 0);
lean_dec(v_unused_1219_);
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
else
{
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1214_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0));
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v___x_1214_);
v___x_1216_ = v___x_1212_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
else
{
return v___x_1209_;
}
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1222_; 
lean_dec(v_a_1199_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_e_1165_);
v___x_1220_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__1));
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1220_);
v___x_1222_ = v___x_1201_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_e_1165_);
lean_dec(v_declName_1164_);
v_a_1225_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1176_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1176_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___boxed(lean_object* v_declName_1233_, lean_object* v_e_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch(v_declName_1233_, v_e_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpControl(lean_object* v_e_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
uint8_t v___x_1257_; 
v___x_1257_ = l_Lean_Expr_isApp(v_e_1246_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
lean_dec(v_a_1255_);
lean_dec_ref(v_a_1254_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
lean_dec(v_a_1251_);
lean_dec_ref(v_a_1250_);
lean_dec(v_a_1249_);
lean_dec_ref(v_a_1248_);
lean_dec(v_a_1247_);
lean_dec_ref(v_e_1246_);
v___x_1258_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_1258_, 0, v___x_1257_);
v___x_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1258_);
return v___x_1259_;
}
else
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_Expr_getAppFn(v_e_1246_);
if (lean_obj_tag(v___x_1260_) == 4)
{
lean_object* v_declName_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v_declName_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_declName_1261_);
lean_dec_ref(v___x_1260_);
v___x_1262_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__1));
v___x_1263_ = lean_name_eq(v_declName_1261_, v___x_1262_);
if (v___x_1263_ == 0)
{
lean_object* v___x_1264_; uint8_t v___x_1265_; 
v___x_1264_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__1));
v___x_1265_ = lean_name_eq(v_declName_1261_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1266_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__1));
v___x_1267_ = lean_name_eq(v_declName_1261_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; 
v___x_1268_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch(v_declName_1261_, v_e_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
return v___x_1268_;
}
else
{
lean_object* v___x_1269_; 
lean_dec(v_declName_1261_);
v___x_1269_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte(v_e_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
return v___x_1269_;
}
}
else
{
lean_object* v___x_1270_; 
lean_dec(v_declName_1261_);
v___x_1270_ = l_Lean_Meta_Sym_Simp_simpCond(v_e_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
return v___x_1270_;
}
}
else
{
lean_object* v___x_1271_; 
lean_dec(v_declName_1261_);
v___x_1271_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte(v_e_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_);
return v___x_1271_;
}
}
else
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
lean_dec_ref(v___x_1260_);
lean_dec(v_a_1255_);
lean_dec_ref(v_a_1254_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
lean_dec(v_a_1251_);
lean_dec_ref(v_a_1250_);
lean_dec(v_a_1249_);
lean_dec_ref(v_a_1248_);
lean_dec(v_a_1247_);
lean_dec_ref(v_e_1246_);
v___x_1272_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__1));
v___x_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
return v___x_1273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpControl___boxed(lean_object* v_e_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_Meta_Sym_Simp_simpControl(v_e_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_);
return v_res_1285_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Init_Sym_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Sym_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_ControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Init_Sym_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_ControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Sym_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
}
#ifdef __cplusplus
}
#endif

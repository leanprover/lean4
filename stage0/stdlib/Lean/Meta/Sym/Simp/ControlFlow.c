// Lean compiler output
// Module: Lean.Meta.Sym.Simp.ControlFlow
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InferType import Lean.Meta.Sym.Simp.App import Lean.Meta.Sym.Simp.Result import Lean.Meta.Sym.Util import Lean.Meta.Sym.Reduce import Lean.Meta.WHNF import Lean.Meta.AppBuilder import Init.Sym.Lemmas
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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkRflResult(uint8_t, uint8_t);
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
lean_object* l_Lean_Meta_Sym_reduceMatcherApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_markAsNotDone(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "ite_eq_right_of_eq_false"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__13 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(85, 26, 223, 35, 242, 130, 83, 13)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ite_eq_left_of_eq_true"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__15 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(73, 84, 15, 184, 226, 12, 142, 9)}};
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
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "dite_eq_right_of_eq_false"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27_value),LEAN_SCALAR_PTR_LITERAL(181, 72, 248, 145, 136, 9, 228, 221)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__28 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__28_value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "dite_eq_left_of_eq_true"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29_value),LEAN_SCALAR_PTR_LITERAL(36, 253, 19, 136, 170, 78, 36, 13)}};
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
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpControl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpControl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_reduceControl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_reduceControl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(lean_object* v_f_1_, lean_object* v_a_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___y_11_; lean_object* v___x_14_; uint8_t v_debug_15_; 
v___x_14_ = lean_st_ref_get(v___y_4_);
v_debug_15_ = lean_ctor_get_uint8(v___x_14_, sizeof(void*)*12);
lean_dec(v___x_14_);
if (v_debug_15_ == 0)
{
v___y_11_ = v___y_4_;
goto v___jp_10_;
}
else
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_1_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_16_) == 0)
{
lean_object* v___x_17_; 
lean_dec_ref_known(v___x_16_, 1);
v___x_17_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_dec_ref_known(v___x_17_, 1);
v___y_11_ = v___y_4_;
goto v___jp_10_;
}
else
{
lean_object* v_a_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_25_; 
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
return v___x_13_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v_res_34_;
v_res_34_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(v_f_1_, v_a_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_);
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg___boxed(lean_object* v_f_35_, lean_object* v_a_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(v_f_35_, v_a_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
lean_dec(v___y_38_);
lean_dec_ref(v___y_37_);
return v_res_44_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1(lean_object* v_f_45_, lean_object* v_a_u2081_46_, lean_object* v_a_u2082_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(v_f_45_, v_a_u2081_46_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v_a_59_; lean_object* v___x_60_; 
v_a_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_a_59_);
lean_dec_ref_known(v___x_58_, 1);
v___x_60_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(v_a_59_, v_a_u2082_47_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
return v___x_60_;
}
else
{
lean_dec_ref(v_a_u2082_47_);
return v___x_58_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_45_ = stack[0].m_obj;
lean_object* v_a_u2081_46_ = stack[1].m_obj;
lean_object* v_a_u2082_47_ = stack[2].m_obj;
lean_object* v___y_48_ = stack[3].m_obj;
lean_object* v___y_49_ = stack[4].m_obj;
lean_object* v___y_50_ = stack[5].m_obj;
lean_object* v___y_51_ = stack[6].m_obj;
lean_object* v___y_52_ = stack[7].m_obj;
lean_object* v___y_53_ = stack[8].m_obj;
lean_object* v___y_54_ = stack[9].m_obj;
lean_object* v___y_55_ = stack[10].m_obj;
lean_object* v___y_56_ = stack[11].m_obj;
lean_object* v_res_61_;
v_res_61_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1(v_f_45_, v_a_u2081_46_, v_a_u2082_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
stack->m_obj
 = v_res_61_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1___boxed(lean_object* v_f_62_, lean_object* v_a_u2081_63_, lean_object* v_a_u2082_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1(v_f_62_, v_a_u2081_63_, v_a_u2082_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
lean_dec(v___y_69_);
lean_dec_ref(v___y_68_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
lean_dec(v___y_65_);
return v_res_75_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(lean_object* v_f_76_, lean_object* v_a_u2081_77_, lean_object* v_a_u2082_78_, lean_object* v_a_u2083_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1(v_f_76_, v_a_u2081_77_, v_a_u2082_78_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v_a_91_; lean_object* v___x_92_; 
v_a_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_a_91_);
lean_dec_ref_known(v___x_90_, 1);
v___x_92_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(v_a_91_, v_a_u2083_79_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
return v___x_92_;
}
else
{
lean_dec_ref(v_a_u2083_79_);
return v___x_90_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_76_ = stack[0].m_obj;
lean_object* v_a_u2081_77_ = stack[1].m_obj;
lean_object* v_a_u2082_78_ = stack[2].m_obj;
lean_object* v_a_u2083_79_ = stack[3].m_obj;
lean_object* v___y_80_ = stack[4].m_obj;
lean_object* v___y_81_ = stack[5].m_obj;
lean_object* v___y_82_ = stack[6].m_obj;
lean_object* v___y_83_ = stack[7].m_obj;
lean_object* v___y_84_ = stack[8].m_obj;
lean_object* v___y_85_ = stack[9].m_obj;
lean_object* v___y_86_ = stack[10].m_obj;
lean_object* v___y_87_ = stack[11].m_obj;
lean_object* v___y_88_ = stack[12].m_obj;
lean_object* v_res_93_;
v_res_93_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(v_f_76_, v_a_u2081_77_, v_a_u2082_78_, v_a_u2083_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
stack->m_obj
 = v_res_93_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0___boxed(lean_object* v_f_94_, lean_object* v_a_u2081_95_, lean_object* v_a_u2082_96_, lean_object* v_a_u2083_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(v_f_94_, v_a_u2081_95_, v_a_u2082_96_, v_a_u2083_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
return v_res_108_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(lean_object* v_f_109_, lean_object* v_a_u2081_110_, lean_object* v_a_u2082_111_, lean_object* v_a_u2083_112_, lean_object* v_a_u2084_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(v_f_109_, v_a_u2081_110_, v_a_u2082_111_, v_a_u2083_112_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_126_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_a_125_);
lean_dec_ref_known(v___x_124_, 1);
v___x_126_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(v_a_125_, v_a_u2084_113_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
return v___x_126_;
}
else
{
lean_dec_ref(v_a_u2084_113_);
return v___x_124_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_109_ = stack[0].m_obj;
lean_object* v_a_u2081_110_ = stack[1].m_obj;
lean_object* v_a_u2082_111_ = stack[2].m_obj;
lean_object* v_a_u2083_112_ = stack[3].m_obj;
lean_object* v_a_u2084_113_ = stack[4].m_obj;
lean_object* v___y_114_ = stack[5].m_obj;
lean_object* v___y_115_ = stack[6].m_obj;
lean_object* v___y_116_ = stack[7].m_obj;
lean_object* v___y_117_ = stack[8].m_obj;
lean_object* v___y_118_ = stack[9].m_obj;
lean_object* v___y_119_ = stack[10].m_obj;
lean_object* v___y_120_ = stack[11].m_obj;
lean_object* v___y_121_ = stack[12].m_obj;
lean_object* v___y_122_ = stack[13].m_obj;
lean_object* v_res_127_;
v_res_127_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(v_f_109_, v_a_u2081_110_, v_a_u2082_111_, v_a_u2083_112_, v_a_u2084_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
stack->m_obj
 = v_res_127_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0___boxed(lean_object* v_f_128_, lean_object* v_a_u2081_129_, lean_object* v_a_u2082_130_, lean_object* v_a_u2083_131_, lean_object* v_a_u2084_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(v_f_128_, v_a_u2081_129_, v_a_u2082_130_, v_a_u2083_131_, v_a_u2084_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
return v_res_143_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_box(0);
v___x_157_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__7));
v___x_158_ = l_Lean_mkConst(v___x_157_, v___x_156_);
return v___x_158_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0(uint8_t v___x_172_, lean_object* v_e_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v___x_187_; uint8_t v___x_188_; 
lean_inc_ref(v_e_173_);
v___x_187_ = l_Lean_Expr_cleanupAnnotations(v_e_173_);
v___x_188_ = l_Lean_Expr_isApp(v___x_187_);
if (v___x_188_ == 0)
{
lean_dec_ref(v___x_187_);
lean_dec_ref(v_e_173_);
goto v___jp_184_;
}
else
{
lean_object* v_arg_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v_arg_189_ = lean_ctor_get(v___x_187_, 1);
lean_inc_ref(v_arg_189_);
v___x_190_ = l_Lean_Expr_appFnCleanup___redArg(v___x_187_);
v___x_191_ = l_Lean_Expr_isApp(v___x_190_);
if (v___x_191_ == 0)
{
lean_dec_ref(v___x_190_);
lean_dec_ref(v_arg_189_);
lean_dec_ref(v_e_173_);
goto v___jp_184_;
}
else
{
lean_object* v_arg_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_arg_192_ = lean_ctor_get(v___x_190_, 1);
lean_inc_ref(v_arg_192_);
v___x_193_ = l_Lean_Expr_appFnCleanup___redArg(v___x_190_);
v___x_194_ = l_Lean_Expr_isApp(v___x_193_);
if (v___x_194_ == 0)
{
lean_dec_ref(v___x_193_);
lean_dec_ref(v_arg_192_);
lean_dec_ref(v_arg_189_);
lean_dec_ref(v_e_173_);
goto v___jp_184_;
}
else
{
lean_object* v_arg_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v_arg_195_ = lean_ctor_get(v___x_193_, 1);
lean_inc_ref(v_arg_195_);
v___x_196_ = l_Lean_Expr_appFnCleanup___redArg(v___x_193_);
v___x_197_ = l_Lean_Expr_isApp(v___x_196_);
if (v___x_197_ == 0)
{
lean_dec_ref(v___x_196_);
lean_dec_ref(v_arg_195_);
lean_dec_ref(v_arg_192_);
lean_dec_ref(v_arg_189_);
lean_dec_ref(v_e_173_);
goto v___jp_184_;
}
else
{
lean_object* v_arg_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_arg_198_ = lean_ctor_get(v___x_196_, 1);
lean_inc_ref(v_arg_198_);
v___x_199_ = l_Lean_Expr_appFnCleanup___redArg(v___x_196_);
v___x_200_ = l_Lean_Expr_isApp(v___x_199_);
if (v___x_200_ == 0)
{
lean_dec_ref(v___x_199_);
lean_dec_ref(v_arg_198_);
lean_dec_ref(v_arg_195_);
lean_dec_ref(v_arg_192_);
lean_dec_ref(v_arg_189_);
lean_dec_ref(v_e_173_);
goto v___jp_184_;
}
else
{
lean_object* v_arg_201_; lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v_arg_201_ = lean_ctor_get(v___x_199_, 1);
lean_inc_ref(v_arg_201_);
v___x_202_ = l_Lean_Expr_appFnCleanup___redArg(v___x_199_);
v___x_203_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__1));
v___x_204_ = l_Lean_Expr_isConstOf(v___x_202_, v___x_203_);
if (v___x_204_ == 0)
{
lean_dec_ref(v___x_202_);
lean_dec_ref(v_arg_201_);
lean_dec_ref(v_arg_198_);
lean_dec_ref(v_arg_195_);
lean_dec_ref(v_arg_192_);
lean_dec_ref(v_arg_189_);
lean_dec_ref(v_e_173_);
goto v___jp_184_;
}
else
{
lean_object* v___x_205_; 
lean_inc(v___y_182_);
lean_inc_ref(v___y_181_);
lean_inc(v___y_180_);
lean_inc_ref(v___y_179_);
lean_inc(v___y_178_);
lean_inc_ref(v___y_177_);
lean_inc(v___y_176_);
lean_inc_ref(v___y_175_);
lean_inc(v___y_174_);
lean_inc_ref(v_arg_198_);
v___x_205_ = lean_sym_simp(v_arg_198_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_a_206_);
lean_dec_ref_known(v___x_205_, 1);
if (lean_obj_tag(v_a_206_) == 0)
{
uint8_t v_contextDependent_207_; lean_object* v___x_208_; 
lean_dec_ref(v_e_173_);
v_contextDependent_207_ = lean_ctor_get_uint8(v_a_206_, 1);
lean_dec_ref_known(v_a_206_, 0);
v___x_208_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_198_, v___y_177_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_250_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_250_ == 0)
{
v___x_211_ = v___x_208_;
v_isShared_212_ = v_isSharedCheck_250_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_208_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_250_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
uint8_t v___x_213_; 
v___x_213_ = lean_unbox(v_a_209_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; 
lean_del_object(v___x_211_);
v___x_214_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_198_, v___y_177_);
lean_dec_ref(v_arg_198_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_233_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_233_ == 0)
{
v___x_217_ = v___x_214_;
v_isShared_218_ = v_isSharedCheck_233_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_214_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_233_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
uint8_t v___x_219_; 
v___x_219_ = lean_unbox(v_a_215_);
lean_dec(v_a_215_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; lean_object* v___x_222_; 
lean_dec(v_a_209_);
lean_dec_ref(v___x_202_);
lean_dec_ref(v_arg_201_);
lean_dec_ref(v_arg_195_);
lean_dec_ref(v_arg_192_);
lean_dec_ref(v_arg_189_);
v___x_220_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_204_, v_contextDependent_207_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_220_);
v___x_222_ = v___x_217_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
else
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; lean_object* v___x_231_; 
v___x_224_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__3));
v___x_225_ = l_Lean_Expr_constLevels_x21(v___x_202_);
lean_dec_ref(v___x_202_);
v___x_226_ = l_Lean_mkConst(v___x_224_, v___x_225_);
lean_inc_ref(v_arg_189_);
v___x_227_ = l_Lean_mkApp4(v___x_226_, v_arg_201_, v_arg_195_, v_arg_192_, v_arg_189_);
v___x_228_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_228_, 0, v_arg_189_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = lean_unbox(v_a_209_);
lean_dec(v_a_209_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*2, v___x_229_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*2 + 1, v_contextDependent_207_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_228_);
v___x_231_ = v___x_217_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_228_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_dec(v_a_209_);
lean_dec_ref(v___x_202_);
lean_dec_ref(v_arg_201_);
lean_dec_ref(v_arg_195_);
lean_dec_ref(v_arg_192_);
lean_dec_ref(v_arg_189_);
v_a_234_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_214_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_214_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
lean_dec(v_a_209_);
lean_dec_ref(v_arg_198_);
v___x_242_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__5));
v___x_243_ = l_Lean_Expr_constLevels_x21(v___x_202_);
lean_dec_ref(v___x_202_);
v___x_244_ = l_Lean_mkConst(v___x_242_, v___x_243_);
lean_inc_ref(v_arg_192_);
v___x_245_ = l_Lean_mkApp4(v___x_244_, v_arg_201_, v_arg_195_, v_arg_192_, v_arg_189_);
v___x_246_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_246_, 0, v_arg_192_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*2, v___x_172_);
lean_ctor_set_uint8(v___x_246_, sizeof(void*)*2 + 1, v_contextDependent_207_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_246_);
v___x_248_ = v___x_211_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
lean_dec_ref(v___x_202_);
lean_dec_ref(v_arg_201_);
lean_dec_ref(v_arg_198_);
lean_dec_ref(v_arg_195_);
lean_dec_ref(v_arg_192_);
lean_dec_ref(v_arg_189_);
v_a_251_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_208_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_208_);
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
else
{
lean_object* v_e_x27_259_; lean_object* v_proof_260_; uint8_t v_contextDependent_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_373_; 
lean_dec_ref(v___x_202_);
lean_dec_ref(v_arg_201_);
lean_dec_ref(v_arg_198_);
lean_dec_ref(v_arg_195_);
v_e_x27_259_ = lean_ctor_get(v_a_206_, 0);
v_proof_260_ = lean_ctor_get(v_a_206_, 1);
v_contextDependent_261_ = lean_ctor_get_uint8(v_a_206_, sizeof(void*)*2 + 1);
v_isSharedCheck_373_ = !lean_is_exclusive(v_a_206_);
if (v_isSharedCheck_373_ == 0)
{
v___x_263_ = v_a_206_;
v_isShared_264_ = v_isSharedCheck_373_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_proof_260_);
lean_inc(v_e_x27_259_);
lean_dec(v_a_206_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_373_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; 
v___x_265_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_259_, v___y_177_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_364_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_364_ == 0)
{
v___x_268_ = v___x_265_;
v_isShared_269_ = v_isSharedCheck_364_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_265_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_364_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
uint8_t v___x_270_; 
v___x_270_ = lean_unbox(v_a_266_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
lean_del_object(v___x_268_);
v___x_271_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_259_, v___y_177_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_346_; 
v_a_272_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_346_ == 0)
{
v___x_274_ = v___x_271_;
v_isShared_275_ = v_isSharedCheck_346_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_271_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_346_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
uint8_t v___x_276_; 
v___x_276_ = lean_unbox(v_a_272_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
lean_del_object(v___x_274_);
lean_dec(v_a_266_);
v___x_277_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8, &l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8_once, _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8);
lean_inc_ref(v_e_x27_259_);
v___x_278_ = l_Lean_Expr_app___override(v___x_277_, v_e_x27_259_);
v___x_279_ = lean_box(0);
v___x_280_ = l_Lean_Meta_trySynthInstance(v___x_278_, v___x_279_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_327_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_327_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_327_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_327_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
if (lean_obj_tag(v_a_281_) == 1)
{
lean_object* v_a_285_; lean_object* v___x_286_; 
lean_del_object(v___x_283_);
lean_dec(v_a_272_);
v_a_285_ = lean_ctor_get(v_a_281_, 0);
lean_inc(v_a_285_);
lean_dec_ref_known(v_a_281_, 1);
v___x_286_ = l_Lean_Meta_Sym_shareCommon(v_a_285_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc_n(v_a_287_, 2);
lean_dec_ref_known(v___x_286_, 1);
v___x_288_ = lean_unsigned_to_nat(4u);
v___x_289_ = l_Lean_Expr_getBoundedAppFn(v___x_288_, v_e_173_);
lean_inc_ref(v_e_x27_259_);
v___x_290_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(v___x_289_, v_e_x27_259_, v_a_287_, v_arg_192_, v_arg_189_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_304_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_304_ == 0)
{
v___x_293_ = v___x_290_;
v_isShared_294_ = v_isSharedCheck_304_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_290_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_304_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_295_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12));
v___x_296_ = l_Lean_Expr_replaceFn(v_e_173_, v___x_295_);
v___x_297_ = l_Lean_mkApp3(v___x_296_, v_e_x27_259_, v_a_287_, v_proof_260_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v___x_297_);
lean_ctor_set(v___x_263_, 0, v_a_291_);
v___x_299_ = v___x_263_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_291_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v___x_297_);
lean_ctor_set_uint8(v_reuseFailAlloc_303_, sizeof(void*)*2 + 1, v_contextDependent_261_);
v___x_299_ = v_reuseFailAlloc_303_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
lean_object* v___x_301_; 
lean_ctor_set_uint8(v___x_299_, sizeof(void*)*2, v___x_204_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_299_);
v___x_301_ = v___x_293_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
else
{
lean_object* v_a_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_312_; 
lean_dec(v_a_287_);
lean_del_object(v___x_263_);
lean_dec_ref(v_proof_260_);
lean_dec_ref(v_e_x27_259_);
lean_dec_ref(v_e_173_);
v_a_305_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_312_ == 0)
{
v___x_307_ = v___x_290_;
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_a_305_);
lean_dec(v___x_290_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_312_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_310_; 
if (v_isShared_308_ == 0)
{
v___x_310_ = v___x_307_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_a_305_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_320_; 
lean_del_object(v___x_263_);
lean_dec_ref(v_proof_260_);
lean_dec_ref(v_e_x27_259_);
lean_dec_ref(v_arg_192_);
lean_dec_ref(v_arg_189_);
lean_dec_ref(v_e_173_);
v_a_313_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_320_ == 0)
{
v___x_315_ = v___x_286_;
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_286_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_320_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
}
}
else
{
lean_object* v___x_321_; uint8_t v___x_322_; uint8_t v___x_323_; lean_object* v___x_325_; 
lean_dec(v_a_281_);
lean_del_object(v___x_263_);
lean_dec_ref(v_proof_260_);
lean_dec_ref(v_e_x27_259_);
lean_dec_ref(v_arg_192_);
lean_dec_ref(v_arg_189_);
lean_dec_ref(v_e_173_);
v___x_321_ = lean_alloc_ctor(0, 0, 2);
v___x_322_ = lean_unbox(v_a_272_);
lean_ctor_set_uint8(v___x_321_, 0, v___x_322_);
v___x_323_ = lean_unbox(v_a_272_);
lean_dec(v_a_272_);
lean_ctor_set_uint8(v___x_321_, 1, v___x_323_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_321_);
v___x_325_ = v___x_283_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v___x_321_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_dec(v_a_272_);
lean_del_object(v___x_263_);
lean_dec_ref(v_proof_260_);
lean_dec_ref(v_e_x27_259_);
lean_dec_ref(v_arg_192_);
lean_dec_ref(v_arg_189_);
lean_dec_ref(v_e_173_);
v_a_328_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_280_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_280_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_340_; 
lean_dec(v_a_272_);
lean_dec_ref(v_e_x27_259_);
lean_dec_ref(v_arg_192_);
v___x_336_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__14));
v___x_337_ = l_Lean_Expr_replaceFn(v_e_173_, v___x_336_);
v___x_338_ = l_Lean_Expr_app___override(v___x_337_, v_proof_260_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v___x_338_);
lean_ctor_set(v___x_263_, 0, v_arg_189_);
v___x_340_ = v___x_263_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_arg_189_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v___x_338_);
v___x_340_ = v_reuseFailAlloc_345_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
uint8_t v___x_341_; lean_object* v___x_343_; 
v___x_341_ = lean_unbox(v_a_266_);
lean_dec(v_a_266_);
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*2, v___x_341_);
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*2 + 1, v_contextDependent_261_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v___x_340_);
v___x_343_ = v___x_274_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_340_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec(v_a_266_);
lean_del_object(v___x_263_);
lean_dec_ref(v_proof_260_);
lean_dec_ref(v_e_x27_259_);
lean_dec_ref(v_arg_192_);
lean_dec_ref(v_arg_189_);
lean_dec_ref(v_e_173_);
v_a_347_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_271_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_271_);
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
else
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_359_; 
lean_dec(v_a_266_);
lean_dec_ref(v_e_x27_259_);
lean_dec_ref(v_arg_189_);
v___x_355_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__16));
v___x_356_ = l_Lean_Expr_replaceFn(v_e_173_, v___x_355_);
v___x_357_ = l_Lean_Expr_app___override(v___x_356_, v_proof_260_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v___x_357_);
lean_ctor_set(v___x_263_, 0, v_arg_192_);
v___x_359_ = v___x_263_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_arg_192_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v___x_357_);
lean_ctor_set_uint8(v_reuseFailAlloc_363_, sizeof(void*)*2 + 1, v_contextDependent_261_);
v___x_359_ = v_reuseFailAlloc_363_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_361_; 
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*2, v___x_172_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_359_);
v___x_361_ = v___x_268_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
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
else
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
lean_del_object(v___x_263_);
lean_dec_ref(v_proof_260_);
lean_dec_ref(v_e_x27_259_);
lean_dec_ref(v_arg_192_);
lean_dec_ref(v_arg_189_);
lean_dec_ref(v_e_173_);
v_a_365_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___x_265_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_265_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_365_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_202_);
lean_dec_ref(v_arg_201_);
lean_dec_ref(v_arg_198_);
lean_dec_ref(v_arg_195_);
lean_dec_ref(v_arg_192_);
lean_dec_ref(v_arg_189_);
lean_dec_ref(v_e_173_);
return v___x_205_;
}
}
}
}
}
}
}
v___jp_184_:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_185_, 0, v___x_172_);
lean_ctor_set_uint8(v___x_185_, 1, v___x_172_);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_172_ = stack[0].m_num;
lean_object* v_e_173_ = stack[1].m_obj;
lean_object* v___y_174_ = stack[2].m_obj;
lean_object* v___y_175_ = stack[3].m_obj;
lean_object* v___y_176_ = stack[4].m_obj;
lean_object* v___y_177_ = stack[5].m_obj;
lean_object* v___y_178_ = stack[6].m_obj;
lean_object* v___y_179_ = stack[7].m_obj;
lean_object* v___y_180_ = stack[8].m_obj;
lean_object* v___y_181_ = stack[9].m_obj;
lean_object* v___y_182_ = stack[10].m_obj;
lean_object* v_res_374_;
v_res_374_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0(v___x_172_, v_e_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
stack->m_obj
 = v_res_374_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___boxed(lean_object* v___x_375_, lean_object* v_e_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
uint8_t v___x_17248__boxed_387_; lean_object* v_res_388_; 
v___x_17248__boxed_387_ = lean_unbox(v___x_375_);
v_res_388_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0(v___x_17248__boxed_387_, v_e_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
return v_res_388_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte(lean_object* v_e_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_numArgs_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v_numArgs_400_ = l_Lean_Expr_getAppNumArgs(v_e_389_);
v___x_401_ = lean_unsigned_to_nat(5u);
v___x_402_ = lean_nat_dec_lt(v_numArgs_400_, v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___f_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_403_ = lean_box(v___x_402_);
v___f_404_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___boxed), 12, 1);
lean_closure_set(v___f_404_, 0, v___x_403_);
v___x_405_ = lean_nat_sub(v_numArgs_400_, v___x_401_);
lean_dec(v_numArgs_400_);
v___x_406_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_389_, v___x_405_, v___f_404_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
lean_dec(v___x_405_);
return v___x_406_;
}
else
{
uint8_t v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec(v_numArgs_400_);
lean_dec_ref(v_e_389_);
v___x_407_ = 0;
v___x_408_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_408_, 0, v___x_402_);
lean_ctor_set_uint8(v___x_408_, 1, v___x_407_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_389_ = stack[0].m_obj;
lean_object* v_a_390_ = stack[1].m_obj;
lean_object* v_a_391_ = stack[2].m_obj;
lean_object* v_a_392_ = stack[3].m_obj;
lean_object* v_a_393_ = stack[4].m_obj;
lean_object* v_a_394_ = stack[5].m_obj;
lean_object* v_a_395_ = stack[6].m_obj;
lean_object* v_a_396_ = stack[7].m_obj;
lean_object* v_a_397_ = stack[8].m_obj;
lean_object* v_a_398_ = stack[9].m_obj;
lean_object* v_res_410_;
v_res_410_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte(v_e_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
stack->m_obj
 = v_res_410_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___boxed(lean_object* v_e_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte(v_e_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
return v_res_422_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1(lean_object* v_f_423_, lean_object* v_a_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(v_f_423_, v_a_424_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
return v___x_435_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_423_ = stack[0].m_obj;
lean_object* v_a_424_ = stack[1].m_obj;
lean_object* v___y_425_ = stack[2].m_obj;
lean_object* v___y_426_ = stack[3].m_obj;
lean_object* v___y_427_ = stack[4].m_obj;
lean_object* v___y_428_ = stack[5].m_obj;
lean_object* v___y_429_ = stack[6].m_obj;
lean_object* v___y_430_ = stack[7].m_obj;
lean_object* v___y_431_ = stack[8].m_obj;
lean_object* v___y_432_ = stack[9].m_obj;
lean_object* v___y_433_ = stack[10].m_obj;
lean_object* v_res_436_;
v_res_436_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1(v_f_423_, v_a_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
stack->m_obj
 = v_res_436_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___boxed(lean_object* v_f_437_, lean_object* v_a_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1(v_f_437_, v_a_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
return v_res_449_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = lean_box(0);
v___x_457_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__3));
v___x_458_ = l_Lean_mkConst(v___x_457_, v___x_456_);
return v___x_458_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_459_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4, &l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4_once, _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4);
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = lean_mk_empty_array_with_capacity(v___x_460_);
v___x_462_ = lean_array_push(v___x_461_, v___x_459_);
return v___x_462_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = lean_box(0);
v___x_472_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__10));
v___x_473_ = l_Lean_mkConst(v___x_472_, v___x_471_);
return v___x_473_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_474_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11, &l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11_once, _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11);
v___x_475_ = lean_unsigned_to_nat(1u);
v___x_476_ = lean_mk_empty_array_with_capacity(v___x_475_);
v___x_477_ = lean_array_push(v___x_476_, v___x_474_);
return v___x_477_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_box(0);
v___x_490_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__19));
v___x_491_ = l_Lean_mkConst(v___x_490_, v___x_489_);
return v___x_491_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_unsigned_to_nat(0u);
v___x_493_ = l_Lean_mkBVar(v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_498_ = lean_box(0);
v___x_499_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__23));
v___x_500_ = l_Lean_mkConst(v___x_499_, v___x_498_);
return v___x_500_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0(uint8_t v___x_512_, lean_object* v_e_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v___x_527_; uint8_t v___x_528_; 
lean_inc_ref(v_e_513_);
v___x_527_ = l_Lean_Expr_cleanupAnnotations(v_e_513_);
v___x_528_ = l_Lean_Expr_isApp(v___x_527_);
if (v___x_528_ == 0)
{
lean_dec_ref(v___x_527_);
lean_dec_ref(v_e_513_);
goto v___jp_524_;
}
else
{
lean_object* v_arg_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_arg_529_ = lean_ctor_get(v___x_527_, 1);
lean_inc_ref(v_arg_529_);
v___x_530_ = l_Lean_Expr_appFnCleanup___redArg(v___x_527_);
v___x_531_ = l_Lean_Expr_isApp(v___x_530_);
if (v___x_531_ == 0)
{
lean_dec_ref(v___x_530_);
lean_dec_ref(v_arg_529_);
lean_dec_ref(v_e_513_);
goto v___jp_524_;
}
else
{
lean_object* v_arg_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v_arg_532_ = lean_ctor_get(v___x_530_, 1);
lean_inc_ref(v_arg_532_);
v___x_533_ = l_Lean_Expr_appFnCleanup___redArg(v___x_530_);
v___x_534_ = l_Lean_Expr_isApp(v___x_533_);
if (v___x_534_ == 0)
{
lean_dec_ref(v___x_533_);
lean_dec_ref(v_arg_532_);
lean_dec_ref(v_arg_529_);
lean_dec_ref(v_e_513_);
goto v___jp_524_;
}
else
{
lean_object* v_arg_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v_arg_535_ = lean_ctor_get(v___x_533_, 1);
lean_inc_ref(v_arg_535_);
v___x_536_ = l_Lean_Expr_appFnCleanup___redArg(v___x_533_);
v___x_537_ = l_Lean_Expr_isApp(v___x_536_);
if (v___x_537_ == 0)
{
lean_dec_ref(v___x_536_);
lean_dec_ref(v_arg_535_);
lean_dec_ref(v_arg_532_);
lean_dec_ref(v_arg_529_);
lean_dec_ref(v_e_513_);
goto v___jp_524_;
}
else
{
lean_object* v_arg_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v_arg_538_ = lean_ctor_get(v___x_536_, 1);
lean_inc_ref(v_arg_538_);
v___x_539_ = l_Lean_Expr_appFnCleanup___redArg(v___x_536_);
v___x_540_ = l_Lean_Expr_isApp(v___x_539_);
if (v___x_540_ == 0)
{
lean_dec_ref(v___x_539_);
lean_dec_ref(v_arg_538_);
lean_dec_ref(v_arg_535_);
lean_dec_ref(v_arg_532_);
lean_dec_ref(v_arg_529_);
lean_dec_ref(v_e_513_);
goto v___jp_524_;
}
else
{
lean_object* v_arg_541_; lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v_arg_541_ = lean_ctor_get(v___x_539_, 1);
lean_inc_ref(v_arg_541_);
v___x_542_ = l_Lean_Expr_appFnCleanup___redArg(v___x_539_);
v___x_543_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__1));
v___x_544_ = l_Lean_Expr_isConstOf(v___x_542_, v___x_543_);
if (v___x_544_ == 0)
{
lean_dec_ref(v___x_542_);
lean_dec_ref(v_arg_541_);
lean_dec_ref(v_arg_538_);
lean_dec_ref(v_arg_535_);
lean_dec_ref(v_arg_532_);
lean_dec_ref(v_arg_529_);
lean_dec_ref(v_e_513_);
goto v___jp_524_;
}
else
{
lean_object* v___x_545_; 
lean_inc(v___y_522_);
lean_inc_ref(v___y_521_);
lean_inc(v___y_520_);
lean_inc_ref(v___y_519_);
lean_inc(v___y_518_);
lean_inc_ref(v___y_517_);
lean_inc(v___y_516_);
lean_inc_ref(v___y_515_);
lean_inc(v___y_514_);
lean_inc_ref(v_arg_538_);
v___x_545_ = lean_sym_simp(v_arg_538_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref_known(v___x_545_, 1);
if (lean_obj_tag(v_a_546_) == 0)
{
uint8_t v_contextDependent_547_; lean_object* v___x_548_; 
lean_dec_ref(v_e_513_);
v_contextDependent_547_ = lean_ctor_get_uint8(v_a_546_, 1);
lean_dec_ref_known(v_a_546_, 0);
v___x_548_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_538_, v___y_517_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; uint8_t v___x_550_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_548_, 1);
v___x_550_ = lean_unbox(v_a_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
v___x_551_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_538_, v___y_517_);
lean_dec_ref(v_arg_538_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_588_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_588_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_588_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_588_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
uint8_t v___x_556_; 
v___x_556_ = lean_unbox(v_a_552_);
lean_dec(v_a_552_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_559_; 
lean_dec(v_a_549_);
lean_dec_ref(v___x_542_);
lean_dec_ref(v_arg_541_);
lean_dec_ref(v_arg_535_);
lean_dec_ref(v_arg_532_);
lean_dec_ref(v_arg_529_);
v___x_557_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_544_, v_contextDependent_547_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_557_);
v___x_559_ = v___x_554_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
else
{
lean_object* v___x_561_; uint8_t v___x_562_; uint8_t v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
lean_del_object(v___x_554_);
v___x_561_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5, &l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5_once, _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5);
v___x_562_ = lean_unbox(v_a_549_);
v___x_563_ = lean_unbox(v_a_549_);
lean_inc_ref(v_arg_529_);
v___x_564_ = l_Lean_Expr_betaRev(v_arg_529_, v___x_561_, v___x_562_, v___x_563_);
v___x_565_ = l_Lean_Meta_Sym_shareCommonInc(v___x_564_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_579_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_579_ == 0)
{
v___x_568_ = v___x_565_;
v_isShared_569_ = v_isSharedCheck_579_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_565_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_579_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; lean_object* v___x_577_; 
v___x_570_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__7));
v___x_571_ = l_Lean_Expr_constLevels_x21(v___x_542_);
lean_dec_ref(v___x_542_);
v___x_572_ = l_Lean_mkConst(v___x_570_, v___x_571_);
v___x_573_ = l_Lean_mkApp4(v___x_572_, v_arg_541_, v_arg_535_, v_arg_532_, v_arg_529_);
v___x_574_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_574_, 0, v_a_566_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = lean_unbox(v_a_549_);
lean_dec(v_a_549_);
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*2, v___x_575_);
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*2 + 1, v_contextDependent_547_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 0, v___x_574_);
v___x_577_ = v___x_568_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_574_);
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
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec(v_a_549_);
lean_dec_ref(v___x_542_);
lean_dec_ref(v_arg_541_);
lean_dec_ref(v_arg_535_);
lean_dec_ref(v_arg_532_);
lean_dec_ref(v_arg_529_);
v_a_580_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_565_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_565_);
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
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec(v_a_549_);
lean_dec_ref(v___x_542_);
lean_dec_ref(v_arg_541_);
lean_dec_ref(v_arg_535_);
lean_dec_ref(v_arg_532_);
lean_dec_ref(v_arg_529_);
v_a_589_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_551_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_551_);
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
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v_a_549_);
lean_dec_ref(v_arg_538_);
v___x_597_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12, &l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12_once, _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12);
lean_inc_ref(v_arg_532_);
v___x_598_ = l_Lean_Expr_betaRev(v_arg_532_, v___x_597_, v___x_512_, v___x_512_);
v___x_599_ = l_Lean_Meta_Sym_shareCommonInc(v___x_598_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_612_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_612_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_612_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_612_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_604_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__14));
v___x_605_ = l_Lean_Expr_constLevels_x21(v___x_542_);
lean_dec_ref(v___x_542_);
v___x_606_ = l_Lean_mkConst(v___x_604_, v___x_605_);
v___x_607_ = l_Lean_mkApp4(v___x_606_, v_arg_541_, v_arg_535_, v_arg_532_, v_arg_529_);
v___x_608_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_608_, 0, v_a_600_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
lean_ctor_set_uint8(v___x_608_, sizeof(void*)*2, v___x_512_);
lean_ctor_set_uint8(v___x_608_, sizeof(void*)*2 + 1, v_contextDependent_547_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_608_);
v___x_610_ = v___x_602_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
else
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_dec_ref(v___x_542_);
lean_dec_ref(v_arg_541_);
lean_dec_ref(v_arg_535_);
lean_dec_ref(v_arg_532_);
lean_dec_ref(v_arg_529_);
v_a_613_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_599_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_599_);
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
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec_ref(v___x_542_);
lean_dec_ref(v_arg_541_);
lean_dec_ref(v_arg_538_);
lean_dec_ref(v_arg_535_);
lean_dec_ref(v_arg_532_);
lean_dec_ref(v_arg_529_);
v_a_621_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_548_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_548_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
else
{
lean_object* v_e_x27_629_; lean_object* v_proof_630_; uint8_t v_contextDependent_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_845_; 
lean_dec_ref(v___x_542_);
lean_dec_ref(v_arg_541_);
lean_dec_ref(v_arg_535_);
v_e_x27_629_ = lean_ctor_get(v_a_546_, 0);
v_proof_630_ = lean_ctor_get(v_a_546_, 1);
v_contextDependent_631_ = lean_ctor_get_uint8(v_a_546_, sizeof(void*)*2 + 1);
v_isSharedCheck_845_ = !lean_is_exclusive(v_a_546_);
if (v_isSharedCheck_845_ == 0)
{
v___x_633_ = v_a_546_;
v_isShared_634_ = v_isSharedCheck_845_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_proof_630_);
lean_inc(v_e_x27_629_);
lean_dec(v_a_546_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_845_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_629_, v___y_517_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; uint8_t v___x_637_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_635_, 1);
v___x_637_ = lean_unbox(v_a_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; 
v___x_638_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_629_, v___y_517_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; uint8_t v___x_640_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v___x_638_, 1);
v___x_640_ = lean_unbox(v_a_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
lean_dec(v_a_636_);
v___x_641_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8, &l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8_once, _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8);
lean_inc_ref(v_e_x27_629_);
v___x_642_ = l_Lean_Expr_app___override(v___x_641_, v_e_x27_629_);
v___x_643_ = lean_box(0);
v___x_644_ = l_Lean_Meta_trySynthInstance(v___x_642_, v___x_643_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_741_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_741_ == 0)
{
v___x_647_ = v___x_644_;
v_isShared_648_ = v_isSharedCheck_741_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_741_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
if (lean_obj_tag(v_a_645_) == 1)
{
lean_object* v_a_649_; lean_object* v___x_650_; 
lean_del_object(v___x_647_);
v_a_649_ = lean_ctor_get(v_a_645_, 0);
lean_inc(v_a_649_);
lean_dec_ref_known(v_a_645_, 1);
v___x_650_ = l_Lean_Meta_Sym_shareCommon(v_a_649_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
v___x_652_ = lean_unsigned_to_nat(4u);
v___x_653_ = l_Lean_Expr_getBoundedAppFn(v___x_652_, v_e_513_);
v___x_654_ = l_Lean_Meta_Sym_shareCommon(v_proof_630_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_656_; uint8_t v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; uint8_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc_n(v_a_655_, 2);
lean_dec_ref_known(v___x_654_, 1);
v___x_656_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__16));
v___x_657_ = 0;
v___x_658_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20, &l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20_once, _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20);
v___x_659_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21, &l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21_once, _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21);
lean_inc_ref_n(v_e_x27_629_, 2);
lean_inc_ref(v_arg_538_);
v___x_660_ = l_Lean_mkApp4(v___x_658_, v_arg_538_, v_e_x27_629_, v_a_655_, v___x_659_);
v___x_661_ = lean_unsigned_to_nat(1u);
v___x_662_ = lean_mk_empty_array_with_capacity(v___x_661_);
lean_inc_ref(v___x_662_);
v___x_663_ = lean_array_push(v___x_662_, v___x_660_);
v___x_664_ = lean_unbox(v_a_639_);
v___x_665_ = lean_unbox(v_a_639_);
v___x_666_ = l_Lean_Expr_betaRev(v_arg_532_, v___x_663_, v___x_664_, v___x_665_);
lean_dec_ref(v___x_663_);
v___x_667_ = l_Lean_mkLambda(v___x_656_, v___x_657_, v_e_x27_629_, v___x_666_);
v___x_668_ = l_Lean_Meta_Sym_shareCommonInc(v___x_667_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; uint8_t v___x_674_; uint8_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
lean_inc_ref_n(v_e_x27_629_, 2);
v___x_670_ = l_Lean_mkNot(v_e_x27_629_);
v___x_671_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24, &l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24_once, _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24);
lean_inc(v_a_655_);
v___x_672_ = l_Lean_mkApp4(v___x_671_, v_arg_538_, v_e_x27_629_, v_a_655_, v___x_659_);
v___x_673_ = lean_array_push(v___x_662_, v___x_672_);
v___x_674_ = lean_unbox(v_a_639_);
v___x_675_ = lean_unbox(v_a_639_);
lean_dec(v_a_639_);
v___x_676_ = l_Lean_Expr_betaRev(v_arg_529_, v___x_673_, v___x_674_, v___x_675_);
lean_dec_ref(v___x_673_);
v___x_677_ = l_Lean_mkLambda(v___x_656_, v___x_657_, v___x_670_, v___x_676_);
v___x_678_ = l_Lean_Meta_Sym_shareCommonInc(v___x_677_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_680_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_a_679_);
lean_dec_ref_known(v___x_678_, 1);
lean_inc(v_a_651_);
lean_inc_ref(v_e_x27_629_);
v___x_680_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(v___x_653_, v_e_x27_629_, v_a_651_, v_a_669_, v_a_679_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_694_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_694_ == 0)
{
v___x_683_ = v___x_680_;
v_isShared_684_ = v_isSharedCheck_694_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_680_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_694_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_689_; 
v___x_685_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26));
v___x_686_ = l_Lean_Expr_replaceFn(v_e_513_, v___x_685_);
v___x_687_ = l_Lean_mkApp3(v___x_686_, v_e_x27_629_, v_a_651_, v_a_655_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___x_687_);
lean_ctor_set(v___x_633_, 0, v_a_681_);
v___x_689_ = v___x_633_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_681_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v___x_687_);
lean_ctor_set_uint8(v_reuseFailAlloc_693_, sizeof(void*)*2 + 1, v_contextDependent_631_);
v___x_689_ = v_reuseFailAlloc_693_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_691_; 
lean_ctor_set_uint8(v___x_689_, sizeof(void*)*2, v___x_544_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_689_);
v___x_691_ = v___x_683_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
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
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_dec(v_a_655_);
lean_dec(v_a_651_);
lean_del_object(v___x_633_);
lean_dec_ref(v_e_x27_629_);
lean_dec_ref(v_e_513_);
v_a_695_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_680_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_680_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec(v_a_669_);
lean_dec(v_a_655_);
lean_dec_ref(v___x_653_);
lean_dec(v_a_651_);
lean_del_object(v___x_633_);
lean_dec_ref(v_e_x27_629_);
lean_dec_ref(v_e_513_);
v_a_703_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_678_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_678_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec_ref(v___x_662_);
lean_dec(v_a_655_);
lean_dec_ref(v___x_653_);
lean_dec(v_a_651_);
lean_dec(v_a_639_);
lean_del_object(v___x_633_);
lean_dec_ref(v_e_x27_629_);
lean_dec_ref(v_arg_538_);
lean_dec_ref(v_arg_529_);
lean_dec_ref(v_e_513_);
v_a_711_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_668_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_668_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec_ref(v___x_653_);
lean_dec(v_a_651_);
lean_dec(v_a_639_);
lean_del_object(v___x_633_);
lean_dec_ref(v_e_x27_629_);
lean_dec_ref(v_arg_538_);
lean_dec_ref(v_arg_532_);
lean_dec_ref(v_arg_529_);
lean_dec_ref(v_e_513_);
v_a_719_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_654_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_654_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
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
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec(v_a_639_);
lean_del_object(v___x_633_);
lean_dec_ref(v_proof_630_);
lean_dec_ref(v_e_x27_629_);
lean_dec_ref(v_arg_538_);
lean_dec_ref(v_arg_532_);
lean_dec_ref(v_arg_529_);
lean_dec_ref(v_e_513_);
v_a_727_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_650_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_650_);
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
else
{
lean_object* v___x_735_; uint8_t v___x_736_; uint8_t v___x_737_; lean_object* v___x_739_; 
lean_dec(v_a_645_);
lean_del_object(v___x_633_);
lean_dec_ref(v_proof_630_);
lean_dec_ref(v_e_x27_629_);
lean_dec_ref(v_arg_538_);
lean_dec_ref(v_arg_532_);
lean_dec_ref(v_arg_529_);
lean_dec_ref(v_e_513_);
v___x_735_ = lean_alloc_ctor(0, 0, 2);
v___x_736_ = lean_unbox(v_a_639_);
lean_ctor_set_uint8(v___x_735_, 0, v___x_736_);
v___x_737_ = lean_unbox(v_a_639_);
lean_dec(v_a_639_);
lean_ctor_set_uint8(v___x_735_, 1, v___x_737_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_735_);
v___x_739_ = v___x_647_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_735_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec(v_a_639_);
lean_del_object(v___x_633_);
lean_dec_ref(v_proof_630_);
lean_dec_ref(v_e_x27_629_);
lean_dec_ref(v_arg_538_);
lean_dec_ref(v_arg_532_);
lean_dec_ref(v_arg_529_);
lean_dec_ref(v_e_513_);
v_a_742_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_644_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_644_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; 
lean_dec(v_a_639_);
lean_dec_ref(v_e_x27_629_);
lean_dec_ref(v_arg_532_);
lean_inc_ref(v_proof_630_);
v___x_750_ = l_Lean_Meta_mkOfEqFalseCore(v_arg_538_, v_proof_630_);
v___x_751_ = l_Lean_Meta_Sym_shareCommon(v___x_750_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; uint8_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v___x_751_, 1);
v___x_753_ = lean_unsigned_to_nat(1u);
v___x_754_ = lean_mk_empty_array_with_capacity(v___x_753_);
v___x_755_ = lean_array_push(v___x_754_, v_a_752_);
v___x_756_ = lean_unbox(v_a_636_);
v___x_757_ = lean_unbox(v_a_636_);
v___x_758_ = l_Lean_Expr_betaRev(v_arg_529_, v___x_755_, v___x_756_, v___x_757_);
lean_dec_ref(v___x_755_);
v___x_759_ = l_Lean_Meta_Sym_shareCommonInc(v___x_758_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_774_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_774_ == 0)
{
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_774_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_774_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_764_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__28));
v___x_765_ = l_Lean_Expr_replaceFn(v_e_513_, v___x_764_);
v___x_766_ = l_Lean_Expr_app___override(v___x_765_, v_proof_630_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___x_766_);
lean_ctor_set(v___x_633_, 0, v_a_760_);
v___x_768_ = v___x_633_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_760_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v___x_766_);
v___x_768_ = v_reuseFailAlloc_773_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
uint8_t v___x_769_; lean_object* v___x_771_; 
v___x_769_ = lean_unbox(v_a_636_);
lean_dec(v_a_636_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*2, v___x_769_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*2 + 1, v_contextDependent_631_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v___x_768_);
v___x_771_ = v___x_762_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_768_);
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
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec(v_a_636_);
lean_del_object(v___x_633_);
lean_dec_ref(v_proof_630_);
lean_dec_ref(v_e_513_);
v_a_775_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_759_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_759_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_a_775_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec(v_a_636_);
lean_del_object(v___x_633_);
lean_dec_ref(v_proof_630_);
lean_dec_ref(v_arg_529_);
lean_dec_ref(v_e_513_);
v_a_783_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_751_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_751_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec(v_a_636_);
lean_del_object(v___x_633_);
lean_dec_ref(v_proof_630_);
lean_dec_ref(v_e_x27_629_);
lean_dec_ref(v_arg_538_);
lean_dec_ref(v_arg_532_);
lean_dec_ref(v_arg_529_);
lean_dec_ref(v_e_513_);
v_a_791_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_638_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_638_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec(v_a_636_);
lean_dec_ref(v_e_x27_629_);
lean_dec_ref(v_arg_529_);
lean_inc_ref(v_proof_630_);
v___x_799_ = l_Lean_Meta_mkOfEqTrueCore(v_arg_538_, v_proof_630_);
v___x_800_ = l_Lean_Meta_Sym_shareCommon(v___x_799_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_800_, 1);
v___x_802_ = lean_unsigned_to_nat(1u);
v___x_803_ = lean_mk_empty_array_with_capacity(v___x_802_);
v___x_804_ = lean_array_push(v___x_803_, v_a_801_);
v___x_805_ = l_Lean_Expr_betaRev(v_arg_532_, v___x_804_, v___x_512_, v___x_512_);
lean_dec_ref(v___x_804_);
v___x_806_ = l_Lean_Meta_Sym_shareCommonInc(v___x_805_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_820_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_820_ == 0)
{
v___x_809_ = v___x_806_;
v_isShared_810_ = v_isSharedCheck_820_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_806_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_820_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_811_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__30));
v___x_812_ = l_Lean_Expr_replaceFn(v_e_513_, v___x_811_);
v___x_813_ = l_Lean_Expr_app___override(v___x_812_, v_proof_630_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___x_813_);
lean_ctor_set(v___x_633_, 0, v_a_807_);
v___x_815_ = v___x_633_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_807_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v___x_813_);
lean_ctor_set_uint8(v_reuseFailAlloc_819_, sizeof(void*)*2 + 1, v_contextDependent_631_);
v___x_815_ = v_reuseFailAlloc_819_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_817_; 
lean_ctor_set_uint8(v___x_815_, sizeof(void*)*2, v___x_512_);
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 0, v___x_815_);
v___x_817_ = v___x_809_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_del_object(v___x_633_);
lean_dec_ref(v_proof_630_);
lean_dec_ref(v_e_513_);
v_a_821_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_806_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_806_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_del_object(v___x_633_);
lean_dec_ref(v_proof_630_);
lean_dec_ref(v_arg_532_);
lean_dec_ref(v_e_513_);
v_a_829_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_800_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_800_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_del_object(v___x_633_);
lean_dec_ref(v_proof_630_);
lean_dec_ref(v_e_x27_629_);
lean_dec_ref(v_arg_538_);
lean_dec_ref(v_arg_532_);
lean_dec_ref(v_arg_529_);
lean_dec_ref(v_e_513_);
v_a_837_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_635_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_635_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_542_);
lean_dec_ref(v_arg_541_);
lean_dec_ref(v_arg_538_);
lean_dec_ref(v_arg_535_);
lean_dec_ref(v_arg_532_);
lean_dec_ref(v_arg_529_);
lean_dec_ref(v_e_513_);
return v___x_545_;
}
}
}
}
}
}
}
v___jp_524_:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_525_, 0, v___x_512_);
lean_ctor_set_uint8(v___x_525_, 1, v___x_512_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_512_ = stack[0].m_num;
lean_object* v_e_513_ = stack[1].m_obj;
lean_object* v___y_514_ = stack[2].m_obj;
lean_object* v___y_515_ = stack[3].m_obj;
lean_object* v___y_516_ = stack[4].m_obj;
lean_object* v___y_517_ = stack[5].m_obj;
lean_object* v___y_518_ = stack[6].m_obj;
lean_object* v___y_519_ = stack[7].m_obj;
lean_object* v___y_520_ = stack[8].m_obj;
lean_object* v___y_521_ = stack[9].m_obj;
lean_object* v___y_522_ = stack[10].m_obj;
lean_object* v_res_846_;
v_res_846_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0(v___x_512_, v_e_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
stack->m_obj
 = v_res_846_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___boxed(lean_object* v___x_847_, lean_object* v_e_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
uint8_t v___x_31228__boxed_859_; lean_object* v_res_860_; 
v___x_31228__boxed_859_ = lean_unbox(v___x_847_);
v_res_860_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0(v___x_31228__boxed_859_, v_e_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
return v_res_860_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte(lean_object* v_e_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_numArgs_872_; lean_object* v___x_873_; uint8_t v___x_874_; 
v_numArgs_872_ = l_Lean_Expr_getAppNumArgs(v_e_861_);
v___x_873_ = lean_unsigned_to_nat(5u);
v___x_874_ = lean_nat_dec_lt(v_numArgs_872_, v___x_873_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; lean_object* v___f_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_875_ = lean_box(v___x_874_);
v___f_876_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___boxed), 12, 1);
lean_closure_set(v___f_876_, 0, v___x_875_);
v___x_877_ = lean_nat_sub(v_numArgs_872_, v___x_873_);
lean_dec(v_numArgs_872_);
v___x_878_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_861_, v___x_877_, v___f_876_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
lean_dec(v___x_877_);
return v___x_878_;
}
else
{
uint8_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
lean_dec(v_numArgs_872_);
lean_dec_ref(v_e_861_);
v___x_879_ = 0;
v___x_880_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_880_, 0, v___x_874_);
lean_ctor_set_uint8(v___x_880_, 1, v___x_879_);
v___x_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_881_, 0, v___x_880_);
return v___x_881_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_861_ = stack[0].m_obj;
lean_object* v_a_862_ = stack[1].m_obj;
lean_object* v_a_863_ = stack[2].m_obj;
lean_object* v_a_864_ = stack[3].m_obj;
lean_object* v_a_865_ = stack[4].m_obj;
lean_object* v_a_866_ = stack[5].m_obj;
lean_object* v_a_867_ = stack[6].m_obj;
lean_object* v_a_868_ = stack[7].m_obj;
lean_object* v_a_869_ = stack[8].m_obj;
lean_object* v_a_870_ = stack[9].m_obj;
lean_object* v_res_882_;
v_res_882_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte(v_e_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_);
stack->m_obj
 = v_res_882_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___boxed(lean_object* v_e_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte(v_e_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec(v_a_884_);
return v_res_894_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpCond___lam__0(uint8_t v___x_919_, lean_object* v_e_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v___x_934_; uint8_t v___x_935_; 
lean_inc_ref(v_e_920_);
v___x_934_ = l_Lean_Expr_cleanupAnnotations(v_e_920_);
v___x_935_ = l_Lean_Expr_isApp(v___x_934_);
if (v___x_935_ == 0)
{
lean_dec_ref(v___x_934_);
lean_dec_ref(v_e_920_);
goto v___jp_931_;
}
else
{
lean_object* v_arg_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
v_arg_936_ = lean_ctor_get(v___x_934_, 1);
lean_inc_ref(v_arg_936_);
v___x_937_ = l_Lean_Expr_appFnCleanup___redArg(v___x_934_);
v___x_938_ = l_Lean_Expr_isApp(v___x_937_);
if (v___x_938_ == 0)
{
lean_dec_ref(v___x_937_);
lean_dec_ref(v_arg_936_);
lean_dec_ref(v_e_920_);
goto v___jp_931_;
}
else
{
lean_object* v_arg_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v_arg_939_ = lean_ctor_get(v___x_937_, 1);
lean_inc_ref(v_arg_939_);
v___x_940_ = l_Lean_Expr_appFnCleanup___redArg(v___x_937_);
v___x_941_ = l_Lean_Expr_isApp(v___x_940_);
if (v___x_941_ == 0)
{
lean_dec_ref(v___x_940_);
lean_dec_ref(v_arg_939_);
lean_dec_ref(v_arg_936_);
lean_dec_ref(v_e_920_);
goto v___jp_931_;
}
else
{
lean_object* v_arg_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v_arg_942_ = lean_ctor_get(v___x_940_, 1);
lean_inc_ref(v_arg_942_);
v___x_943_ = l_Lean_Expr_appFnCleanup___redArg(v___x_940_);
v___x_944_ = l_Lean_Expr_isApp(v___x_943_);
if (v___x_944_ == 0)
{
lean_dec_ref(v___x_943_);
lean_dec_ref(v_arg_942_);
lean_dec_ref(v_arg_939_);
lean_dec_ref(v_arg_936_);
lean_dec_ref(v_e_920_);
goto v___jp_931_;
}
else
{
lean_object* v_arg_945_; lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v_arg_945_ = lean_ctor_get(v___x_943_, 1);
lean_inc_ref(v_arg_945_);
v___x_946_ = l_Lean_Expr_appFnCleanup___redArg(v___x_943_);
v___x_947_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__1));
v___x_948_ = l_Lean_Expr_isConstOf(v___x_946_, v___x_947_);
if (v___x_948_ == 0)
{
lean_dec_ref(v___x_946_);
lean_dec_ref(v_arg_945_);
lean_dec_ref(v_arg_942_);
lean_dec_ref(v_arg_939_);
lean_dec_ref(v_arg_936_);
lean_dec_ref(v_e_920_);
goto v___jp_931_;
}
else
{
lean_object* v___x_949_; 
lean_inc(v___y_929_);
lean_inc_ref(v___y_928_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc_ref(v___y_922_);
lean_inc(v___y_921_);
lean_inc_ref(v_arg_942_);
v___x_949_ = lean_sym_simp(v_arg_942_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
if (lean_obj_tag(v_a_950_) == 0)
{
uint8_t v_contextDependent_951_; lean_object* v___x_952_; 
lean_dec_ref(v_e_920_);
v_contextDependent_951_ = lean_ctor_get_uint8(v_a_950_, 1);
lean_dec_ref_known(v_a_950_, 0);
v___x_952_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_924_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_996_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_996_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_996_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_996_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
size_t v___x_957_; size_t v___x_958_; uint8_t v___x_959_; 
v___x_957_ = lean_ptr_addr(v_arg_942_);
lean_dec_ref(v_arg_942_);
v___x_958_ = lean_ptr_addr(v_a_953_);
lean_dec(v_a_953_);
v___x_959_ = lean_usize_dec_eq(v___x_957_, v___x_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; 
lean_del_object(v___x_955_);
v___x_960_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_924_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_979_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_979_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_979_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_979_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
size_t v___x_965_; uint8_t v___x_966_; 
v___x_965_ = lean_ptr_addr(v_a_961_);
lean_dec(v_a_961_);
v___x_966_ = lean_usize_dec_eq(v___x_957_, v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_969_; 
lean_dec_ref(v___x_946_);
lean_dec_ref(v_arg_945_);
lean_dec_ref(v_arg_939_);
lean_dec_ref(v_arg_936_);
v___x_967_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_948_, v_contextDependent_951_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_967_);
v___x_969_ = v___x_963_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
else
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_971_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__3));
v___x_972_ = l_Lean_Expr_constLevels_x21(v___x_946_);
lean_dec_ref(v___x_946_);
v___x_973_ = l_Lean_mkConst(v___x_971_, v___x_972_);
lean_inc_ref(v_arg_936_);
v___x_974_ = l_Lean_mkApp3(v___x_973_, v_arg_945_, v_arg_939_, v_arg_936_);
v___x_975_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_975_, 0, v_arg_936_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*2, v___x_959_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*2 + 1, v_contextDependent_951_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_975_);
v___x_977_ = v___x_963_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec_ref(v___x_946_);
lean_dec_ref(v_arg_945_);
lean_dec_ref(v_arg_939_);
lean_dec_ref(v_arg_936_);
v_a_980_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_960_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_960_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_988_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__5));
v___x_989_ = l_Lean_Expr_constLevels_x21(v___x_946_);
lean_dec_ref(v___x_946_);
v___x_990_ = l_Lean_mkConst(v___x_988_, v___x_989_);
lean_inc_ref(v_arg_939_);
v___x_991_ = l_Lean_mkApp3(v___x_990_, v_arg_945_, v_arg_939_, v_arg_936_);
v___x_992_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_992_, 0, v_arg_939_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*2, v___x_919_);
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*2 + 1, v_contextDependent_951_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v___x_992_);
v___x_994_ = v___x_955_;
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
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec_ref(v___x_946_);
lean_dec_ref(v_arg_945_);
lean_dec_ref(v_arg_942_);
lean_dec_ref(v_arg_939_);
lean_dec_ref(v_arg_936_);
v_a_997_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_952_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_952_);
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
else
{
lean_object* v_e_x27_1005_; lean_object* v_proof_1006_; uint8_t v_contextDependent_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1087_; 
lean_dec_ref(v___x_946_);
lean_dec_ref(v_arg_945_);
lean_dec_ref(v_arg_942_);
v_e_x27_1005_ = lean_ctor_get(v_a_950_, 0);
v_proof_1006_ = lean_ctor_get(v_a_950_, 1);
v_contextDependent_1007_ = lean_ctor_get_uint8(v_a_950_, sizeof(void*)*2 + 1);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_a_950_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1009_ = v_a_950_;
v_isShared_1010_ = v_isSharedCheck_1087_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_proof_1006_);
lean_inc(v_e_x27_1005_);
lean_dec(v_a_950_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1087_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_924_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1078_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1014_ = v___x_1011_;
v_isShared_1015_ = v_isSharedCheck_1078_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1078_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
size_t v___x_1016_; size_t v___x_1017_; uint8_t v___x_1018_; 
v___x_1016_ = lean_ptr_addr(v_e_x27_1005_);
v___x_1017_ = lean_ptr_addr(v_a_1012_);
lean_dec(v_a_1012_);
v___x_1018_ = lean_usize_dec_eq(v___x_1016_, v___x_1017_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; 
lean_del_object(v___x_1014_);
v___x_1019_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_924_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1060_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1060_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1060_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
size_t v___x_1024_; uint8_t v___x_1025_; 
v___x_1024_ = lean_ptr_addr(v_a_1020_);
lean_dec(v_a_1020_);
v___x_1025_ = lean_usize_dec_eq(v___x_1016_, v___x_1024_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_del_object(v___x_1022_);
v___x_1026_ = lean_unsigned_to_nat(3u);
v___x_1027_ = l_Lean_Expr_getBoundedAppFn(v___x_1026_, v_e_920_);
lean_inc_ref(v_e_x27_1005_);
v___x_1028_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(v___x_1027_, v_e_x27_1005_, v_arg_939_, v_arg_936_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1042_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1031_ = v___x_1028_;
v_isShared_1032_ = v_isSharedCheck_1042_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1028_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1042_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1033_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7));
v___x_1034_ = l_Lean_Expr_replaceFn(v_e_920_, v___x_1033_);
v___x_1035_ = l_Lean_mkAppB(v___x_1034_, v_e_x27_1005_, v_proof_1006_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v___x_1035_);
lean_ctor_set(v___x_1009_, 0, v_a_1029_);
v___x_1037_ = v___x_1009_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1029_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v___x_1035_);
lean_ctor_set_uint8(v_reuseFailAlloc_1041_, sizeof(void*)*2 + 1, v_contextDependent_1007_);
v___x_1037_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1039_; 
lean_ctor_set_uint8(v___x_1037_, sizeof(void*)*2, v___x_948_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v___x_1037_);
v___x_1039_ = v___x_1031_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
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
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_del_object(v___x_1009_);
lean_dec_ref(v_proof_1006_);
lean_dec_ref(v_e_x27_1005_);
lean_dec_ref(v_e_920_);
v_a_1043_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1028_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1028_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
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
else
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
lean_dec_ref(v_e_x27_1005_);
lean_dec_ref(v_arg_939_);
v___x_1051_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9));
v___x_1052_ = l_Lean_Expr_replaceFn(v_e_920_, v___x_1051_);
v___x_1053_ = l_Lean_Expr_app___override(v___x_1052_, v_proof_1006_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v___x_1053_);
lean_ctor_set(v___x_1009_, 0, v_arg_936_);
v___x_1055_ = v___x_1009_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_arg_936_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v___x_1053_);
lean_ctor_set_uint8(v_reuseFailAlloc_1059_, sizeof(void*)*2 + 1, v_contextDependent_1007_);
v___x_1055_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1057_; 
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*2, v___x_1018_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1055_);
v___x_1057_ = v___x_1022_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
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
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_del_object(v___x_1009_);
lean_dec_ref(v_proof_1006_);
lean_dec_ref(v_e_x27_1005_);
lean_dec_ref(v_arg_939_);
lean_dec_ref(v_arg_936_);
lean_dec_ref(v_e_920_);
v_a_1061_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1019_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1019_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
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
else
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
lean_dec_ref(v_e_x27_1005_);
lean_dec_ref(v_arg_936_);
v___x_1069_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11));
v___x_1070_ = l_Lean_Expr_replaceFn(v_e_920_, v___x_1069_);
v___x_1071_ = l_Lean_Expr_app___override(v___x_1070_, v_proof_1006_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v___x_1071_);
lean_ctor_set(v___x_1009_, 0, v_arg_939_);
v___x_1073_ = v___x_1009_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_arg_939_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v___x_1071_);
lean_ctor_set_uint8(v_reuseFailAlloc_1077_, sizeof(void*)*2 + 1, v_contextDependent_1007_);
v___x_1073_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1075_; 
lean_ctor_set_uint8(v___x_1073_, sizeof(void*)*2, v___x_919_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1073_);
v___x_1075_ = v___x_1014_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1073_);
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
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_del_object(v___x_1009_);
lean_dec_ref(v_proof_1006_);
lean_dec_ref(v_e_x27_1005_);
lean_dec_ref(v_arg_939_);
lean_dec_ref(v_arg_936_);
lean_dec_ref(v_e_920_);
v_a_1079_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1011_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1011_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_946_);
lean_dec_ref(v_arg_945_);
lean_dec_ref(v_arg_942_);
lean_dec_ref(v_arg_939_);
lean_dec_ref(v_arg_936_);
lean_dec_ref(v_e_920_);
return v___x_949_;
}
}
}
}
}
}
v___jp_931_:
{
lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_932_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_932_, 0, v___x_919_);
lean_ctor_set_uint8(v___x_932_, 1, v___x_919_);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpCond___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_919_ = stack[0].m_num;
lean_object* v_e_920_ = stack[1].m_obj;
lean_object* v___y_921_ = stack[2].m_obj;
lean_object* v___y_922_ = stack[3].m_obj;
lean_object* v___y_923_ = stack[4].m_obj;
lean_object* v___y_924_ = stack[5].m_obj;
lean_object* v___y_925_ = stack[6].m_obj;
lean_object* v___y_926_ = stack[7].m_obj;
lean_object* v___y_927_ = stack[8].m_obj;
lean_object* v___y_928_ = stack[9].m_obj;
lean_object* v___y_929_ = stack[10].m_obj;
lean_object* v_res_1088_;
v_res_1088_ = l_Lean_Meta_Sym_Simp_simpCond___lam__0(v___x_919_, v_e_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_);
stack->m_obj
 = v_res_1088_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpCond___lam__0___boxed(lean_object* v___x_1089_, lean_object* v_e_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
uint8_t v___x_11369__boxed_1101_; lean_object* v_res_1102_; 
v___x_11369__boxed_1101_ = lean_unbox(v___x_1089_);
v_res_1102_ = l_Lean_Meta_Sym_Simp_simpCond___lam__0(v___x_11369__boxed_1101_, v_e_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
lean_dec(v___y_1091_);
return v_res_1102_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpCond(lean_object* v_e_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v_numArgs_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v_numArgs_1114_ = l_Lean_Expr_getAppNumArgs(v_e_1103_);
v___x_1115_ = lean_unsigned_to_nat(4u);
v___x_1116_ = lean_nat_dec_lt(v_numArgs_1114_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; lean_object* v___f_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1117_ = lean_box(v___x_1116_);
v___f_1118_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simpCond___lam__0___boxed), 12, 1);
lean_closure_set(v___f_1118_, 0, v___x_1117_);
v___x_1119_ = lean_nat_sub(v_numArgs_1114_, v___x_1115_);
lean_dec(v_numArgs_1114_);
v___x_1120_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_1103_, v___x_1119_, v___f_1118_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
lean_dec(v___x_1119_);
return v___x_1120_;
}
else
{
uint8_t v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec(v_numArgs_1114_);
lean_dec_ref(v_e_1103_);
v___x_1121_ = 0;
v___x_1122_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1122_, 0, v___x_1116_);
lean_ctor_set_uint8(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
return v___x_1123_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpCond_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1103_ = stack[0].m_obj;
lean_object* v_a_1104_ = stack[1].m_obj;
lean_object* v_a_1105_ = stack[2].m_obj;
lean_object* v_a_1106_ = stack[3].m_obj;
lean_object* v_a_1107_ = stack[4].m_obj;
lean_object* v_a_1108_ = stack[5].m_obj;
lean_object* v_a_1109_ = stack[6].m_obj;
lean_object* v_a_1110_ = stack[7].m_obj;
lean_object* v_a_1111_ = stack[8].m_obj;
lean_object* v_a_1112_ = stack[9].m_obj;
lean_object* v_res_1124_;
v_res_1124_ = l_Lean_Meta_Sym_Simp_simpCond(v_e_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_);
stack->m_obj
 = v_res_1124_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpCond___boxed(lean_object* v_e_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_Meta_Sym_Simp_simpCond(v_e_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_);
lean_dec(v_a_1134_);
lean_dec_ref(v_a_1133_);
lean_dec(v_a_1132_);
lean_dec_ref(v_a_1131_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec(v_a_1126_);
return v_res_1136_;
}
}
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg(lean_object* v_declName_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; lean_object* v_env_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1140_ = lean_st_ref_get(v___y_1138_);
v_env_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc_ref(v_env_1141_);
lean_dec(v___x_1140_);
v___x_1142_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_1141_, v_declName_1137_);
v___x_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1137_ = stack[0].m_obj;
lean_object* v___y_1138_ = stack[1].m_obj;
lean_object* v_res_1144_;
v_res_1144_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg(v_declName_1137_, v___y_1138_);
stack->m_obj
 = v_res_1144_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg___boxed(lean_object* v_declName_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg(v_declName_1145_, v___y_1146_);
lean_dec(v___y_1146_);
return v_res_1148_;
}
}
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0(lean_object* v_declName_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg(v_declName_1149_, v___y_1158_);
return v___x_1160_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1149_ = stack[0].m_obj;
lean_object* v___y_1150_ = stack[1].m_obj;
lean_object* v___y_1151_ = stack[2].m_obj;
lean_object* v___y_1152_ = stack[3].m_obj;
lean_object* v___y_1153_ = stack[4].m_obj;
lean_object* v___y_1154_ = stack[5].m_obj;
lean_object* v___y_1155_ = stack[6].m_obj;
lean_object* v___y_1156_ = stack[7].m_obj;
lean_object* v___y_1157_ = stack[8].m_obj;
lean_object* v___y_1158_ = stack[9].m_obj;
lean_object* v_res_1161_;
v_res_1161_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0(v_declName_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
stack->m_obj
 = v_res_1161_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___boxed(lean_object* v_declName_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0(v_declName_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
return v_res_1173_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch(lean_object* v_declName_1176_, lean_object* v_e_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_Meta_Sym_reduceMatcherApp_x3f(v_e_1177_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref_known(v___x_1188_, 1);
if (lean_obj_tag(v_a_1189_) == 1)
{
lean_object* v_val_1190_; lean_object* v___x_1191_; 
lean_dec_ref(v_e_1177_);
lean_dec(v_declName_1176_);
v_val_1190_ = lean_ctor_get(v_a_1189_, 0);
lean_inc_n(v_val_1190_, 2);
lean_dec_ref_known(v_a_1189_, 1);
v___x_1191_ = l_Lean_Meta_Sym_mkEqRefl(v_val_1190_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1201_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1201_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1201_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
uint8_t v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1196_ = 0;
v___x_1197_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1197_, 0, v_val_1190_);
lean_ctor_set(v___x_1197_, 1, v_a_1192_);
lean_ctor_set_uint8(v___x_1197_, sizeof(void*)*2, v___x_1196_);
lean_ctor_set_uint8(v___x_1197_, sizeof(void*)*2 + 1, v___x_1196_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1197_);
v___x_1199_ = v___x_1194_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec(v_val_1190_);
v_a_1202_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1191_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1191_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
else
{
lean_object* v___x_1210_; lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1238_; 
lean_dec(v_a_1189_);
v___x_1210_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg(v_declName_1176_, v_a_1186_);
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1213_ = v___x_1210_;
v_isShared_1214_ = v_isSharedCheck_1238_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1238_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
if (lean_obj_tag(v_a_1211_) == 1)
{
lean_object* v_val_1215_; lean_object* v_numParams_1216_; lean_object* v_numDiscrs_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_del_object(v___x_1213_);
v_val_1215_ = lean_ctor_get(v_a_1211_, 0);
lean_inc(v_val_1215_);
lean_dec_ref_known(v_a_1211_, 1);
v_numParams_1216_ = lean_ctor_get(v_val_1215_, 0);
lean_inc(v_numParams_1216_);
v_numDiscrs_1217_ = lean_ctor_get(v_val_1215_, 1);
lean_inc(v_numDiscrs_1217_);
lean_dec(v_val_1215_);
v___x_1218_ = lean_unsigned_to_nat(1u);
v___x_1219_ = lean_nat_add(v_numParams_1216_, v___x_1218_);
lean_dec(v_numParams_1216_);
v___x_1220_ = lean_nat_add(v___x_1219_, v_numDiscrs_1217_);
lean_dec(v_numDiscrs_1217_);
v___x_1221_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_e_1177_, v___x_1219_, v___x_1220_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
lean_dec(v___x_1220_);
lean_dec(v___x_1219_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
if (lean_obj_tag(v_a_1222_) == 0)
{
lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1232_; 
lean_inc_ref(v_a_1222_);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1232_ == 0)
{
lean_object* v_unused_1233_; 
v_unused_1233_ = lean_ctor_get(v___x_1221_, 0);
lean_dec(v_unused_1233_);
v___x_1224_ = v___x_1221_;
v_isShared_1225_ = v_isSharedCheck_1232_;
goto v_resetjp_1223_;
}
else
{
lean_dec(v___x_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1232_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
uint8_t v_contextDependent_1226_; uint8_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
v_contextDependent_1226_ = lean_ctor_get_uint8(v_a_1222_, 1);
lean_dec_ref_known(v_a_1222_, 0);
v___x_1227_ = 1;
v___x_1228_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_1227_, v_contextDependent_1226_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v___x_1228_);
v___x_1230_ = v___x_1224_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
else
{
return v___x_1221_;
}
}
else
{
return v___x_1221_;
}
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1236_; 
lean_dec(v_a_1211_);
lean_dec_ref(v_e_1177_);
v___x_1234_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0));
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1234_);
v___x_1236_ = v___x_1213_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1234_);
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
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_dec_ref(v_e_1177_);
lean_dec(v_declName_1176_);
v_a_1239_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1188_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1188_);
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
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1176_ = stack[0].m_obj;
lean_object* v_e_1177_ = stack[1].m_obj;
lean_object* v_a_1178_ = stack[2].m_obj;
lean_object* v_a_1179_ = stack[3].m_obj;
lean_object* v_a_1180_ = stack[4].m_obj;
lean_object* v_a_1181_ = stack[5].m_obj;
lean_object* v_a_1182_ = stack[6].m_obj;
lean_object* v_a_1183_ = stack[7].m_obj;
lean_object* v_a_1184_ = stack[8].m_obj;
lean_object* v_a_1185_ = stack[9].m_obj;
lean_object* v_a_1186_ = stack[10].m_obj;
lean_object* v_res_1247_;
v_res_1247_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch(v_declName_1176_, v_e_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
stack->m_obj
 = v_res_1247_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___boxed(lean_object* v_declName_1248_, lean_object* v_e_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch(v_declName_1248_, v_e_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec(v_a_1252_);
lean_dec_ref(v_a_1251_);
lean_dec(v_a_1250_);
return v_res_1260_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_simpControl(lean_object* v_e_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
uint8_t v___x_1272_; 
v___x_1272_ = l_Lean_Expr_isApp(v_e_1261_);
if (v___x_1272_ == 0)
{
lean_object* v___x_1273_; lean_object* v___x_1274_; 
lean_dec_ref(v_e_1261_);
v___x_1273_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1273_, 0, v___x_1272_);
lean_ctor_set_uint8(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
return v___x_1274_;
}
else
{
lean_object* v___x_1275_; 
v___x_1275_ = l_Lean_Expr_getAppFn(v_e_1261_);
if (lean_obj_tag(v___x_1275_) == 4)
{
lean_object* v_declName_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
v_declName_1276_ = lean_ctor_get(v___x_1275_, 0);
lean_inc(v_declName_1276_);
lean_dec_ref_known(v___x_1275_, 2);
v___x_1277_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__1));
v___x_1278_ = lean_name_eq(v_declName_1276_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; uint8_t v___x_1280_; 
v___x_1279_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_simpCond___lam__0___closed__1));
v___x_1280_ = lean_name_eq(v_declName_1276_, v___x_1279_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1281_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__1));
v___x_1282_ = lean_name_eq(v_declName_1276_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_object* v___x_1283_; 
v___x_1283_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch(v_declName_1276_, v_e_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
return v___x_1283_;
}
else
{
lean_object* v___x_1284_; 
lean_dec(v_declName_1276_);
v___x_1284_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte(v_e_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
return v___x_1284_;
}
}
else
{
lean_object* v___x_1285_; 
lean_dec(v_declName_1276_);
v___x_1285_ = l_Lean_Meta_Sym_Simp_simpCond(v_e_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
return v___x_1285_;
}
}
else
{
lean_object* v___x_1286_; 
lean_dec(v_declName_1276_);
v___x_1286_ = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte(v_e_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
return v___x_1286_;
}
}
else
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_dec_ref(v___x_1275_);
lean_dec_ref(v_e_1261_);
v___x_1287_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0));
v___x_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
return v___x_1288_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_simpControl_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1261_ = stack[0].m_obj;
lean_object* v_a_1262_ = stack[1].m_obj;
lean_object* v_a_1263_ = stack[2].m_obj;
lean_object* v_a_1264_ = stack[3].m_obj;
lean_object* v_a_1265_ = stack[4].m_obj;
lean_object* v_a_1266_ = stack[5].m_obj;
lean_object* v_a_1267_ = stack[6].m_obj;
lean_object* v_a_1268_ = stack[7].m_obj;
lean_object* v_a_1269_ = stack[8].m_obj;
lean_object* v_a_1270_ = stack[9].m_obj;
lean_object* v_res_1289_;
v_res_1289_ = l_Lean_Meta_Sym_Simp_simpControl(v_e_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
stack->m_obj
 = v_res_1289_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpControl___boxed(lean_object* v_e_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lean_Meta_Sym_Simp_simpControl(v_e_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_a_1291_);
return v_res_1301_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_reduceControl(lean_object* v_e_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Lean_Meta_Sym_Simp_simpControl(v_e_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1322_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1313_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1316_ = v___x_1313_;
v_isShared_1317_ = v_isSharedCheck_1322_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_a_1314_);
lean_dec(v___x_1313_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1322_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; lean_object* v___x_1320_; 
v___x_1318_ = l_Lean_Meta_Sym_Simp_Result_markAsNotDone(v_a_1314_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v___x_1318_);
v___x_1320_ = v___x_1316_;
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
}
else
{
return v___x_1313_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_reduceControl_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1302_ = stack[0].m_obj;
lean_object* v_a_1303_ = stack[1].m_obj;
lean_object* v_a_1304_ = stack[2].m_obj;
lean_object* v_a_1305_ = stack[3].m_obj;
lean_object* v_a_1306_ = stack[4].m_obj;
lean_object* v_a_1307_ = stack[5].m_obj;
lean_object* v_a_1308_ = stack[6].m_obj;
lean_object* v_a_1309_ = stack[7].m_obj;
lean_object* v_a_1310_ = stack[8].m_obj;
lean_object* v_a_1311_ = stack[9].m_obj;
lean_object* v_res_1323_;
v_res_1323_ = l_Lean_Meta_Sym_Simp_reduceControl(v_e_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
stack->m_obj
 = v_res_1323_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_reduceControl___boxed(lean_object* v_e_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_Meta_Sym_Simp_reduceControl(v_e_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
lean_dec(v_a_1331_);
lean_dec_ref(v_a_1330_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
return v_res_1335_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Reduce(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Init_Sym_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = runtime_initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Reduce(builtin);
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
lean_object* initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Reduce(uint8_t builtin);
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
res = initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Reduce(builtin);
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

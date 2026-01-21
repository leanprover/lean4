// Lean compiler output
// Module: Lean.Meta.Sym.Simp.ControlFlow
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.InferType import Lean.Meta.Sym.Simp.App import Lean.Meta.SynthInstance import Lean.Meta.WHNF import Lean.Meta.AppBuilder import Init.Sym.Lemmas
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
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__12;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__13;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__13;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__0;
lean_object* l_Lean_Expr_replaceFn(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpControl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__31;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8;
uint8_t l_Lean_Expr_isApp(lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4;
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__2;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__13;
lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__0;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__15;
lean_object* l_Lean_mkBVar(lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getBoundedAppFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpControl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__15;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__17;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__8;
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__6;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__5;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__6;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__28;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21;
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__18;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27;
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__19;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12;
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__9;
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29;
uint8_t l_Lean_Expr_isFalse(lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__16;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__22;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__7;
lean_object* l_Lean_Meta_Sym_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__1;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__8;
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__11;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__1;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__14;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__25;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__10;
uint8_t l_Lean_Expr_isTrue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__3;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__14;
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__3;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__3;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__6;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__1;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__4;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__16;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__23;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__2;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__10;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__30;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__5;
static lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__14;
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_14; uint8_t x_15; 
x_14 = lean_st_ref_get(x_3);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*6);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_9 = x_3;
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_16; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_1);
x_16 = l_Lean_Meta_Sym_Internal_Sym_assertShared(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec_ref(x_16);
lean_inc(x_3);
lean_inc_ref(x_2);
x_17 = l_Lean_Meta_Sym_Internal_Sym_assertShared(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_dec_ref(x_17);
x_9 = x_3;
x_10 = lean_box(0);
goto block_13;
}
else
{
uint8_t x_18; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Expr_app___override(x_1, x_2);
x_12 = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(x_11, x_9);
lean_dec(x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
x_13 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(x_14, x_3, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_3);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
x_14 = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(x_15, x_4, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_4);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
x_15 = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(x_16, x_5, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
else
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_5);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ite", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ite_false", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ite_true", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Decidable", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__7;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Sym", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ite_cond_congr", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__11;
x_2 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10;
x_3 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ite_cond_eq_false", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__13;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ite_cond_eq_true", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__15;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_15; uint8_t x_16; 
lean_inc_ref(x_2);
x_15 = l_Lean_Expr_cleanupAnnotations(x_2);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec_ref(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_14;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_17);
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_14;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_20);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_14;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_14;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_25);
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_28);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_30 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__1;
x_31 = l_Lean_Expr_isConstOf(x_29, x_30);
if (x_31 == 0)
{
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_14;
}
else
{
lean_object* x_32; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_25);
x_32 = lean_sym_simp(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_inc_ref(x_25);
x_36 = l_Lean_Expr_isTrue(x_25);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Expr_isFalse(x_25);
if (x_37 == 0)
{
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_ctor_set_uint8(x_34, 0, x_31);
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_34);
x_38 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__3;
x_39 = l_Lean_Expr_constLevels_x21(x_29);
lean_dec_ref(x_29);
x_40 = l_Lean_mkConst(x_38, x_39);
lean_inc_ref(x_17);
x_41 = l_Lean_mkApp3(x_40, x_28, x_20, x_17);
x_42 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_42, 0, x_17);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_36);
lean_ctor_set(x_32, 0, x_42);
return x_32;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_free_object(x_34);
lean_dec_ref(x_25);
x_43 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__5;
x_44 = l_Lean_Expr_constLevels_x21(x_29);
lean_dec_ref(x_29);
x_45 = l_Lean_mkConst(x_43, x_44);
lean_inc_ref(x_20);
x_46 = l_Lean_mkApp3(x_45, x_28, x_20, x_17);
x_47 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_47, 0, x_20);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_1);
lean_ctor_set(x_32, 0, x_47);
return x_32;
}
}
else
{
uint8_t x_48; 
lean_dec(x_34);
lean_inc_ref(x_25);
x_48 = l_Lean_Expr_isTrue(x_25);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = l_Lean_Expr_isFalse(x_25);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
x_50 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_50, 0, x_31);
lean_ctor_set(x_32, 0, x_50);
return x_32;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__3;
x_52 = l_Lean_Expr_constLevels_x21(x_29);
lean_dec_ref(x_29);
x_53 = l_Lean_mkConst(x_51, x_52);
lean_inc_ref(x_17);
x_54 = l_Lean_mkApp3(x_53, x_28, x_20, x_17);
x_55 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_55, 0, x_17);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_48);
lean_ctor_set(x_32, 0, x_55);
return x_32;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec_ref(x_25);
x_56 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__5;
x_57 = l_Lean_Expr_constLevels_x21(x_29);
lean_dec_ref(x_29);
x_58 = l_Lean_mkConst(x_56, x_57);
lean_inc_ref(x_20);
x_59 = l_Lean_mkApp3(x_58, x_28, x_20, x_17);
x_60 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_60, 0, x_20);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_1);
lean_ctor_set(x_32, 0, x_60);
return x_32;
}
}
}
else
{
uint8_t x_61; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
x_61 = !lean_is_exclusive(x_34);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_34, 0);
x_63 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_62);
x_64 = l_Lean_Expr_isTrue(x_62);
if (x_64 == 0)
{
uint8_t x_65; 
lean_inc_ref(x_62);
x_65 = l_Lean_Expr_isFalse(x_62);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_free_object(x_32);
x_66 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8;
lean_inc_ref(x_62);
x_67 = l_Lean_Expr_app___override(x_66, x_62);
x_68 = lean_box(0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_69 = l_Lean_Meta_trySynthInstance(x_67, x_68, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_69, 0);
if (lean_obj_tag(x_71) == 1)
{
lean_object* x_72; lean_object* x_73; 
lean_free_object(x_69);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
x_73 = l_Lean_Meta_Sym_shareCommon___redArg(x_72, x_6);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = lean_unsigned_to_nat(4u);
x_76 = l_Lean_Expr_getBoundedAppFn(x_75, x_2);
lean_inc(x_74);
lean_inc_ref(x_62);
x_77 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(x_76, x_62, x_74, x_20, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12;
x_81 = l_Lean_Expr_replaceFn(x_2, x_80);
x_82 = l_Lean_mkApp3(x_81, x_62, x_74, x_63);
lean_ctor_set(x_34, 1, x_82);
lean_ctor_set(x_34, 0, x_79);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_31);
lean_ctor_set(x_77, 0, x_34);
return x_77;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_77, 0);
lean_inc(x_83);
lean_dec(x_77);
x_84 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12;
x_85 = l_Lean_Expr_replaceFn(x_2, x_84);
x_86 = l_Lean_mkApp3(x_85, x_62, x_74, x_63);
lean_ctor_set(x_34, 1, x_86);
lean_ctor_set(x_34, 0, x_83);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_31);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_34);
return x_87;
}
}
else
{
uint8_t x_88; 
lean_dec(x_74);
lean_free_object(x_34);
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_2);
x_88 = !lean_is_exclusive(x_77);
if (x_88 == 0)
{
return x_77;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_77, 0);
lean_inc(x_89);
lean_dec(x_77);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_free_object(x_34);
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_91 = !lean_is_exclusive(x_73);
if (x_91 == 0)
{
return x_73;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_73, 0);
lean_inc(x_92);
lean_dec(x_73);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; 
lean_dec(x_71);
lean_free_object(x_34);
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_94 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_94, 0, x_65);
lean_ctor_set(x_69, 0, x_94);
return x_69;
}
}
else
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_69, 0);
lean_inc(x_95);
lean_dec(x_69);
if (lean_obj_tag(x_95) == 1)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_97 = l_Lean_Meta_Sym_shareCommon___redArg(x_96, x_6);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = lean_unsigned_to_nat(4u);
x_100 = l_Lean_Expr_getBoundedAppFn(x_99, x_2);
lean_inc(x_98);
lean_inc_ref(x_62);
x_101 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(x_100, x_62, x_98, x_20, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
x_104 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12;
x_105 = l_Lean_Expr_replaceFn(x_2, x_104);
x_106 = l_Lean_mkApp3(x_105, x_62, x_98, x_63);
lean_ctor_set(x_34, 1, x_106);
lean_ctor_set(x_34, 0, x_102);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_31);
if (lean_is_scalar(x_103)) {
 x_107 = lean_alloc_ctor(0, 1, 0);
} else {
 x_107 = x_103;
}
lean_ctor_set(x_107, 0, x_34);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_98);
lean_free_object(x_34);
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_2);
x_108 = lean_ctor_get(x_101, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 x_109 = x_101;
} else {
 lean_dec_ref(x_101);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_free_object(x_34);
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_111 = lean_ctor_get(x_97, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_112 = x_97;
} else {
 lean_dec_ref(x_97);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 1, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_95);
lean_free_object(x_34);
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_114 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_114, 0, x_65);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_free_object(x_34);
lean_dec_ref(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_116 = !lean_is_exclusive(x_69);
if (x_116 == 0)
{
return x_69;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_69, 0);
lean_inc(x_117);
lean_dec(x_69);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec_ref(x_62);
lean_dec_ref(x_20);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_119 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__14;
x_120 = l_Lean_Expr_replaceFn(x_2, x_119);
x_121 = l_Lean_Expr_app___override(x_120, x_63);
lean_ctor_set(x_34, 1, x_121);
lean_ctor_set(x_34, 0, x_17);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_64);
return x_32;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec_ref(x_62);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_122 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__16;
x_123 = l_Lean_Expr_replaceFn(x_2, x_122);
x_124 = l_Lean_Expr_app___override(x_123, x_63);
lean_ctor_set(x_34, 1, x_124);
lean_ctor_set(x_34, 0, x_20);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_1);
return x_32;
}
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_125 = lean_ctor_get(x_34, 0);
x_126 = lean_ctor_get(x_34, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_34);
lean_inc_ref(x_125);
x_127 = l_Lean_Expr_isTrue(x_125);
if (x_127 == 0)
{
uint8_t x_128; 
lean_inc_ref(x_125);
x_128 = l_Lean_Expr_isFalse(x_125);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_free_object(x_32);
x_129 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8;
lean_inc_ref(x_125);
x_130 = l_Lean_Expr_app___override(x_129, x_125);
x_131 = lean_box(0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_132 = l_Lean_Meta_trySynthInstance(x_130, x_131, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_134 = x_132;
} else {
 lean_dec_ref(x_132);
 x_134 = lean_box(0);
}
if (lean_obj_tag(x_133) == 1)
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_134);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec_ref(x_133);
x_136 = l_Lean_Meta_Sym_shareCommon___redArg(x_135, x_6);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec_ref(x_136);
x_138 = lean_unsigned_to_nat(4u);
x_139 = l_Lean_Expr_getBoundedAppFn(x_138, x_2);
lean_inc(x_137);
lean_inc_ref(x_125);
x_140 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(x_139, x_125, x_137, x_20, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_142 = x_140;
} else {
 lean_dec_ref(x_140);
 x_142 = lean_box(0);
}
x_143 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12;
x_144 = l_Lean_Expr_replaceFn(x_2, x_143);
x_145 = l_Lean_mkApp3(x_144, x_125, x_137, x_126);
x_146 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_146, 0, x_141);
lean_ctor_set(x_146, 1, x_145);
lean_ctor_set_uint8(x_146, sizeof(void*)*2, x_31);
if (lean_is_scalar(x_142)) {
 x_147 = lean_alloc_ctor(0, 1, 0);
} else {
 x_147 = x_142;
}
lean_ctor_set(x_147, 0, x_146);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_137);
lean_dec_ref(x_126);
lean_dec_ref(x_125);
lean_dec_ref(x_2);
x_148 = lean_ctor_get(x_140, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_149 = x_140;
} else {
 lean_dec_ref(x_140);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 1, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_148);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec_ref(x_126);
lean_dec_ref(x_125);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_151 = lean_ctor_get(x_136, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 x_152 = x_136;
} else {
 lean_dec_ref(x_136);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_133);
lean_dec_ref(x_126);
lean_dec_ref(x_125);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_154 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_154, 0, x_128);
if (lean_is_scalar(x_134)) {
 x_155 = lean_alloc_ctor(0, 1, 0);
} else {
 x_155 = x_134;
}
lean_ctor_set(x_155, 0, x_154);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec_ref(x_126);
lean_dec_ref(x_125);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_156 = lean_ctor_get(x_132, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_157 = x_132;
} else {
 lean_dec_ref(x_132);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 1, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_156);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec_ref(x_125);
lean_dec_ref(x_20);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_159 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__14;
x_160 = l_Lean_Expr_replaceFn(x_2, x_159);
x_161 = l_Lean_Expr_app___override(x_160, x_126);
x_162 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_162, 0, x_17);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*2, x_127);
lean_ctor_set(x_32, 0, x_162);
return x_32;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec_ref(x_125);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_163 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__16;
x_164 = l_Lean_Expr_replaceFn(x_2, x_163);
x_165 = l_Lean_Expr_app___override(x_164, x_126);
x_166 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_166, 0, x_20);
lean_ctor_set(x_166, 1, x_165);
lean_ctor_set_uint8(x_166, sizeof(void*)*2, x_1);
lean_ctor_set(x_32, 0, x_166);
return x_32;
}
}
}
}
else
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_32, 0);
lean_inc(x_167);
lean_dec(x_32);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; uint8_t x_169; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
if (lean_is_exclusive(x_167)) {
 x_168 = x_167;
} else {
 lean_dec_ref(x_167);
 x_168 = lean_box(0);
}
lean_inc_ref(x_25);
x_169 = l_Lean_Expr_isTrue(x_25);
if (x_169 == 0)
{
uint8_t x_170; 
x_170 = l_Lean_Expr_isFalse(x_25);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
if (lean_is_scalar(x_168)) {
 x_171 = lean_alloc_ctor(0, 0, 1);
} else {
 x_171 = x_168;
}
lean_ctor_set_uint8(x_171, 0, x_31);
x_172 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_172, 0, x_171);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_168);
x_173 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__3;
x_174 = l_Lean_Expr_constLevels_x21(x_29);
lean_dec_ref(x_29);
x_175 = l_Lean_mkConst(x_173, x_174);
lean_inc_ref(x_17);
x_176 = l_Lean_mkApp3(x_175, x_28, x_20, x_17);
x_177 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_177, 0, x_17);
lean_ctor_set(x_177, 1, x_176);
lean_ctor_set_uint8(x_177, sizeof(void*)*2, x_169);
x_178 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_178, 0, x_177);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_168);
lean_dec_ref(x_25);
x_179 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__5;
x_180 = l_Lean_Expr_constLevels_x21(x_29);
lean_dec_ref(x_29);
x_181 = l_Lean_mkConst(x_179, x_180);
lean_inc_ref(x_20);
x_182 = l_Lean_mkApp3(x_181, x_28, x_20, x_17);
x_183 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_183, 0, x_20);
lean_ctor_set(x_183, 1, x_182);
lean_ctor_set_uint8(x_183, sizeof(void*)*2, x_1);
x_184 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_184, 0, x_183);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
x_185 = lean_ctor_get(x_167, 0);
lean_inc_ref(x_185);
x_186 = lean_ctor_get(x_167, 1);
lean_inc_ref(x_186);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_187 = x_167;
} else {
 lean_dec_ref(x_167);
 x_187 = lean_box(0);
}
lean_inc_ref(x_185);
x_188 = l_Lean_Expr_isTrue(x_185);
if (x_188 == 0)
{
uint8_t x_189; 
lean_inc_ref(x_185);
x_189 = l_Lean_Expr_isFalse(x_185);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_190 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8;
lean_inc_ref(x_185);
x_191 = l_Lean_Expr_app___override(x_190, x_185);
x_192 = lean_box(0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_193 = l_Lean_Meta_trySynthInstance(x_191, x_192, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 x_195 = x_193;
} else {
 lean_dec_ref(x_193);
 x_195 = lean_box(0);
}
if (lean_obj_tag(x_194) == 1)
{
lean_object* x_196; lean_object* x_197; 
lean_dec(x_195);
x_196 = lean_ctor_get(x_194, 0);
lean_inc(x_196);
lean_dec_ref(x_194);
x_197 = l_Lean_Meta_Sym_shareCommon___redArg(x_196, x_6);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
lean_dec_ref(x_197);
x_199 = lean_unsigned_to_nat(4u);
x_200 = l_Lean_Expr_getBoundedAppFn(x_199, x_2);
lean_inc(x_198);
lean_inc_ref(x_185);
x_201 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(x_200, x_185, x_198, x_20, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
x_204 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12;
x_205 = l_Lean_Expr_replaceFn(x_2, x_204);
x_206 = l_Lean_mkApp3(x_205, x_185, x_198, x_186);
if (lean_is_scalar(x_187)) {
 x_207 = lean_alloc_ctor(1, 2, 1);
} else {
 x_207 = x_187;
}
lean_ctor_set(x_207, 0, x_202);
lean_ctor_set(x_207, 1, x_206);
lean_ctor_set_uint8(x_207, sizeof(void*)*2, x_31);
if (lean_is_scalar(x_203)) {
 x_208 = lean_alloc_ctor(0, 1, 0);
} else {
 x_208 = x_203;
}
lean_ctor_set(x_208, 0, x_207);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_198);
lean_dec(x_187);
lean_dec_ref(x_186);
lean_dec_ref(x_185);
lean_dec_ref(x_2);
x_209 = lean_ctor_get(x_201, 0);
lean_inc(x_209);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_210 = x_201;
} else {
 lean_dec_ref(x_201);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(1, 1, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_209);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_187);
lean_dec_ref(x_186);
lean_dec_ref(x_185);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_212 = lean_ctor_get(x_197, 0);
lean_inc(x_212);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 x_213 = x_197;
} else {
 lean_dec_ref(x_197);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 1, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_212);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_194);
lean_dec(x_187);
lean_dec_ref(x_186);
lean_dec_ref(x_185);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_215 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_215, 0, x_189);
if (lean_is_scalar(x_195)) {
 x_216 = lean_alloc_ctor(0, 1, 0);
} else {
 x_216 = x_195;
}
lean_ctor_set(x_216, 0, x_215);
return x_216;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_187);
lean_dec_ref(x_186);
lean_dec_ref(x_185);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_217 = lean_ctor_get(x_193, 0);
lean_inc(x_217);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 x_218 = x_193;
} else {
 lean_dec_ref(x_193);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 1, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_217);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec_ref(x_185);
lean_dec_ref(x_20);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_220 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__14;
x_221 = l_Lean_Expr_replaceFn(x_2, x_220);
x_222 = l_Lean_Expr_app___override(x_221, x_186);
if (lean_is_scalar(x_187)) {
 x_223 = lean_alloc_ctor(1, 2, 1);
} else {
 x_223 = x_187;
}
lean_ctor_set(x_223, 0, x_17);
lean_ctor_set(x_223, 1, x_222);
lean_ctor_set_uint8(x_223, sizeof(void*)*2, x_188);
x_224 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_224, 0, x_223);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec_ref(x_185);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_225 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__16;
x_226 = l_Lean_Expr_replaceFn(x_2, x_225);
x_227 = l_Lean_Expr_app___override(x_226, x_186);
if (lean_is_scalar(x_187)) {
 x_228 = lean_alloc_ctor(1, 2, 1);
} else {
 x_228 = x_187;
}
lean_ctor_set(x_228, 0, x_20);
lean_ctor_set(x_228, 1, x_227);
lean_ctor_set_uint8(x_228, sizeof(void*)*2, x_1);
x_229 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_229, 0, x_228);
return x_229;
}
}
}
}
else
{
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_32;
}
}
}
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_12, 0, x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Expr_getAppNumArgs(x_1);
x_12 = lean_unsigned_to_nat(5u);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_box(x_13);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___boxed), 11, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_17 = l_Lean_Meta_Sym_Simp_propagateOverApplied(x_1, x_16, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_18 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_18, 0, x_13);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dite", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not_false", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__3;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4;
x_2 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dite_false", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__7;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("True", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("intro", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__10;
x_2 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__9;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12;
x_2 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dite_true", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__14;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("h", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__16;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mpr_prop", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__19;
x_2 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__18;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkBVar(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mpr_not", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__23;
x_2 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__18;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dite_cond_congr", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26;
x_2 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10;
x_3 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dite_cond_eq_false", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__28;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dite_cond_eq_true", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__30;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_15; uint8_t x_16; 
lean_inc_ref(x_2);
x_15 = l_Lean_Expr_cleanupAnnotations(x_2);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec_ref(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_14;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_17);
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_14;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_20);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_14;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_14;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_25);
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_28);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_30 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__1;
x_31 = l_Lean_Expr_isConstOf(x_29, x_30);
if (x_31 == 0)
{
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_14;
}
else
{
lean_object* x_32; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_25);
x_32 = lean_sym_simp(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_inc_ref(x_25);
x_36 = l_Lean_Expr_isTrue(x_25);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Expr_isFalse(x_25);
if (x_37 == 0)
{
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_ctor_set_uint8(x_34, 0, x_31);
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_free_object(x_34);
lean_free_object(x_32);
x_38 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__6;
lean_inc_ref(x_17);
x_39 = l_Lean_Expr_betaRev(x_17, x_38, x_36, x_36);
x_40 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_39, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__8;
x_44 = l_Lean_Expr_constLevels_x21(x_29);
lean_dec_ref(x_29);
x_45 = l_Lean_mkConst(x_43, x_44);
x_46 = l_Lean_mkApp3(x_45, x_28, x_20, x_17);
x_47 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_47, 0, x_42);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_36);
lean_ctor_set(x_40, 0, x_47);
return x_40;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_40, 0);
lean_inc(x_48);
lean_dec(x_40);
x_49 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__8;
x_50 = l_Lean_Expr_constLevels_x21(x_29);
lean_dec_ref(x_29);
x_51 = l_Lean_mkConst(x_49, x_50);
x_52 = l_Lean_mkApp3(x_51, x_28, x_20, x_17);
x_53 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_36);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
x_55 = !lean_is_exclusive(x_40);
if (x_55 == 0)
{
return x_40;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_40, 0);
lean_inc(x_56);
lean_dec(x_40);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_free_object(x_34);
lean_free_object(x_32);
lean_dec_ref(x_25);
x_58 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__13;
lean_inc_ref(x_20);
x_59 = l_Lean_Expr_betaRev(x_20, x_58, x_1, x_1);
x_60 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_59, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__15;
x_64 = l_Lean_Expr_constLevels_x21(x_29);
lean_dec_ref(x_29);
x_65 = l_Lean_mkConst(x_63, x_64);
x_66 = l_Lean_mkApp3(x_65, x_28, x_20, x_17);
x_67 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_1);
lean_ctor_set(x_60, 0, x_67);
return x_60;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_60, 0);
lean_inc(x_68);
lean_dec(x_60);
x_69 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__15;
x_70 = l_Lean_Expr_constLevels_x21(x_29);
lean_dec_ref(x_29);
x_71 = l_Lean_mkConst(x_69, x_70);
x_72 = l_Lean_mkApp3(x_71, x_28, x_20, x_17);
x_73 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*2, x_1);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
x_75 = !lean_is_exclusive(x_60);
if (x_75 == 0)
{
return x_60;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_60, 0);
lean_inc(x_76);
lean_dec(x_60);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_34);
lean_inc_ref(x_25);
x_78 = l_Lean_Expr_isTrue(x_25);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_Lean_Expr_isFalse(x_25);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_6);
x_80 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_80, 0, x_31);
lean_ctor_set(x_32, 0, x_80);
return x_32;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_free_object(x_32);
x_81 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__6;
lean_inc_ref(x_17);
x_82 = l_Lean_Expr_betaRev(x_17, x_81, x_78, x_78);
x_83 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_82, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
x_86 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__8;
x_87 = l_Lean_Expr_constLevels_x21(x_29);
lean_dec_ref(x_29);
x_88 = l_Lean_mkConst(x_86, x_87);
x_89 = l_Lean_mkApp3(x_88, x_28, x_20, x_17);
x_90 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set_uint8(x_90, sizeof(void*)*2, x_78);
if (lean_is_scalar(x_85)) {
 x_91 = lean_alloc_ctor(0, 1, 0);
} else {
 x_91 = x_85;
}
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
x_92 = lean_ctor_get(x_83, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_93 = x_83;
} else {
 lean_dec_ref(x_83);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 1, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_92);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_free_object(x_32);
lean_dec_ref(x_25);
x_95 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__13;
lean_inc_ref(x_20);
x_96 = l_Lean_Expr_betaRev(x_20, x_95, x_1, x_1);
x_97 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_96, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
x_100 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__15;
x_101 = l_Lean_Expr_constLevels_x21(x_29);
lean_dec_ref(x_29);
x_102 = l_Lean_mkConst(x_100, x_101);
x_103 = l_Lean_mkApp3(x_102, x_28, x_20, x_17);
x_104 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_104, 0, x_98);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set_uint8(x_104, sizeof(void*)*2, x_1);
if (lean_is_scalar(x_99)) {
 x_105 = lean_alloc_ctor(0, 1, 0);
} else {
 x_105 = x_99;
}
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
x_106 = lean_ctor_get(x_97, 0);
lean_inc(x_106);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_107 = x_97;
} else {
 lean_dec_ref(x_97);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 1, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_106);
return x_108;
}
}
}
}
else
{
uint8_t x_109; 
lean_free_object(x_32);
lean_dec_ref(x_29);
lean_dec_ref(x_28);
x_109 = !lean_is_exclusive(x_34);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_110 = lean_ctor_get(x_34, 0);
x_111 = lean_ctor_get(x_34, 1);
lean_inc_ref(x_110);
x_112 = l_Lean_Expr_isTrue(x_110);
if (x_112 == 0)
{
uint8_t x_113; 
lean_inc_ref(x_110);
x_113 = l_Lean_Expr_isFalse(x_110);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8;
lean_inc_ref(x_110);
x_115 = l_Lean_Expr_app___override(x_114, x_110);
x_116 = lean_box(0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_117 = l_Lean_Meta_trySynthInstance(x_115, x_116, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_117, 0);
if (lean_obj_tag(x_119) == 1)
{
lean_object* x_120; lean_object* x_121; 
lean_free_object(x_117);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
x_121 = l_Lean_Meta_Sym_shareCommon___redArg(x_120, x_6);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec_ref(x_121);
x_123 = l_Lean_Meta_Sym_shareCommon___redArg(x_111, x_6);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
x_125 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__17;
x_126 = 0;
x_127 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21;
x_128 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__22;
lean_inc(x_124);
lean_inc_ref(x_110);
lean_inc_ref(x_25);
x_129 = l_Lean_mkApp4(x_127, x_25, x_110, x_124, x_128);
x_130 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5;
x_131 = lean_array_push(x_130, x_129);
x_132 = l_Lean_Expr_betaRev(x_20, x_131, x_113, x_113);
lean_dec_ref(x_131);
lean_inc_ref(x_110);
x_133 = l_Lean_mkLambda(x_125, x_126, x_110, x_132);
x_134 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_133, x_6);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
lean_inc_ref(x_110);
x_136 = l_Lean_mkNot(x_110);
x_137 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__25;
lean_inc(x_124);
lean_inc_ref(x_110);
x_138 = l_Lean_mkApp4(x_137, x_25, x_110, x_124, x_128);
x_139 = lean_array_push(x_130, x_138);
x_140 = l_Lean_Expr_betaRev(x_17, x_139, x_113, x_113);
lean_dec_ref(x_139);
x_141 = l_Lean_mkLambda(x_125, x_126, x_136, x_140);
x_142 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_141, x_6);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = lean_unsigned_to_nat(4u);
x_145 = l_Lean_Expr_getBoundedAppFn(x_144, x_2);
lean_inc(x_122);
lean_inc_ref(x_110);
x_146 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(x_145, x_110, x_122, x_135, x_143, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_146) == 0)
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_146, 0);
x_149 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27;
x_150 = l_Lean_Expr_replaceFn(x_2, x_149);
x_151 = l_Lean_mkApp3(x_150, x_110, x_122, x_124);
lean_ctor_set(x_34, 1, x_151);
lean_ctor_set(x_34, 0, x_148);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_31);
lean_ctor_set(x_146, 0, x_34);
return x_146;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_152 = lean_ctor_get(x_146, 0);
lean_inc(x_152);
lean_dec(x_146);
x_153 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27;
x_154 = l_Lean_Expr_replaceFn(x_2, x_153);
x_155 = l_Lean_mkApp3(x_154, x_110, x_122, x_124);
lean_ctor_set(x_34, 1, x_155);
lean_ctor_set(x_34, 0, x_152);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_31);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_34);
return x_156;
}
}
else
{
uint8_t x_157; 
lean_dec(x_124);
lean_dec(x_122);
lean_free_object(x_34);
lean_dec_ref(x_110);
lean_dec_ref(x_2);
x_157 = !lean_is_exclusive(x_146);
if (x_157 == 0)
{
return x_146;
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_146, 0);
lean_inc(x_158);
lean_dec(x_146);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_135);
lean_dec(x_124);
lean_dec(x_122);
lean_free_object(x_34);
lean_dec_ref(x_110);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_160 = !lean_is_exclusive(x_142);
if (x_160 == 0)
{
return x_142;
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_142, 0);
lean_inc(x_161);
lean_dec(x_142);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_161);
return x_162;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_124);
lean_dec(x_122);
lean_free_object(x_34);
lean_dec_ref(x_110);
lean_dec_ref(x_25);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_163 = !lean_is_exclusive(x_134);
if (x_163 == 0)
{
return x_134;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_134, 0);
lean_inc(x_164);
lean_dec(x_134);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_122);
lean_free_object(x_34);
lean_dec_ref(x_110);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_166 = !lean_is_exclusive(x_123);
if (x_166 == 0)
{
return x_123;
}
else
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_123, 0);
lean_inc(x_167);
lean_dec(x_123);
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_167);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_free_object(x_34);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_169 = !lean_is_exclusive(x_121);
if (x_169 == 0)
{
return x_121;
}
else
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_121, 0);
lean_inc(x_170);
lean_dec(x_121);
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_170);
return x_171;
}
}
}
else
{
lean_object* x_172; 
lean_dec(x_119);
lean_free_object(x_34);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_172 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_172, 0, x_113);
lean_ctor_set(x_117, 0, x_172);
return x_117;
}
}
else
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_117, 0);
lean_inc(x_173);
lean_dec(x_117);
if (lean_obj_tag(x_173) == 1)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec_ref(x_173);
x_175 = l_Lean_Meta_Sym_shareCommon___redArg(x_174, x_6);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec_ref(x_175);
x_177 = l_Lean_Meta_Sym_shareCommon___redArg(x_111, x_6);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec_ref(x_177);
x_179 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__17;
x_180 = 0;
x_181 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21;
x_182 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__22;
lean_inc(x_178);
lean_inc_ref(x_110);
lean_inc_ref(x_25);
x_183 = l_Lean_mkApp4(x_181, x_25, x_110, x_178, x_182);
x_184 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5;
x_185 = lean_array_push(x_184, x_183);
x_186 = l_Lean_Expr_betaRev(x_20, x_185, x_113, x_113);
lean_dec_ref(x_185);
lean_inc_ref(x_110);
x_187 = l_Lean_mkLambda(x_179, x_180, x_110, x_186);
x_188 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_187, x_6);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
lean_dec_ref(x_188);
lean_inc_ref(x_110);
x_190 = l_Lean_mkNot(x_110);
x_191 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__25;
lean_inc(x_178);
lean_inc_ref(x_110);
x_192 = l_Lean_mkApp4(x_191, x_25, x_110, x_178, x_182);
x_193 = lean_array_push(x_184, x_192);
x_194 = l_Lean_Expr_betaRev(x_17, x_193, x_113, x_113);
lean_dec_ref(x_193);
x_195 = l_Lean_mkLambda(x_179, x_180, x_190, x_194);
x_196 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_195, x_6);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
lean_dec_ref(x_196);
x_198 = lean_unsigned_to_nat(4u);
x_199 = l_Lean_Expr_getBoundedAppFn(x_198, x_2);
lean_inc(x_176);
lean_inc_ref(x_110);
x_200 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(x_199, x_110, x_176, x_189, x_197, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 x_202 = x_200;
} else {
 lean_dec_ref(x_200);
 x_202 = lean_box(0);
}
x_203 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27;
x_204 = l_Lean_Expr_replaceFn(x_2, x_203);
x_205 = l_Lean_mkApp3(x_204, x_110, x_176, x_178);
lean_ctor_set(x_34, 1, x_205);
lean_ctor_set(x_34, 0, x_201);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_31);
if (lean_is_scalar(x_202)) {
 x_206 = lean_alloc_ctor(0, 1, 0);
} else {
 x_206 = x_202;
}
lean_ctor_set(x_206, 0, x_34);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_178);
lean_dec(x_176);
lean_free_object(x_34);
lean_dec_ref(x_110);
lean_dec_ref(x_2);
x_207 = lean_ctor_get(x_200, 0);
lean_inc(x_207);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 x_208 = x_200;
} else {
 lean_dec_ref(x_200);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 1, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_207);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_189);
lean_dec(x_178);
lean_dec(x_176);
lean_free_object(x_34);
lean_dec_ref(x_110);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_210 = lean_ctor_get(x_196, 0);
lean_inc(x_210);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 x_211 = x_196;
} else {
 lean_dec_ref(x_196);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 1, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_210);
return x_212;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_178);
lean_dec(x_176);
lean_free_object(x_34);
lean_dec_ref(x_110);
lean_dec_ref(x_25);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_213 = lean_ctor_get(x_188, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 x_214 = x_188;
} else {
 lean_dec_ref(x_188);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 1, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_213);
return x_215;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_176);
lean_free_object(x_34);
lean_dec_ref(x_110);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_216 = lean_ctor_get(x_177, 0);
lean_inc(x_216);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 x_217 = x_177;
} else {
 lean_dec_ref(x_177);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(1, 1, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_216);
return x_218;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_free_object(x_34);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_219 = lean_ctor_get(x_175, 0);
lean_inc(x_219);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 x_220 = x_175;
} else {
 lean_dec_ref(x_175);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(1, 1, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_219);
return x_221;
}
}
else
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_173);
lean_free_object(x_34);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_222 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_222, 0, x_113);
x_223 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_223, 0, x_222);
return x_223;
}
}
}
else
{
uint8_t x_224; 
lean_free_object(x_34);
lean_dec_ref(x_111);
lean_dec_ref(x_110);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_224 = !lean_is_exclusive(x_117);
if (x_224 == 0)
{
return x_117;
}
else
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_117, 0);
lean_inc(x_225);
lean_dec(x_117);
x_226 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_226, 0, x_225);
return x_226;
}
}
}
else
{
lean_object* x_227; lean_object* x_228; 
lean_dec_ref(x_110);
lean_dec_ref(x_20);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc_ref(x_111);
x_227 = l_Lean_Meta_mkOfEqFalseCore(x_25, x_111);
x_228 = l_Lean_Meta_Sym_shareCommon___redArg(x_227, x_6);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
lean_dec_ref(x_228);
x_230 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5;
x_231 = lean_array_push(x_230, x_229);
x_232 = l_Lean_Expr_betaRev(x_17, x_231, x_112, x_112);
lean_dec_ref(x_231);
x_233 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_232, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_233) == 0)
{
uint8_t x_234; 
x_234 = !lean_is_exclusive(x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_235 = lean_ctor_get(x_233, 0);
x_236 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29;
x_237 = l_Lean_Expr_replaceFn(x_2, x_236);
x_238 = l_Lean_Expr_app___override(x_237, x_111);
lean_ctor_set(x_34, 1, x_238);
lean_ctor_set(x_34, 0, x_235);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_112);
lean_ctor_set(x_233, 0, x_34);
return x_233;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_239 = lean_ctor_get(x_233, 0);
lean_inc(x_239);
lean_dec(x_233);
x_240 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29;
x_241 = l_Lean_Expr_replaceFn(x_2, x_240);
x_242 = l_Lean_Expr_app___override(x_241, x_111);
lean_ctor_set(x_34, 1, x_242);
lean_ctor_set(x_34, 0, x_239);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_112);
x_243 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_243, 0, x_34);
return x_243;
}
}
else
{
uint8_t x_244; 
lean_free_object(x_34);
lean_dec_ref(x_111);
lean_dec_ref(x_2);
x_244 = !lean_is_exclusive(x_233);
if (x_244 == 0)
{
return x_233;
}
else
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_233, 0);
lean_inc(x_245);
lean_dec(x_233);
x_246 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_246, 0, x_245);
return x_246;
}
}
}
else
{
uint8_t x_247; 
lean_free_object(x_34);
lean_dec_ref(x_111);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_2);
x_247 = !lean_is_exclusive(x_228);
if (x_247 == 0)
{
return x_228;
}
else
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_228, 0);
lean_inc(x_248);
lean_dec(x_228);
x_249 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_249, 0, x_248);
return x_249;
}
}
}
}
else
{
lean_object* x_250; lean_object* x_251; 
lean_dec_ref(x_110);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc_ref(x_111);
x_250 = l_Lean_Meta_mkOfEqTrueCore(x_25, x_111);
x_251 = l_Lean_Meta_Sym_shareCommon___redArg(x_250, x_6);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
lean_dec_ref(x_251);
x_253 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5;
x_254 = lean_array_push(x_253, x_252);
x_255 = l_Lean_Expr_betaRev(x_20, x_254, x_1, x_1);
lean_dec_ref(x_254);
x_256 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_255, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_256) == 0)
{
uint8_t x_257; 
x_257 = !lean_is_exclusive(x_256);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_258 = lean_ctor_get(x_256, 0);
x_259 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__31;
x_260 = l_Lean_Expr_replaceFn(x_2, x_259);
x_261 = l_Lean_Expr_app___override(x_260, x_111);
lean_ctor_set(x_34, 1, x_261);
lean_ctor_set(x_34, 0, x_258);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_1);
lean_ctor_set(x_256, 0, x_34);
return x_256;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_262 = lean_ctor_get(x_256, 0);
lean_inc(x_262);
lean_dec(x_256);
x_263 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__31;
x_264 = l_Lean_Expr_replaceFn(x_2, x_263);
x_265 = l_Lean_Expr_app___override(x_264, x_111);
lean_ctor_set(x_34, 1, x_265);
lean_ctor_set(x_34, 0, x_262);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_1);
x_266 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_266, 0, x_34);
return x_266;
}
}
else
{
uint8_t x_267; 
lean_free_object(x_34);
lean_dec_ref(x_111);
lean_dec_ref(x_2);
x_267 = !lean_is_exclusive(x_256);
if (x_267 == 0)
{
return x_256;
}
else
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_ctor_get(x_256, 0);
lean_inc(x_268);
lean_dec(x_256);
x_269 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_269, 0, x_268);
return x_269;
}
}
}
else
{
uint8_t x_270; 
lean_free_object(x_34);
lean_dec_ref(x_111);
lean_dec_ref(x_20);
lean_dec(x_6);
lean_dec_ref(x_2);
x_270 = !lean_is_exclusive(x_251);
if (x_270 == 0)
{
return x_251;
}
else
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_251, 0);
lean_inc(x_271);
lean_dec(x_251);
x_272 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_272, 0, x_271);
return x_272;
}
}
}
}
else
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_273 = lean_ctor_get(x_34, 0);
x_274 = lean_ctor_get(x_34, 1);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_34);
lean_inc_ref(x_273);
x_275 = l_Lean_Expr_isTrue(x_273);
if (x_275 == 0)
{
uint8_t x_276; 
lean_inc_ref(x_273);
x_276 = l_Lean_Expr_isFalse(x_273);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_277 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8;
lean_inc_ref(x_273);
x_278 = l_Lean_Expr_app___override(x_277, x_273);
x_279 = lean_box(0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_280 = l_Lean_Meta_trySynthInstance(x_278, x_279, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 x_282 = x_280;
} else {
 lean_dec_ref(x_280);
 x_282 = lean_box(0);
}
if (lean_obj_tag(x_281) == 1)
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_282);
x_283 = lean_ctor_get(x_281, 0);
lean_inc(x_283);
lean_dec_ref(x_281);
x_284 = l_Lean_Meta_Sym_shareCommon___redArg(x_283, x_6);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
lean_dec_ref(x_284);
x_286 = l_Lean_Meta_Sym_shareCommon___redArg(x_274, x_6);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
lean_dec_ref(x_286);
x_288 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__17;
x_289 = 0;
x_290 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21;
x_291 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__22;
lean_inc(x_287);
lean_inc_ref(x_273);
lean_inc_ref(x_25);
x_292 = l_Lean_mkApp4(x_290, x_25, x_273, x_287, x_291);
x_293 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5;
x_294 = lean_array_push(x_293, x_292);
x_295 = l_Lean_Expr_betaRev(x_20, x_294, x_276, x_276);
lean_dec_ref(x_294);
lean_inc_ref(x_273);
x_296 = l_Lean_mkLambda(x_288, x_289, x_273, x_295);
x_297 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_296, x_6);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
lean_dec_ref(x_297);
lean_inc_ref(x_273);
x_299 = l_Lean_mkNot(x_273);
x_300 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__25;
lean_inc(x_287);
lean_inc_ref(x_273);
x_301 = l_Lean_mkApp4(x_300, x_25, x_273, x_287, x_291);
x_302 = lean_array_push(x_293, x_301);
x_303 = l_Lean_Expr_betaRev(x_17, x_302, x_276, x_276);
lean_dec_ref(x_302);
x_304 = l_Lean_mkLambda(x_288, x_289, x_299, x_303);
x_305 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_304, x_6);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
lean_dec_ref(x_305);
x_307 = lean_unsigned_to_nat(4u);
x_308 = l_Lean_Expr_getBoundedAppFn(x_307, x_2);
lean_inc(x_285);
lean_inc_ref(x_273);
x_309 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(x_308, x_273, x_285, x_298, x_306, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 x_311 = x_309;
} else {
 lean_dec_ref(x_309);
 x_311 = lean_box(0);
}
x_312 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27;
x_313 = l_Lean_Expr_replaceFn(x_2, x_312);
x_314 = l_Lean_mkApp3(x_313, x_273, x_285, x_287);
x_315 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_315, 0, x_310);
lean_ctor_set(x_315, 1, x_314);
lean_ctor_set_uint8(x_315, sizeof(void*)*2, x_31);
if (lean_is_scalar(x_311)) {
 x_316 = lean_alloc_ctor(0, 1, 0);
} else {
 x_316 = x_311;
}
lean_ctor_set(x_316, 0, x_315);
return x_316;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_287);
lean_dec(x_285);
lean_dec_ref(x_273);
lean_dec_ref(x_2);
x_317 = lean_ctor_get(x_309, 0);
lean_inc(x_317);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 x_318 = x_309;
} else {
 lean_dec_ref(x_309);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(1, 1, 0);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_317);
return x_319;
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_dec(x_298);
lean_dec(x_287);
lean_dec(x_285);
lean_dec_ref(x_273);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_320 = lean_ctor_get(x_305, 0);
lean_inc(x_320);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 x_321 = x_305;
} else {
 lean_dec_ref(x_305);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(1, 1, 0);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_320);
return x_322;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_287);
lean_dec(x_285);
lean_dec_ref(x_273);
lean_dec_ref(x_25);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_323 = lean_ctor_get(x_297, 0);
lean_inc(x_323);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 x_324 = x_297;
} else {
 lean_dec_ref(x_297);
 x_324 = lean_box(0);
}
if (lean_is_scalar(x_324)) {
 x_325 = lean_alloc_ctor(1, 1, 0);
} else {
 x_325 = x_324;
}
lean_ctor_set(x_325, 0, x_323);
return x_325;
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_285);
lean_dec_ref(x_273);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_326 = lean_ctor_get(x_286, 0);
lean_inc(x_326);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 x_327 = x_286;
} else {
 lean_dec_ref(x_286);
 x_327 = lean_box(0);
}
if (lean_is_scalar(x_327)) {
 x_328 = lean_alloc_ctor(1, 1, 0);
} else {
 x_328 = x_327;
}
lean_ctor_set(x_328, 0, x_326);
return x_328;
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec_ref(x_274);
lean_dec_ref(x_273);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_329 = lean_ctor_get(x_284, 0);
lean_inc(x_329);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 x_330 = x_284;
} else {
 lean_dec_ref(x_284);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(1, 1, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_329);
return x_331;
}
}
else
{
lean_object* x_332; lean_object* x_333; 
lean_dec(x_281);
lean_dec_ref(x_274);
lean_dec_ref(x_273);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_332 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_332, 0, x_276);
if (lean_is_scalar(x_282)) {
 x_333 = lean_alloc_ctor(0, 1, 0);
} else {
 x_333 = x_282;
}
lean_ctor_set(x_333, 0, x_332);
return x_333;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec_ref(x_274);
lean_dec_ref(x_273);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_334 = lean_ctor_get(x_280, 0);
lean_inc(x_334);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 x_335 = x_280;
} else {
 lean_dec_ref(x_280);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(1, 1, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_334);
return x_336;
}
}
else
{
lean_object* x_337; lean_object* x_338; 
lean_dec_ref(x_273);
lean_dec_ref(x_20);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc_ref(x_274);
x_337 = l_Lean_Meta_mkOfEqFalseCore(x_25, x_274);
x_338 = l_Lean_Meta_Sym_shareCommon___redArg(x_337, x_6);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
lean_dec_ref(x_338);
x_340 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5;
x_341 = lean_array_push(x_340, x_339);
x_342 = l_Lean_Expr_betaRev(x_17, x_341, x_275, x_275);
lean_dec_ref(x_341);
x_343 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_342, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 x_345 = x_343;
} else {
 lean_dec_ref(x_343);
 x_345 = lean_box(0);
}
x_346 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29;
x_347 = l_Lean_Expr_replaceFn(x_2, x_346);
x_348 = l_Lean_Expr_app___override(x_347, x_274);
x_349 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_349, 0, x_344);
lean_ctor_set(x_349, 1, x_348);
lean_ctor_set_uint8(x_349, sizeof(void*)*2, x_275);
if (lean_is_scalar(x_345)) {
 x_350 = lean_alloc_ctor(0, 1, 0);
} else {
 x_350 = x_345;
}
lean_ctor_set(x_350, 0, x_349);
return x_350;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec_ref(x_274);
lean_dec_ref(x_2);
x_351 = lean_ctor_get(x_343, 0);
lean_inc(x_351);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 x_352 = x_343;
} else {
 lean_dec_ref(x_343);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 1, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_351);
return x_353;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec_ref(x_274);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_2);
x_354 = lean_ctor_get(x_338, 0);
lean_inc(x_354);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 x_355 = x_338;
} else {
 lean_dec_ref(x_338);
 x_355 = lean_box(0);
}
if (lean_is_scalar(x_355)) {
 x_356 = lean_alloc_ctor(1, 1, 0);
} else {
 x_356 = x_355;
}
lean_ctor_set(x_356, 0, x_354);
return x_356;
}
}
}
else
{
lean_object* x_357; lean_object* x_358; 
lean_dec_ref(x_273);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc_ref(x_274);
x_357 = l_Lean_Meta_mkOfEqTrueCore(x_25, x_274);
x_358 = l_Lean_Meta_Sym_shareCommon___redArg(x_357, x_6);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
lean_dec_ref(x_358);
x_360 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5;
x_361 = lean_array_push(x_360, x_359);
x_362 = l_Lean_Expr_betaRev(x_20, x_361, x_1, x_1);
lean_dec_ref(x_361);
x_363 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_362, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 x_365 = x_363;
} else {
 lean_dec_ref(x_363);
 x_365 = lean_box(0);
}
x_366 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__31;
x_367 = l_Lean_Expr_replaceFn(x_2, x_366);
x_368 = l_Lean_Expr_app___override(x_367, x_274);
x_369 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_369, 0, x_364);
lean_ctor_set(x_369, 1, x_368);
lean_ctor_set_uint8(x_369, sizeof(void*)*2, x_1);
if (lean_is_scalar(x_365)) {
 x_370 = lean_alloc_ctor(0, 1, 0);
} else {
 x_370 = x_365;
}
lean_ctor_set(x_370, 0, x_369);
return x_370;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec_ref(x_274);
lean_dec_ref(x_2);
x_371 = lean_ctor_get(x_363, 0);
lean_inc(x_371);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 x_372 = x_363;
} else {
 lean_dec_ref(x_363);
 x_372 = lean_box(0);
}
if (lean_is_scalar(x_372)) {
 x_373 = lean_alloc_ctor(1, 1, 0);
} else {
 x_373 = x_372;
}
lean_ctor_set(x_373, 0, x_371);
return x_373;
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_dec_ref(x_274);
lean_dec_ref(x_20);
lean_dec(x_6);
lean_dec_ref(x_2);
x_374 = lean_ctor_get(x_358, 0);
lean_inc(x_374);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 x_375 = x_358;
} else {
 lean_dec_ref(x_358);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_375)) {
 x_376 = lean_alloc_ctor(1, 1, 0);
} else {
 x_376 = x_375;
}
lean_ctor_set(x_376, 0, x_374);
return x_376;
}
}
}
}
}
else
{
lean_object* x_377; 
x_377 = lean_ctor_get(x_32, 0);
lean_inc(x_377);
lean_dec(x_32);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; uint8_t x_379; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
if (lean_is_exclusive(x_377)) {
 x_378 = x_377;
} else {
 lean_dec_ref(x_377);
 x_378 = lean_box(0);
}
lean_inc_ref(x_25);
x_379 = l_Lean_Expr_isTrue(x_25);
if (x_379 == 0)
{
uint8_t x_380; 
x_380 = l_Lean_Expr_isFalse(x_25);
if (x_380 == 0)
{
lean_object* x_381; lean_object* x_382; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_6);
if (lean_is_scalar(x_378)) {
 x_381 = lean_alloc_ctor(0, 0, 1);
} else {
 x_381 = x_378;
}
lean_ctor_set_uint8(x_381, 0, x_31);
x_382 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_382, 0, x_381);
return x_382;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_378);
x_383 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__6;
lean_inc_ref(x_17);
x_384 = l_Lean_Expr_betaRev(x_17, x_383, x_379, x_379);
x_385 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_384, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 x_387 = x_385;
} else {
 lean_dec_ref(x_385);
 x_387 = lean_box(0);
}
x_388 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__8;
x_389 = l_Lean_Expr_constLevels_x21(x_29);
lean_dec_ref(x_29);
x_390 = l_Lean_mkConst(x_388, x_389);
x_391 = l_Lean_mkApp3(x_390, x_28, x_20, x_17);
x_392 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_392, 0, x_386);
lean_ctor_set(x_392, 1, x_391);
lean_ctor_set_uint8(x_392, sizeof(void*)*2, x_379);
if (lean_is_scalar(x_387)) {
 x_393 = lean_alloc_ctor(0, 1, 0);
} else {
 x_393 = x_387;
}
lean_ctor_set(x_393, 0, x_392);
return x_393;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
x_394 = lean_ctor_get(x_385, 0);
lean_inc(x_394);
if (lean_is_exclusive(x_385)) {
 lean_ctor_release(x_385, 0);
 x_395 = x_385;
} else {
 lean_dec_ref(x_385);
 x_395 = lean_box(0);
}
if (lean_is_scalar(x_395)) {
 x_396 = lean_alloc_ctor(1, 1, 0);
} else {
 x_396 = x_395;
}
lean_ctor_set(x_396, 0, x_394);
return x_396;
}
}
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_378);
lean_dec_ref(x_25);
x_397 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__13;
lean_inc_ref(x_20);
x_398 = l_Lean_Expr_betaRev(x_20, x_397, x_1, x_1);
x_399 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_398, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 x_401 = x_399;
} else {
 lean_dec_ref(x_399);
 x_401 = lean_box(0);
}
x_402 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__15;
x_403 = l_Lean_Expr_constLevels_x21(x_29);
lean_dec_ref(x_29);
x_404 = l_Lean_mkConst(x_402, x_403);
x_405 = l_Lean_mkApp3(x_404, x_28, x_20, x_17);
x_406 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_406, 0, x_400);
lean_ctor_set(x_406, 1, x_405);
lean_ctor_set_uint8(x_406, sizeof(void*)*2, x_1);
if (lean_is_scalar(x_401)) {
 x_407 = lean_alloc_ctor(0, 1, 0);
} else {
 x_407 = x_401;
}
lean_ctor_set(x_407, 0, x_406);
return x_407;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
x_408 = lean_ctor_get(x_399, 0);
lean_inc(x_408);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 x_409 = x_399;
} else {
 lean_dec_ref(x_399);
 x_409 = lean_box(0);
}
if (lean_is_scalar(x_409)) {
 x_410 = lean_alloc_ctor(1, 1, 0);
} else {
 x_410 = x_409;
}
lean_ctor_set(x_410, 0, x_408);
return x_410;
}
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
x_411 = lean_ctor_get(x_377, 0);
lean_inc_ref(x_411);
x_412 = lean_ctor_get(x_377, 1);
lean_inc_ref(x_412);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_413 = x_377;
} else {
 lean_dec_ref(x_377);
 x_413 = lean_box(0);
}
lean_inc_ref(x_411);
x_414 = l_Lean_Expr_isTrue(x_411);
if (x_414 == 0)
{
uint8_t x_415; 
lean_inc_ref(x_411);
x_415 = l_Lean_Expr_isFalse(x_411);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_416 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8;
lean_inc_ref(x_411);
x_417 = l_Lean_Expr_app___override(x_416, x_411);
x_418 = lean_box(0);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_419 = l_Lean_Meta_trySynthInstance(x_417, x_418, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 x_421 = x_419;
} else {
 lean_dec_ref(x_419);
 x_421 = lean_box(0);
}
if (lean_obj_tag(x_420) == 1)
{
lean_object* x_422; lean_object* x_423; 
lean_dec(x_421);
x_422 = lean_ctor_get(x_420, 0);
lean_inc(x_422);
lean_dec_ref(x_420);
x_423 = l_Lean_Meta_Sym_shareCommon___redArg(x_422, x_6);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
lean_dec_ref(x_423);
x_425 = l_Lean_Meta_Sym_shareCommon___redArg(x_412, x_6);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; uint8_t x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
lean_dec_ref(x_425);
x_427 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__17;
x_428 = 0;
x_429 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21;
x_430 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__22;
lean_inc(x_426);
lean_inc_ref(x_411);
lean_inc_ref(x_25);
x_431 = l_Lean_mkApp4(x_429, x_25, x_411, x_426, x_430);
x_432 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5;
x_433 = lean_array_push(x_432, x_431);
x_434 = l_Lean_Expr_betaRev(x_20, x_433, x_415, x_415);
lean_dec_ref(x_433);
lean_inc_ref(x_411);
x_435 = l_Lean_mkLambda(x_427, x_428, x_411, x_434);
x_436 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_435, x_6);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
lean_dec_ref(x_436);
lean_inc_ref(x_411);
x_438 = l_Lean_mkNot(x_411);
x_439 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__25;
lean_inc(x_426);
lean_inc_ref(x_411);
x_440 = l_Lean_mkApp4(x_439, x_25, x_411, x_426, x_430);
x_441 = lean_array_push(x_432, x_440);
x_442 = l_Lean_Expr_betaRev(x_17, x_441, x_415, x_415);
lean_dec_ref(x_441);
x_443 = l_Lean_mkLambda(x_427, x_428, x_438, x_442);
x_444 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_443, x_6);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
lean_dec_ref(x_444);
x_446 = lean_unsigned_to_nat(4u);
x_447 = l_Lean_Expr_getBoundedAppFn(x_446, x_2);
lean_inc(x_424);
lean_inc_ref(x_411);
x_448 = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0(x_447, x_411, x_424, x_437, x_445, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 x_450 = x_448;
} else {
 lean_dec_ref(x_448);
 x_450 = lean_box(0);
}
x_451 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27;
x_452 = l_Lean_Expr_replaceFn(x_2, x_451);
x_453 = l_Lean_mkApp3(x_452, x_411, x_424, x_426);
if (lean_is_scalar(x_413)) {
 x_454 = lean_alloc_ctor(1, 2, 1);
} else {
 x_454 = x_413;
}
lean_ctor_set(x_454, 0, x_449);
lean_ctor_set(x_454, 1, x_453);
lean_ctor_set_uint8(x_454, sizeof(void*)*2, x_31);
if (lean_is_scalar(x_450)) {
 x_455 = lean_alloc_ctor(0, 1, 0);
} else {
 x_455 = x_450;
}
lean_ctor_set(x_455, 0, x_454);
return x_455;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_426);
lean_dec(x_424);
lean_dec(x_413);
lean_dec_ref(x_411);
lean_dec_ref(x_2);
x_456 = lean_ctor_get(x_448, 0);
lean_inc(x_456);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 x_457 = x_448;
} else {
 lean_dec_ref(x_448);
 x_457 = lean_box(0);
}
if (lean_is_scalar(x_457)) {
 x_458 = lean_alloc_ctor(1, 1, 0);
} else {
 x_458 = x_457;
}
lean_ctor_set(x_458, 0, x_456);
return x_458;
}
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
lean_dec(x_437);
lean_dec(x_426);
lean_dec(x_424);
lean_dec(x_413);
lean_dec_ref(x_411);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_459 = lean_ctor_get(x_444, 0);
lean_inc(x_459);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 x_460 = x_444;
} else {
 lean_dec_ref(x_444);
 x_460 = lean_box(0);
}
if (lean_is_scalar(x_460)) {
 x_461 = lean_alloc_ctor(1, 1, 0);
} else {
 x_461 = x_460;
}
lean_ctor_set(x_461, 0, x_459);
return x_461;
}
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; 
lean_dec(x_426);
lean_dec(x_424);
lean_dec(x_413);
lean_dec_ref(x_411);
lean_dec_ref(x_25);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_462 = lean_ctor_get(x_436, 0);
lean_inc(x_462);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 x_463 = x_436;
} else {
 lean_dec_ref(x_436);
 x_463 = lean_box(0);
}
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(1, 1, 0);
} else {
 x_464 = x_463;
}
lean_ctor_set(x_464, 0, x_462);
return x_464;
}
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; 
lean_dec(x_424);
lean_dec(x_413);
lean_dec_ref(x_411);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_465 = lean_ctor_get(x_425, 0);
lean_inc(x_465);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 x_466 = x_425;
} else {
 lean_dec_ref(x_425);
 x_466 = lean_box(0);
}
if (lean_is_scalar(x_466)) {
 x_467 = lean_alloc_ctor(1, 1, 0);
} else {
 x_467 = x_466;
}
lean_ctor_set(x_467, 0, x_465);
return x_467;
}
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
lean_dec(x_413);
lean_dec_ref(x_412);
lean_dec_ref(x_411);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_468 = lean_ctor_get(x_423, 0);
lean_inc(x_468);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 x_469 = x_423;
} else {
 lean_dec_ref(x_423);
 x_469 = lean_box(0);
}
if (lean_is_scalar(x_469)) {
 x_470 = lean_alloc_ctor(1, 1, 0);
} else {
 x_470 = x_469;
}
lean_ctor_set(x_470, 0, x_468);
return x_470;
}
}
else
{
lean_object* x_471; lean_object* x_472; 
lean_dec(x_420);
lean_dec(x_413);
lean_dec_ref(x_412);
lean_dec_ref(x_411);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_471 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_471, 0, x_415);
if (lean_is_scalar(x_421)) {
 x_472 = lean_alloc_ctor(0, 1, 0);
} else {
 x_472 = x_421;
}
lean_ctor_set(x_472, 0, x_471);
return x_472;
}
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; 
lean_dec(x_413);
lean_dec_ref(x_412);
lean_dec_ref(x_411);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_473 = lean_ctor_get(x_419, 0);
lean_inc(x_473);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 x_474 = x_419;
} else {
 lean_dec_ref(x_419);
 x_474 = lean_box(0);
}
if (lean_is_scalar(x_474)) {
 x_475 = lean_alloc_ctor(1, 1, 0);
} else {
 x_475 = x_474;
}
lean_ctor_set(x_475, 0, x_473);
return x_475;
}
}
else
{
lean_object* x_476; lean_object* x_477; 
lean_dec_ref(x_411);
lean_dec_ref(x_20);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc_ref(x_412);
x_476 = l_Lean_Meta_mkOfEqFalseCore(x_25, x_412);
x_477 = l_Lean_Meta_Sym_shareCommon___redArg(x_476, x_6);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
lean_dec_ref(x_477);
x_479 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5;
x_480 = lean_array_push(x_479, x_478);
x_481 = l_Lean_Expr_betaRev(x_17, x_480, x_414, x_414);
lean_dec_ref(x_480);
x_482 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_481, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 x_484 = x_482;
} else {
 lean_dec_ref(x_482);
 x_484 = lean_box(0);
}
x_485 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29;
x_486 = l_Lean_Expr_replaceFn(x_2, x_485);
x_487 = l_Lean_Expr_app___override(x_486, x_412);
if (lean_is_scalar(x_413)) {
 x_488 = lean_alloc_ctor(1, 2, 1);
} else {
 x_488 = x_413;
}
lean_ctor_set(x_488, 0, x_483);
lean_ctor_set(x_488, 1, x_487);
lean_ctor_set_uint8(x_488, sizeof(void*)*2, x_414);
if (lean_is_scalar(x_484)) {
 x_489 = lean_alloc_ctor(0, 1, 0);
} else {
 x_489 = x_484;
}
lean_ctor_set(x_489, 0, x_488);
return x_489;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_413);
lean_dec_ref(x_412);
lean_dec_ref(x_2);
x_490 = lean_ctor_get(x_482, 0);
lean_inc(x_490);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 x_491 = x_482;
} else {
 lean_dec_ref(x_482);
 x_491 = lean_box(0);
}
if (lean_is_scalar(x_491)) {
 x_492 = lean_alloc_ctor(1, 1, 0);
} else {
 x_492 = x_491;
}
lean_ctor_set(x_492, 0, x_490);
return x_492;
}
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_dec(x_413);
lean_dec_ref(x_412);
lean_dec_ref(x_17);
lean_dec(x_6);
lean_dec_ref(x_2);
x_493 = lean_ctor_get(x_477, 0);
lean_inc(x_493);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 x_494 = x_477;
} else {
 lean_dec_ref(x_477);
 x_494 = lean_box(0);
}
if (lean_is_scalar(x_494)) {
 x_495 = lean_alloc_ctor(1, 1, 0);
} else {
 x_495 = x_494;
}
lean_ctor_set(x_495, 0, x_493);
return x_495;
}
}
}
else
{
lean_object* x_496; lean_object* x_497; 
lean_dec_ref(x_411);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_inc_ref(x_412);
x_496 = l_Lean_Meta_mkOfEqTrueCore(x_25, x_412);
x_497 = l_Lean_Meta_Sym_shareCommon___redArg(x_496, x_6);
if (lean_obj_tag(x_497) == 0)
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
lean_dec_ref(x_497);
x_499 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5;
x_500 = lean_array_push(x_499, x_498);
x_501 = l_Lean_Expr_betaRev(x_20, x_500, x_1, x_1);
lean_dec_ref(x_500);
x_502 = l_Lean_Meta_Sym_shareCommonInc___redArg(x_501, x_6);
lean_dec(x_6);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 x_504 = x_502;
} else {
 lean_dec_ref(x_502);
 x_504 = lean_box(0);
}
x_505 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__31;
x_506 = l_Lean_Expr_replaceFn(x_2, x_505);
x_507 = l_Lean_Expr_app___override(x_506, x_412);
if (lean_is_scalar(x_413)) {
 x_508 = lean_alloc_ctor(1, 2, 1);
} else {
 x_508 = x_413;
}
lean_ctor_set(x_508, 0, x_503);
lean_ctor_set(x_508, 1, x_507);
lean_ctor_set_uint8(x_508, sizeof(void*)*2, x_1);
if (lean_is_scalar(x_504)) {
 x_509 = lean_alloc_ctor(0, 1, 0);
} else {
 x_509 = x_504;
}
lean_ctor_set(x_509, 0, x_508);
return x_509;
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; 
lean_dec(x_413);
lean_dec_ref(x_412);
lean_dec_ref(x_2);
x_510 = lean_ctor_get(x_502, 0);
lean_inc(x_510);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 x_511 = x_502;
} else {
 lean_dec_ref(x_502);
 x_511 = lean_box(0);
}
if (lean_is_scalar(x_511)) {
 x_512 = lean_alloc_ctor(1, 1, 0);
} else {
 x_512 = x_511;
}
lean_ctor_set(x_512, 0, x_510);
return x_512;
}
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec(x_413);
lean_dec_ref(x_412);
lean_dec_ref(x_20);
lean_dec(x_6);
lean_dec_ref(x_2);
x_513 = lean_ctor_get(x_497, 0);
lean_inc(x_513);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 x_514 = x_497;
} else {
 lean_dec_ref(x_497);
 x_514 = lean_box(0);
}
if (lean_is_scalar(x_514)) {
 x_515 = lean_alloc_ctor(1, 1, 0);
} else {
 x_515 = x_514;
}
lean_ctor_set(x_515, 0, x_513);
return x_515;
}
}
}
}
}
else
{
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_32;
}
}
}
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_12, 0, x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Expr_getAppNumArgs(x_1);
x_12 = lean_unsigned_to_nat(5u);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_box(x_13);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___boxed), 11, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_17 = l_Lean_Meta_Sym_Simp_propagateOverApplied(x_1, x_16, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_18 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_18, 0, x_13);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cond", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__3;
x_2 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__2;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__5;
x_2 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__2;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cond_false", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cond_true", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cond_cond_congr", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11;
x_2 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10;
x_3 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cond_cond_eq_false", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__13;
x_2 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10;
x_3 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cond_cond_eq_true", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__15;
x_2 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10;
x_3 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_15; uint8_t x_16; 
lean_inc_ref(x_2);
x_15 = l_Lean_Expr_cleanupAnnotations(x_2);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec_ref(x_15);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_14;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_17);
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_14;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_20);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_14;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_23);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_26);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_28 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__1;
x_29 = l_Lean_Expr_isConstOf(x_27, x_28);
if (x_29 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_14;
}
else
{
lean_object* x_30; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_23);
x_30 = lean_sym_simp(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__4;
x_35 = l_Lean_Expr_isConstOf(x_23, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__6;
x_37 = l_Lean_Expr_isConstOf(x_23, x_36);
lean_dec_ref(x_23);
if (x_37 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_ctor_set_uint8(x_32, 0, x_29);
return x_30;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_32);
x_38 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__8;
x_39 = l_Lean_Expr_constLevels_x21(x_27);
lean_dec_ref(x_27);
x_40 = l_Lean_mkConst(x_38, x_39);
lean_inc_ref(x_17);
x_41 = l_Lean_mkApp3(x_40, x_26, x_20, x_17);
x_42 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_42, 0, x_17);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_35);
lean_ctor_set(x_30, 0, x_42);
return x_30;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_free_object(x_32);
lean_dec_ref(x_23);
x_43 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__10;
x_44 = l_Lean_Expr_constLevels_x21(x_27);
lean_dec_ref(x_27);
x_45 = l_Lean_mkConst(x_43, x_44);
lean_inc_ref(x_20);
x_46 = l_Lean_mkApp3(x_45, x_26, x_20, x_17);
x_47 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_47, 0, x_20);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_1);
lean_ctor_set(x_30, 0, x_47);
return x_30;
}
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_32);
x_48 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__4;
x_49 = l_Lean_Expr_isConstOf(x_23, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__6;
x_51 = l_Lean_Expr_isConstOf(x_23, x_50);
lean_dec_ref(x_23);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
x_52 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_52, 0, x_29);
lean_ctor_set(x_30, 0, x_52);
return x_30;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__8;
x_54 = l_Lean_Expr_constLevels_x21(x_27);
lean_dec_ref(x_27);
x_55 = l_Lean_mkConst(x_53, x_54);
lean_inc_ref(x_17);
x_56 = l_Lean_mkApp3(x_55, x_26, x_20, x_17);
x_57 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_57, 0, x_17);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_49);
lean_ctor_set(x_30, 0, x_57);
return x_30;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec_ref(x_23);
x_58 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__10;
x_59 = l_Lean_Expr_constLevels_x21(x_27);
lean_dec_ref(x_27);
x_60 = l_Lean_mkConst(x_58, x_59);
lean_inc_ref(x_20);
x_61 = l_Lean_mkApp3(x_60, x_26, x_20, x_17);
x_62 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_62, 0, x_20);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*2, x_1);
lean_ctor_set(x_30, 0, x_62);
return x_30;
}
}
}
else
{
uint8_t x_63; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
x_63 = !lean_is_exclusive(x_32);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_32, 0);
x_65 = lean_ctor_get(x_32, 1);
x_66 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__4;
x_67 = l_Lean_Expr_isConstOf(x_64, x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__6;
x_69 = l_Lean_Expr_isConstOf(x_64, x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_free_object(x_30);
x_70 = lean_unsigned_to_nat(3u);
x_71 = l_Lean_Expr_getBoundedAppFn(x_70, x_2);
lean_inc_ref(x_64);
x_72 = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(x_71, x_64, x_20, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__12;
x_76 = l_Lean_Expr_replaceFn(x_2, x_75);
x_77 = l_Lean_mkAppB(x_76, x_64, x_65);
lean_ctor_set(x_32, 1, x_77);
lean_ctor_set(x_32, 0, x_74);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_29);
lean_ctor_set(x_72, 0, x_32);
return x_72;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
lean_dec(x_72);
x_79 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__12;
x_80 = l_Lean_Expr_replaceFn(x_2, x_79);
x_81 = l_Lean_mkAppB(x_80, x_64, x_65);
lean_ctor_set(x_32, 1, x_81);
lean_ctor_set(x_32, 0, x_78);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_29);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_32);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_free_object(x_32);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec_ref(x_2);
x_83 = !lean_is_exclusive(x_72);
if (x_83 == 0)
{
return x_72;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_72, 0);
lean_inc(x_84);
lean_dec(x_72);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec_ref(x_64);
lean_dec_ref(x_20);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_86 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__14;
x_87 = l_Lean_Expr_replaceFn(x_2, x_86);
x_88 = l_Lean_Expr_app___override(x_87, x_65);
lean_ctor_set(x_32, 1, x_88);
lean_ctor_set(x_32, 0, x_17);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_67);
return x_30;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec_ref(x_64);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_89 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__16;
x_90 = l_Lean_Expr_replaceFn(x_2, x_89);
x_91 = l_Lean_Expr_app___override(x_90, x_65);
lean_ctor_set(x_32, 1, x_91);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_1);
return x_30;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_92 = lean_ctor_get(x_32, 0);
x_93 = lean_ctor_get(x_32, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_32);
x_94 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__4;
x_95 = l_Lean_Expr_isConstOf(x_92, x_94);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__6;
x_97 = l_Lean_Expr_isConstOf(x_92, x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_free_object(x_30);
x_98 = lean_unsigned_to_nat(3u);
x_99 = l_Lean_Expr_getBoundedAppFn(x_98, x_2);
lean_inc_ref(x_92);
x_100 = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(x_99, x_92, x_20, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__12;
x_104 = l_Lean_Expr_replaceFn(x_2, x_103);
x_105 = l_Lean_mkAppB(x_104, x_92, x_93);
x_106 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_106, 0, x_101);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set_uint8(x_106, sizeof(void*)*2, x_29);
if (lean_is_scalar(x_102)) {
 x_107 = lean_alloc_ctor(0, 1, 0);
} else {
 x_107 = x_102;
}
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec_ref(x_93);
lean_dec_ref(x_92);
lean_dec_ref(x_2);
x_108 = lean_ctor_get(x_100, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 x_109 = x_100;
} else {
 lean_dec_ref(x_100);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec_ref(x_92);
lean_dec_ref(x_20);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_111 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__14;
x_112 = l_Lean_Expr_replaceFn(x_2, x_111);
x_113 = l_Lean_Expr_app___override(x_112, x_93);
x_114 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_114, 0, x_17);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set_uint8(x_114, sizeof(void*)*2, x_95);
lean_ctor_set(x_30, 0, x_114);
return x_30;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec_ref(x_92);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_115 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__16;
x_116 = l_Lean_Expr_replaceFn(x_2, x_115);
x_117 = l_Lean_Expr_app___override(x_116, x_93);
x_118 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_118, 0, x_20);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set_uint8(x_118, sizeof(void*)*2, x_1);
lean_ctor_set(x_30, 0, x_118);
return x_30;
}
}
}
}
else
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_30, 0);
lean_inc(x_119);
lean_dec(x_30);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
if (lean_is_exclusive(x_119)) {
 x_120 = x_119;
} else {
 lean_dec_ref(x_119);
 x_120 = lean_box(0);
}
x_121 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__4;
x_122 = l_Lean_Expr_isConstOf(x_23, x_121);
if (x_122 == 0)
{
lean_object* x_123; uint8_t x_124; 
x_123 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__6;
x_124 = l_Lean_Expr_isConstOf(x_23, x_123);
lean_dec_ref(x_23);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
if (lean_is_scalar(x_120)) {
 x_125 = lean_alloc_ctor(0, 0, 1);
} else {
 x_125 = x_120;
}
lean_ctor_set_uint8(x_125, 0, x_29);
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_120);
x_127 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__8;
x_128 = l_Lean_Expr_constLevels_x21(x_27);
lean_dec_ref(x_27);
x_129 = l_Lean_mkConst(x_127, x_128);
lean_inc_ref(x_17);
x_130 = l_Lean_mkApp3(x_129, x_26, x_20, x_17);
x_131 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_131, 0, x_17);
lean_ctor_set(x_131, 1, x_130);
lean_ctor_set_uint8(x_131, sizeof(void*)*2, x_122);
x_132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_120);
lean_dec_ref(x_23);
x_133 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__10;
x_134 = l_Lean_Expr_constLevels_x21(x_27);
lean_dec_ref(x_27);
x_135 = l_Lean_mkConst(x_133, x_134);
lean_inc_ref(x_20);
x_136 = l_Lean_mkApp3(x_135, x_26, x_20, x_17);
x_137 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_137, 0, x_20);
lean_ctor_set(x_137, 1, x_136);
lean_ctor_set_uint8(x_137, sizeof(void*)*2, x_1);
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
x_139 = lean_ctor_get(x_119, 0);
lean_inc_ref(x_139);
x_140 = lean_ctor_get(x_119, 1);
lean_inc_ref(x_140);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_141 = x_119;
} else {
 lean_dec_ref(x_119);
 x_141 = lean_box(0);
}
x_142 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__4;
x_143 = l_Lean_Expr_isConstOf(x_139, x_142);
if (x_143 == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__6;
x_145 = l_Lean_Expr_isConstOf(x_139, x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_unsigned_to_nat(3u);
x_147 = l_Lean_Expr_getBoundedAppFn(x_146, x_2);
lean_inc_ref(x_139);
x_148 = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte_spec__0_spec__0(x_147, x_139, x_20, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
x_151 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__12;
x_152 = l_Lean_Expr_replaceFn(x_2, x_151);
x_153 = l_Lean_mkAppB(x_152, x_139, x_140);
if (lean_is_scalar(x_141)) {
 x_154 = lean_alloc_ctor(1, 2, 1);
} else {
 x_154 = x_141;
}
lean_ctor_set(x_154, 0, x_149);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set_uint8(x_154, sizeof(void*)*2, x_29);
if (lean_is_scalar(x_150)) {
 x_155 = lean_alloc_ctor(0, 1, 0);
} else {
 x_155 = x_150;
}
lean_ctor_set(x_155, 0, x_154);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec_ref(x_139);
lean_dec_ref(x_2);
x_156 = lean_ctor_get(x_148, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 x_157 = x_148;
} else {
 lean_dec_ref(x_148);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 1, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_156);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec_ref(x_139);
lean_dec_ref(x_20);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_159 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__14;
x_160 = l_Lean_Expr_replaceFn(x_2, x_159);
x_161 = l_Lean_Expr_app___override(x_160, x_140);
if (lean_is_scalar(x_141)) {
 x_162 = lean_alloc_ctor(1, 2, 1);
} else {
 x_162 = x_141;
}
lean_ctor_set(x_162, 0, x_17);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*2, x_143);
x_163 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_163, 0, x_162);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec_ref(x_139);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_164 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__16;
x_165 = l_Lean_Expr_replaceFn(x_2, x_164);
x_166 = l_Lean_Expr_app___override(x_165, x_140);
if (lean_is_scalar(x_141)) {
 x_167 = lean_alloc_ctor(1, 2, 1);
} else {
 x_167 = x_141;
}
lean_ctor_set(x_167, 0, x_20);
lean_ctor_set(x_167, 1, x_166);
lean_ctor_set_uint8(x_167, sizeof(void*)*2, x_1);
x_168 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_168, 0, x_167);
return x_168;
}
}
}
}
else
{
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_30;
}
}
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_12, 0, x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Expr_getAppNumArgs(x_1);
x_12 = lean_unsigned_to_nat(4u);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_box(x_13);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___boxed), 11, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_nat_sub(x_11, x_12);
lean_dec(x_11);
x_17 = l_Lean_Meta_Sym_Simp_propagateOverApplied(x_1, x_16, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_18 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_18, 0, x_13);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_5, x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg(x_1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_2);
x_12 = l_Lean_Meta_reduceRecMatcher_x3f(x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_inc(x_14);
x_15 = l_Lean_Meta_Sym_mkEqRefl(x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = 0;
x_19 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = 0;
x_22 = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_14);
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_13);
x_27 = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch_spec__0___redArg(x_1, x_10);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
if (lean_obj_tag(x_29) == 1)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_31, x_33);
lean_dec(x_31);
x_35 = lean_nat_add(x_34, x_32);
lean_dec(x_32);
x_36 = l_Lean_Meta_Sym_Simp_simpAppArgRange(x_2, x_34, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_35);
lean_dec(x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 1)
{
lean_dec_ref(x_37);
return x_36;
}
else
{
uint8_t x_38; 
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
x_40 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0;
lean_ctor_set(x_36, 0, x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_36);
x_41 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0;
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
else
{
return x_36;
}
}
else
{
lean_object* x_43; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_43 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__1;
lean_ctor_set(x_27, 0, x_43);
return x_27;
}
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_27, 0);
lean_inc(x_44);
lean_dec(x_27);
if (lean_obj_tag(x_44) == 1)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_46, x_48);
lean_dec(x_46);
x_50 = lean_nat_add(x_49, x_47);
lean_dec(x_47);
x_51 = l_Lean_Meta_Sym_Simp_simpAppArgRange(x_2, x_49, x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_50);
lean_dec(x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 1)
{
lean_dec_ref(x_52);
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0;
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 1, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
else
{
return x_51;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_44);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_56 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__1;
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_12);
if (x_58 == 0)
{
return x_12;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_12, 0);
lean_inc(x_59);
lean_dec(x_12);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpControl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isApp(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__1;
x_17 = lean_name_eq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__1;
x_19 = lean_name_eq(x_15, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__1;
x_21 = lean_name_eq(x_15, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch(x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_15);
x_23 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_15);
x_24 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_15);
x_25 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_26 = l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__1;
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_simpControl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Sym_Simp_simpControl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin);
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
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin);
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
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__0);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__1);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__2 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__2);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__3 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__3);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__4 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__4);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__5 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__5);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__6 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__6);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__7 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__7);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__8);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__9);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__10);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__11 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__11);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__12);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__13 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__13);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__14 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__14();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__14);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__15 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__15();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__15);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__16 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__16();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpIte___lam__0___closed__16);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__0);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__1);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__2 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__2);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__3 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__3);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__4);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__5);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__6 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__6);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__7 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__7);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__8 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__8);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__9 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__9);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__10 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__10);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__11);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__12);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__13 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__13);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__14 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__14();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__14);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__15 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__15();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__15);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__16 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__16();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__16);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__17 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__17();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__17);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__18 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__18();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__18);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__19 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__19();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__19);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__20);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__21);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__22 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__22();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__22);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__23 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__23();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__23);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__24);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__25 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__25();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__25);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__26);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__27);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__28 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__28();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__28);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__29);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__30 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__30();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__30);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__31 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__31();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIte___lam__0___closed__31);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__0);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__1);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__2 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__2);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__3 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__3);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__4 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__4);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__5 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__5);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__6 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__6);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__7);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__8 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__8);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__9);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__10 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__10);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__11);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__12 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__12);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__13 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__13);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__14 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__14();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__14);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__15 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__15();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__15);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__16 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__16();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpCond___lam__0___closed__16);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__0);
l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__1 = _init_l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Sym_Simp_ControlFlow_0__Lean_Meta_Sym_Simp_simpMatch___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

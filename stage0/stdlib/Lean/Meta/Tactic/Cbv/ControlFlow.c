// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.ControlFlow
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.Simp.Result import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.Sym.Simp.ControlFlow import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.InferType import Lean.Meta.Sym.Simp.App import Lean.Meta.SynthInstance import Lean.Meta.WHNF import Lean.Meta.AppBuilder import Init.Sym.Lemmas import Lean.Meta.Tactic.Cbv.TheoremsLookup import Lean.Meta.Tactic.Cbv.Opaque import Lean.Meta.Tactic.Cbv.CbvEvalExt import Lean.Compiler.NoncomputableAttr import Init.CbvSimproc import Lean.Meta.Tactic.Cbv.CbvSimproc
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
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_getMatchTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isTrueExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isFalseExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkRflResult(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_project_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_canUnfoldDefault(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_canUnfoldAtMatcher(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_betaRevS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getBoundedAppFn(lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Expr_replaceFn(lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpInterlaced(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpCond___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 237, 71, 156, 244, 3, 80, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ite_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9_value),LEAN_SCALAR_PTR_LITERAL(168, 126, 169, 138, 86, 190, 160, 178)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ite_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__11_value),LEAN_SCALAR_PTR_LITERAL(101, 74, 75, 252, 5, 15, 175, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__12_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ite_true_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 140, 45, 159, 71, 73, 13, 89)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "ite_false_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(132, 158, 180, 207, 199, 71, 79, 30)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(16, 96, 65, 173, 152, 155, 4, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__3_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__4_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__6;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "ite_of_decide_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__11_value),LEAN_SCALAR_PTR_LITERAL(127, 109, 237, 55, 39, 153, 107, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ite_of_decide_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__14_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__13_value),LEAN_SCALAR_PTR_LITERAL(192, 96, 211, 151, 176, 247, 209, 172)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__14_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "ite_of_decide_eq_true_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 197, 90, 170, 26, 195, 233, 177)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "ite_of_decide_eq_false_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(240, 196, 167, 224, 128, 157, 64, 86)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ite_cond_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 115, 5, 135, 85, 70, 205, 95)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__11_value),LEAN_SCALAR_PTR_LITERAL(217, 231, 214, 152, 207, 100, 121, 38)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9_value),LEAN_SCALAR_PTR_LITERAL(28, 219, 17, 217, 43, 100, 109, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "ite_eq_right_of_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(85, 26, 223, 35, 242, 130, 83, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ite_eq_left_of_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(73, 84, 15, 184, 226, 12, 142, 9)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Cbv"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(93, 144, 236, 69, 149, 78, 215, 228)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__9_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ControlFlow"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__9_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__9_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__10_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__9_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(153, 75, 2, 199, 142, 91, 93, 201)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__10_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__10_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__11_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__10_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(252, 60, 118, 117, 62, 213, 206, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__11_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__11_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__12_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__11_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(157, 4, 12, 27, 152, 101, 133, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__12_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__12_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__12_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(245, 145, 82, 72, 75, 94, 216, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__14_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(144, 2, 145, 22, 246, 43, 198, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__14_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__14_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__15_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__15_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__15_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__14_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__15_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(124, 100, 175, 78, 162, 84, 105, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__17_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "simpIteCbv"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__17_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__17_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__17_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(74, 233, 198, 147, 223, 175, 34, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__19_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__19_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__19_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__19_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_19____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "dite_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 79, 213, 134, 118, 203, 8, 228)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "dite_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__2_value),LEAN_SCALAR_PTR_LITERAL(26, 82, 15, 17, 1, 91, 226, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mpr_prop"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__3_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 177, 76, 157, 211, 15, 217, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "dite_true_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(120, 185, 89, 138, 56, 95, 240, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mpr_not"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__3_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5_value),LEAN_SCALAR_PTR_LITERAL(121, 56, 250, 51, 9, 123, 141, 181)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "dite_false_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8_value),LEAN_SCALAR_PTR_LITERAL(200, 44, 51, 241, 184, 46, 57, 25)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "of_decide_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 143, 142, 104, 169, 34, 63, 25)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "of_decide_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__3_value),LEAN_SCALAR_PTR_LITERAL(101, 242, 48, 138, 187, 4, 117, 248)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "dite_cond_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(72, 238, 116, 219, 106, 19, 52, 46)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 21, 178, 198, 97, 164, 246, 137)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 119, 178, 178, 249, 126, 188, 7)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 218, 189, 96, 14, 237, 238, 210)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "dite_eq_right_of_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(181, 72, 248, 145, 136, 9, 228, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "dite_eq_left_of_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(36, 253, 19, 136, 170, 78, 36, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "simpDIteCbv"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(190, 122, 172, 160, 23, 10, 186, 34)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_19____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "decide_isTrue"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(128, 238, 232, 136, 147, 64, 116, 79)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "decide_isFalse"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__3_value),LEAN_SCALAR_PTR_LITERAL(30, 93, 112, 198, 213, 0, 204, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "decide_isTrue_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 46, 253, 225, 97, 126, 88, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "decide_isFalse_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(210, 108, 78, 146, 25, 88, 128, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "decide_eq_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 73, 110, 63, 16, 22, 220, 5)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "congr_simp"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "decide_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 46, 65, 221, 159, 136, 150, 89)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "decide_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(205, 8, 17, 237, 36, 213, 18, 105)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "decide_prop_eq_false"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(55, 242, 168, 209, 35, 165, 174, 215)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "decide_prop_eq_true"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(31, 147, 176, 82, 87, 65, 127, 52)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(91, 57, 77, 17, 146, 195, 162, 163)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "simpDecideCbv"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(115, 206, 175, 80, 231, 183, 173, 95)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__1_value),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_simpCond___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(76, 195, 71, 185, 148, 180, 220, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(30, 114, 151, 242, 65, 185, 169, 185)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "simpCbvCond"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(159, 133, 67, 239, 99, 33, 147, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value),((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_18_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_18____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cbv"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "rewrite"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__0_value),LEAN_SCALAR_PTR_LITERAL(180, 58, 216, 170, 2, 199, 127, 134)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__1_value),LEAN_SCALAR_PTR_LITERAL(174, 58, 109, 183, 100, 138, 243, 210)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "recMatcher:"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\n==>"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 246}, .m_size = 4, .m_capacity = 4, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "simpDecidableRec"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(80, 52, 244, 154, 141, 147, 125, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rec"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(158, 146, 92, 125, 27, 135, 153, 152)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17__value),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 246}, .m_size = 5, .m_capacity = 5, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_19____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeNone___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "controlFlow"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__0_value),LEAN_SCALAR_PTR_LITERAL(180, 58, 216, 170, 2, 199, 127, 134)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__0_value),LEAN_SCALAR_PTR_LITERAL(124, 7, 140, 41, 97, 241, 74, 13)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "match `"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`:"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(lean_object* v_customCanUnfoldPredicate_x3f_1_, uint8_t v_canUnfoldPredicateConfig_2_, lean_object* v_cfg_3_, lean_object* v_info_4_, lean_object* v___y_5_, lean_object* v___y_6_){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = l_Lean_ConstantInfo_name(v_info_4_);
v___x_9_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(v___x_8_, v___y_6_);
lean_dec(v___x_8_);
if (lean_obj_tag(v___x_9_) == 0)
{
lean_object* v_a_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_24_; 
v_a_10_ = lean_ctor_get(v___x_9_, 0);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_24_ == 0)
{
v___x_12_ = v___x_9_;
v_isShared_13_ = v_isSharedCheck_24_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_a_10_);
lean_dec(v___x_9_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_24_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
uint8_t v___x_14_; 
v___x_14_ = lean_unbox(v_a_10_);
lean_dec(v_a_10_);
if (v___x_14_ == 0)
{
lean_del_object(v___x_12_);
if (lean_obj_tag(v_customCanUnfoldPredicate_x3f_1_) == 0)
{
if (v_canUnfoldPredicateConfig_2_ == 0)
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Meta_canUnfoldDefault(v_cfg_3_, v_info_4_, v___y_5_, v___y_6_);
lean_dec_ref(v_info_4_);
lean_dec_ref(v_cfg_3_);
return v___x_15_;
}
else
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Meta_canUnfoldAtMatcher(v_cfg_3_, v_info_4_, v___y_5_, v___y_6_);
lean_dec_ref(v_info_4_);
lean_dec_ref(v_cfg_3_);
return v___x_16_;
}
}
else
{
lean_object* v_val_17_; lean_object* v___x_18_; 
v_val_17_ = lean_ctor_get(v_customCanUnfoldPredicate_x3f_1_, 0);
lean_inc(v_val_17_);
lean_dec_ref_known(v_customCanUnfoldPredicate_x3f_1_, 1);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
v___x_18_ = lean_apply_5(v_val_17_, v_cfg_3_, v_info_4_, v___y_5_, v___y_6_, lean_box(0));
return v___x_18_;
}
}
else
{
uint8_t v___x_19_; lean_object* v___x_20_; lean_object* v___x_22_; 
lean_dec_ref(v_info_4_);
lean_dec_ref(v_cfg_3_);
lean_dec(v_customCanUnfoldPredicate_x3f_1_);
v___x_19_ = 0;
v___x_20_ = lean_box(v___x_19_);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 0, v___x_20_);
v___x_22_ = v___x_12_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v___x_20_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
else
{
lean_dec_ref(v_info_4_);
lean_dec_ref(v_cfg_3_);
lean_dec(v_customCanUnfoldPredicate_x3f_1_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed(lean_object* v_customCanUnfoldPredicate_x3f_25_, lean_object* v_canUnfoldPredicateConfig_26_, lean_object* v_cfg_27_, lean_object* v_info_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_){
_start:
{
uint8_t v_canUnfoldPredicateConfig_boxed_32_; lean_object* v_res_33_; 
v_canUnfoldPredicateConfig_boxed_32_ = lean_unbox(v_canUnfoldPredicateConfig_26_);
v_res_33_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(v_customCanUnfoldPredicate_x3f_25_, v_canUnfoldPredicateConfig_boxed_32_, v_cfg_27_, v_info_28_, v___y_29_, v___y_30_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(lean_object* v_x_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_){
_start:
{
lean_object* v_keyedConfig_40_; uint8_t v_trackZetaDelta_41_; lean_object* v_zetaDeltaSet_42_; lean_object* v_lctx_43_; lean_object* v_localInstances_44_; lean_object* v_defEqCtx_x3f_45_; lean_object* v_synthPendingDepth_46_; lean_object* v_customCanUnfoldPredicate_x3f_47_; uint8_t v_univApprox_48_; uint8_t v_inTypeClassResolution_49_; uint8_t v_cacheInferType_50_; lean_object* v___x_51_; uint8_t v_canUnfoldPredicateConfig_52_; lean_object* v___x_53_; lean_object* v___f_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v_keyedConfig_40_ = lean_ctor_get(v_a_35_, 0);
v_trackZetaDelta_41_ = lean_ctor_get_uint8(v_a_35_, sizeof(void*)*7);
v_zetaDeltaSet_42_ = lean_ctor_get(v_a_35_, 1);
v_lctx_43_ = lean_ctor_get(v_a_35_, 2);
v_localInstances_44_ = lean_ctor_get(v_a_35_, 3);
v_defEqCtx_x3f_45_ = lean_ctor_get(v_a_35_, 4);
v_synthPendingDepth_46_ = lean_ctor_get(v_a_35_, 5);
v_customCanUnfoldPredicate_x3f_47_ = lean_ctor_get(v_a_35_, 6);
v_univApprox_48_ = lean_ctor_get_uint8(v_a_35_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_49_ = lean_ctor_get_uint8(v_a_35_, sizeof(void*)*7 + 2);
v_cacheInferType_50_ = lean_ctor_get_uint8(v_a_35_, sizeof(void*)*7 + 3);
v___x_51_ = l_Lean_Meta_Context_config(v_a_35_);
v_canUnfoldPredicateConfig_52_ = lean_ctor_get_uint8(v___x_51_, 19);
lean_dec_ref(v___x_51_);
v___x_53_ = lean_box(v_canUnfoldPredicateConfig_52_);
lean_inc(v_customCanUnfoldPredicate_x3f_47_);
v___f_54_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_54_, 0, v_customCanUnfoldPredicate_x3f_47_);
lean_closure_set(v___f_54_, 1, v___x_53_);
v___x_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_55_, 0, v___f_54_);
lean_inc(v_synthPendingDepth_46_);
lean_inc(v_defEqCtx_x3f_45_);
lean_inc_ref(v_localInstances_44_);
lean_inc_ref(v_lctx_43_);
lean_inc(v_zetaDeltaSet_42_);
lean_inc_ref(v_keyedConfig_40_);
v___x_56_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_56_, 0, v_keyedConfig_40_);
lean_ctor_set(v___x_56_, 1, v_zetaDeltaSet_42_);
lean_ctor_set(v___x_56_, 2, v_lctx_43_);
lean_ctor_set(v___x_56_, 3, v_localInstances_44_);
lean_ctor_set(v___x_56_, 4, v_defEqCtx_x3f_45_);
lean_ctor_set(v___x_56_, 5, v_synthPendingDepth_46_);
lean_ctor_set(v___x_56_, 6, v___x_55_);
lean_ctor_set_uint8(v___x_56_, sizeof(void*)*7, v_trackZetaDelta_41_);
lean_ctor_set_uint8(v___x_56_, sizeof(void*)*7 + 1, v_univApprox_48_);
lean_ctor_set_uint8(v___x_56_, sizeof(void*)*7 + 2, v_inTypeClassResolution_49_);
lean_ctor_set_uint8(v___x_56_, sizeof(void*)*7 + 3, v_cacheInferType_50_);
lean_inc(v_a_38_);
lean_inc_ref(v_a_37_);
lean_inc(v_a_36_);
v___x_57_ = lean_apply_5(v_x_34_, v___x_56_, v_a_36_, v_a_37_, v_a_38_, lean_box(0));
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___boxed(lean_object* v_x_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v_x_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(lean_object* v_00_u03b1_65_, lean_object* v_x_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v_x_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___boxed(lean_object* v_00_u03b1_73_, lean_object* v_x_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(v_00_u03b1_73_, v_x_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_);
lean_dec(v_a_78_);
lean_dec_ref(v_a_77_);
lean_dec(v_a_76_);
lean_dec_ref(v_a_75_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg___lam__0(lean_object* v_k_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v_b_87_, lean_object* v_c_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v___x_94_; 
lean_inc(v___y_92_);
lean_inc_ref(v___y_91_);
lean_inc(v___y_90_);
lean_inc_ref(v___y_89_);
lean_inc(v___y_86_);
lean_inc_ref(v___y_85_);
lean_inc(v___y_84_);
lean_inc_ref(v___y_83_);
lean_inc(v___y_82_);
v___x_94_ = lean_apply_12(v_k_81_, v_b_87_, v_c_88_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, lean_box(0));
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg___lam__0___boxed(lean_object* v_k_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v_b_101_, lean_object* v_c_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg___lam__0(v_k_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v_b_101_, v_c_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg(lean_object* v_type_109_, lean_object* v_k_110_, uint8_t v_cleanupAnnotations_111_, uint8_t v_whnfType_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v___f_123_; lean_object* v___x_124_; 
lean_inc(v___y_117_);
lean_inc_ref(v___y_116_);
lean_inc(v___y_115_);
lean_inc_ref(v___y_114_);
lean_inc(v___y_113_);
v___f_123_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_123_, 0, v_k_110_);
lean_closure_set(v___f_123_, 1, v___y_113_);
lean_closure_set(v___f_123_, 2, v___y_114_);
lean_closure_set(v___f_123_, 3, v___y_115_);
lean_closure_set(v___f_123_, 4, v___y_116_);
lean_closure_set(v___f_123_, 5, v___y_117_);
v___x_124_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_109_, v___f_123_, v_cleanupAnnotations_111_, v_whnfType_112_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
if (lean_obj_tag(v___x_124_) == 0)
{
return v___x_124_;
}
else
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg___boxed(lean_object* v_type_133_, lean_object* v_k_134_, lean_object* v_cleanupAnnotations_135_, lean_object* v_whnfType_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_147_; uint8_t v_whnfType_boxed_148_; lean_object* v_res_149_; 
v_cleanupAnnotations_boxed_147_ = lean_unbox(v_cleanupAnnotations_135_);
v_whnfType_boxed_148_ = lean_unbox(v_whnfType_136_);
v_res_149_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg(v_type_133_, v_k_134_, v_cleanupAnnotations_boxed_147_, v_whnfType_boxed_148_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0(lean_object* v_00_u03b1_150_, lean_object* v_type_151_, lean_object* v_k_152_, uint8_t v_cleanupAnnotations_153_, uint8_t v_whnfType_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg(v_type_151_, v_k_152_, v_cleanupAnnotations_153_, v_whnfType_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___boxed(lean_object* v_00_u03b1_166_, lean_object* v_type_167_, lean_object* v_k_168_, lean_object* v_cleanupAnnotations_169_, lean_object* v_whnfType_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_181_; uint8_t v_whnfType_boxed_182_; lean_object* v_res_183_; 
v_cleanupAnnotations_boxed_181_ = lean_unbox(v_cleanupAnnotations_169_);
v_whnfType_boxed_182_ = lean_unbox(v_whnfType_170_);
v_res_183_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0(v_00_u03b1_166_, v_type_167_, v_k_168_, v_cleanupAnnotations_boxed_181_, v_whnfType_boxed_182_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(lean_object* v_f_184_, lean_object* v_a_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v___y_194_; lean_object* v___x_197_; uint8_t v_debug_198_; 
v___x_197_ = lean_st_ref_get(v___y_187_);
v_debug_198_ = lean_ctor_get_uint8(v___x_197_, sizeof(void*)*11);
lean_dec(v___x_197_);
if (v_debug_198_ == 0)
{
v___y_194_ = v___y_187_;
goto v___jp_193_;
}
else
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_184_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v___x_200_; 
lean_dec_ref_known(v___x_199_, 1);
v___x_200_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_dec_ref_known(v___x_200_, 1);
v___y_194_ = v___y_187_;
goto v___jp_193_;
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
lean_dec_ref(v_a_185_);
lean_dec_ref(v_f_184_);
v_a_201_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_200_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_200_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
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
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
lean_dec_ref(v_a_185_);
lean_dec_ref(v_f_184_);
v_a_209_ = lean_ctor_get(v___x_199_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_199_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_199_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
v___jp_193_:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = l_Lean_Expr_app___override(v_f_184_, v_a_185_);
v___x_196_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_195_, v___y_194_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_217_, lean_object* v_a_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(v_f_217_, v_a_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1(lean_object* v_args_227_, lean_object* v_endIdx_228_, lean_object* v_b_229_, lean_object* v_i_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
uint8_t v___x_241_; 
v___x_241_ = lean_nat_dec_le(v_endIdx_228_, v_i_230_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = l_Lean_instInhabitedExpr;
v___x_243_ = lean_array_get_borrowed(v___x_242_, v_args_227_, v_i_230_);
lean_inc(v___x_243_);
v___x_244_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(v_b_229_, v___x_243_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_a_245_);
lean_dec_ref_known(v___x_244_, 1);
v___x_246_ = lean_unsigned_to_nat(1u);
v___x_247_ = lean_nat_add(v_i_230_, v___x_246_);
lean_dec(v_i_230_);
v_b_229_ = v_a_245_;
v_i_230_ = v___x_247_;
goto _start;
}
else
{
lean_dec(v_i_230_);
return v___x_244_;
}
}
else
{
lean_object* v___x_249_; 
lean_dec(v_i_230_);
v___x_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_249_, 0, v_b_229_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1___boxed(lean_object* v_args_250_, lean_object* v_endIdx_251_, lean_object* v_b_252_, lean_object* v_i_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1(v_args_250_, v_endIdx_251_, v_b_252_, v_i_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec(v___y_254_);
lean_dec(v_endIdx_251_);
lean_dec_ref(v_args_250_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1(lean_object* v_f_265_, lean_object* v_args_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_278_ = lean_array_get_size(v_args_266_);
v___x_279_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1(v_args_266_, v___x_278_, v_f_265_, v___x_277_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1___boxed(lean_object* v_f_280_, lean_object* v_args_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1(v_f_280_, v_args_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
lean_dec(v___y_282_);
lean_dec_ref(v_args_281_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0(uint8_t v___x_296_, lean_object* v_inst_297_, lean_object* v___x_298_, uint8_t v___x_299_, lean_object* v_vars_300_, lean_object* v_body_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = l_Lean_Expr_cleanupAnnotations(v_body_301_);
v___x_318_ = l_Lean_Expr_isApp(v___x_317_);
if (v___x_318_ == 0)
{
lean_dec_ref(v___x_317_);
goto v___jp_312_;
}
else
{
lean_object* v_arg_319_; lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v_arg_319_ = lean_ctor_get(v___x_317_, 1);
lean_inc_ref(v_arg_319_);
v___x_320_ = l_Lean_Expr_appFnCleanup___redArg(v___x_317_);
v___x_321_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0___closed__1));
v___x_322_ = l_Lean_Expr_isConstOf(v___x_320_, v___x_321_);
lean_dec_ref(v___x_320_);
if (v___x_322_ == 0)
{
lean_dec_ref(v_arg_319_);
goto v___jp_312_;
}
else
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = lean_array_get_size(v_vars_300_);
v___x_324_ = lean_nat_dec_eq(v___x_323_, v___x_298_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec_ref(v_arg_319_);
v___x_325_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_325_, 0, v___x_324_);
lean_ctor_set_uint8(v___x_325_, 1, v___x_324_);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v_inst_297_);
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
else
{
uint8_t v___x_329_; lean_object* v___x_330_; 
lean_dec_ref(v_inst_297_);
v___x_329_ = 1;
v___x_330_ = l_Lean_Meta_mkLambdaFVars(v_vars_300_, v_arg_319_, v___x_296_, v___x_299_, v___x_296_, v___x_299_, v___x_329_, v___y_307_, v___y_308_, v___y_309_, v___y_310_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_339_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_339_ == 0)
{
v___x_333_ = v___x_330_;
v_isShared_334_ = v_isSharedCheck_339_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_a_331_);
lean_dec(v___x_330_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_339_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v_a_331_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 0, v___x_335_);
v___x_337_ = v___x_333_;
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
else
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_347_; 
v_a_340_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_347_ == 0)
{
v___x_342_ = v___x_330_;
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_330_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_347_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
if (v_isShared_343_ == 0)
{
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_a_340_);
v___x_345_ = v_reuseFailAlloc_346_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
return v___x_345_;
}
}
}
}
}
}
v___jp_312_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_313_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_313_, 0, v___x_296_);
lean_ctor_set_uint8(v___x_313_, 1, v___x_296_);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v_inst_297_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0___boxed(lean_object* v___x_348_, lean_object* v_inst_349_, lean_object* v___x_350_, lean_object* v___x_351_, lean_object* v_vars_352_, lean_object* v_body_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
uint8_t v___x_17451__boxed_364_; uint8_t v___x_17453__boxed_365_; lean_object* v_res_366_; 
v___x_17451__boxed_364_ = lean_unbox(v___x_348_);
v___x_17453__boxed_365_ = lean_unbox(v___x_351_);
v_res_366_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0(v___x_17451__boxed_364_, v_inst_349_, v___x_350_, v___x_17453__boxed_365_, v_vars_352_, v_body_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v___y_354_);
lean_dec_ref(v_vars_352_);
lean_dec(v___x_350_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2(lean_object* v_inst_369_, lean_object* v_x_370_, lean_object* v_x_371_, lean_object* v_x_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
if (lean_obj_tag(v_x_370_) == 5)
{
lean_object* v_fn_383_; lean_object* v_arg_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v_fn_383_ = lean_ctor_get(v_x_370_, 0);
lean_inc_ref(v_fn_383_);
v_arg_384_ = lean_ctor_get(v_x_370_, 1);
lean_inc_ref(v_arg_384_);
lean_dec_ref_known(v_x_370_, 2);
v___x_385_ = lean_array_set(v_x_371_, v_x_372_, v_arg_384_);
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_nat_sub(v_x_372_, v___x_386_);
lean_dec(v_x_372_);
v_x_370_ = v_fn_383_;
v_x_371_ = v___x_385_;
v_x_372_ = v___x_387_;
goto _start;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
lean_dec(v_x_372_);
v___x_389_ = lean_array_get_size(v_x_371_);
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = lean_nat_dec_eq(v___x_389_, v___x_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; 
lean_inc(v___y_381_);
lean_inc_ref(v___y_380_);
lean_inc(v___y_379_);
lean_inc_ref(v___y_378_);
lean_inc_ref(v_x_370_);
v___x_392_ = lean_infer_type(v_x_370_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; uint8_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___f_397_; lean_object* v___x_398_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_a_393_);
lean_dec_ref_known(v___x_392_, 1);
v___x_394_ = 1;
v___x_395_ = lean_box(v___x_391_);
v___x_396_ = lean_box(v___x_394_);
lean_inc_ref(v_inst_369_);
v___f_397_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0___boxed), 16, 4);
lean_closure_set(v___f_397_, 0, v___x_395_);
lean_closure_set(v___f_397_, 1, v_inst_369_);
lean_closure_set(v___f_397_, 2, v___x_389_);
lean_closure_set(v___f_397_, 3, v___x_396_);
v___x_398_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg(v_a_393_, v___f_397_, v___x_391_, v___x_394_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_479_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_479_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_479_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_479_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
if (lean_obj_tag(v_a_399_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_405_; 
lean_dec_ref(v_x_371_);
lean_dec_ref(v_x_370_);
lean_dec_ref(v_inst_369_);
v_a_403_ = lean_ctor_get(v_a_399_, 0);
lean_inc(v_a_403_);
lean_dec_ref_known(v_a_399_, 1);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v_a_403_);
v___x_405_ = v___x_401_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_408_; 
lean_del_object(v___x_401_);
v_a_407_ = lean_ctor_get(v_a_399_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v_a_399_, 1);
v___x_408_ = l_Lean_Meta_Sym_shareCommon(v_a_407_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_410_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc_n(v_a_409_, 2);
lean_dec_ref_known(v___x_408_, 1);
v___x_410_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1(v_a_409_, v_x_371_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec_ref(v_x_371_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v___x_412_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_411_);
lean_dec_ref_known(v___x_410_, 1);
v___x_412_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_a_411_, v___x_390_, v___x_389_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_454_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_454_ == 0)
{
v___x_415_ = v___x_412_;
v_isShared_416_ = v_isSharedCheck_454_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_454_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
if (lean_obj_tag(v_a_413_) == 0)
{
lean_object* v___x_417_; lean_object* v___x_419_; 
lean_dec(v_a_409_);
lean_dec_ref(v_x_370_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v_a_413_);
lean_ctor_set(v___x_417_, 1, v_inst_369_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 0, v___x_417_);
v___x_419_ = v___x_415_;
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
else
{
lean_object* v_e_x27_421_; lean_object* v_proof_422_; uint8_t v_done_423_; uint8_t v_contextDependent_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_453_; 
lean_del_object(v___x_415_);
lean_dec_ref(v_inst_369_);
v_e_x27_421_ = lean_ctor_get(v_a_413_, 0);
v_proof_422_ = lean_ctor_get(v_a_413_, 1);
v_done_423_ = lean_ctor_get_uint8(v_a_413_, sizeof(void*)*2);
v_contextDependent_424_ = lean_ctor_get_uint8(v_a_413_, sizeof(void*)*2 + 1);
v_isSharedCheck_453_ = !lean_is_exclusive(v_a_413_);
if (v_isSharedCheck_453_ == 0)
{
v___x_426_ = v_a_413_;
v_isShared_427_ = v_isSharedCheck_453_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_proof_422_);
lean_inc(v_e_x27_421_);
lean_dec(v_a_413_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_453_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_428_ = l_Lean_Expr_getAppNumArgs(v_e_x27_421_);
v___x_429_ = lean_mk_empty_array_with_capacity(v___x_428_);
lean_dec(v___x_428_);
v___x_430_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_x27_421_, v___x_429_);
lean_inc_ref(v___x_430_);
v___x_431_ = l_Lean_Meta_Sym_betaRevS(v_a_409_, v___x_430_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_444_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_444_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_444_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_444_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v_a_432_);
v___x_437_ = v___x_426_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_432_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_proof_422_);
lean_ctor_set_uint8(v_reuseFailAlloc_443_, sizeof(void*)*2, v_done_423_);
lean_ctor_set_uint8(v_reuseFailAlloc_443_, sizeof(void*)*2 + 1, v_contextDependent_424_);
v___x_437_ = v_reuseFailAlloc_443_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_438_ = l_Lean_mkAppRev(v_x_370_, v___x_430_);
lean_dec_ref(v___x_430_);
v___x_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_439_);
v___x_441_ = v___x_434_;
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
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_dec_ref(v___x_430_);
lean_del_object(v___x_426_);
lean_dec_ref(v_proof_422_);
lean_dec_ref(v_x_370_);
v_a_445_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_431_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_431_);
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
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
lean_dec(v_a_409_);
lean_dec_ref(v_x_370_);
lean_dec_ref(v_inst_369_);
v_a_455_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_412_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_412_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
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
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec(v_a_409_);
lean_dec_ref(v_x_370_);
lean_dec_ref(v_inst_369_);
v_a_463_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_410_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_410_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_dec_ref(v_x_371_);
lean_dec_ref(v_x_370_);
lean_dec_ref(v_inst_369_);
v_a_471_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_408_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_408_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec_ref(v_x_371_);
lean_dec_ref(v_x_370_);
lean_dec_ref(v_inst_369_);
v_a_480_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_398_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_398_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec_ref(v_x_371_);
lean_dec_ref(v_x_370_);
lean_dec_ref(v_inst_369_);
v_a_488_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_392_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_392_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec_ref(v_x_371_);
lean_dec_ref(v_x_370_);
v___x_496_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___closed__0));
v___x_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
lean_ctor_set(v___x_497_, 1, v_inst_369_);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___boxed(lean_object* v_inst_499_, lean_object* v_x_500_, lean_object* v_x_501_, lean_object* v_x_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2(v_inst_499_, v_x_500_, v_x_501_, v_x_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
return v_res_513_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance___closed__0(void){
_start:
{
lean_object* v___x_514_; lean_object* v_dummy_515_; 
v___x_514_ = lean_box(0);
v_dummy_515_ = l_Lean_Expr_sort___override(v___x_514_);
return v_dummy_515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance(lean_object* v_inst_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v_dummy_527_; lean_object* v_nargs_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_dummy_527_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance___closed__0, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance___closed__0_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance___closed__0);
v_nargs_528_ = l_Lean_Expr_getAppNumArgs(v_inst_516_);
lean_inc(v_nargs_528_);
v___x_529_ = lean_mk_array(v_nargs_528_, v_dummy_527_);
v___x_530_ = lean_unsigned_to_nat(1u);
v___x_531_ = lean_nat_sub(v_nargs_528_, v___x_530_);
lean_dec(v_nargs_528_);
lean_inc_ref(v_inst_516_);
v___x_532_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2(v_inst_516_, v_inst_516_, v___x_529_, v___x_531_, v_a_517_, v_a_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_, v_a_525_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance___boxed(lean_object* v_inst_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance(v_inst_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2(lean_object* v_f_545_, lean_object* v_a_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(v_f_545_, v_a_546_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___boxed(lean_object* v_f_558_, lean_object* v_a_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2(v_f_558_, v_a_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(lean_object* v_f_596_, lean_object* v_00_u03b1_597_, lean_object* v_c_598_, lean_object* v_inst_599_, lean_object* v_a_600_, lean_object* v_b_601_, lean_object* v_instToMatch_602_, lean_object* v_fallback_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_instToMatch_602_, v_a_610_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
lean_inc(v_a_615_);
lean_dec_ref_known(v___x_614_, 1);
v___x_616_ = l_Lean_Expr_cleanupAnnotations(v_a_615_);
v___x_617_ = l_Lean_Expr_isApp(v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
lean_dec_ref(v___x_616_);
lean_dec_ref(v_b_601_);
lean_dec_ref(v_a_600_);
lean_dec_ref(v_inst_599_);
lean_dec_ref(v_c_598_);
lean_dec_ref(v_00_u03b1_597_);
lean_inc(v_a_612_);
lean_inc_ref(v_a_611_);
lean_inc(v_a_610_);
lean_inc_ref(v_a_609_);
lean_inc(v_a_608_);
lean_inc_ref(v_a_607_);
lean_inc(v_a_606_);
lean_inc_ref(v_a_605_);
lean_inc(v_a_604_);
v___x_618_ = lean_apply_10(v_fallback_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, lean_box(0));
return v___x_618_;
}
else
{
lean_object* v_arg_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_arg_619_ = lean_ctor_get(v___x_616_, 1);
lean_inc_ref(v_arg_619_);
v___x_620_ = l_Lean_Expr_appFnCleanup___redArg(v___x_616_);
v___x_621_ = l_Lean_Expr_isApp(v___x_620_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; 
lean_dec_ref(v___x_620_);
lean_dec_ref(v_arg_619_);
lean_dec_ref(v_b_601_);
lean_dec_ref(v_a_600_);
lean_dec_ref(v_inst_599_);
lean_dec_ref(v_c_598_);
lean_dec_ref(v_00_u03b1_597_);
lean_inc(v_a_612_);
lean_inc_ref(v_a_611_);
lean_inc(v_a_610_);
lean_inc_ref(v_a_609_);
lean_inc(v_a_608_);
lean_inc_ref(v_a_607_);
lean_inc(v_a_606_);
lean_inc_ref(v_a_605_);
lean_inc(v_a_604_);
v___x_622_ = lean_apply_10(v_fallback_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, lean_box(0));
return v___x_622_;
}
else
{
lean_object* v_arg_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v_arg_623_ = lean_ctor_get(v___x_620_, 1);
lean_inc_ref(v_arg_623_);
v___x_624_ = l_Lean_Expr_appFnCleanup___redArg(v___x_620_);
v___x_625_ = l_Lean_Expr_isApp(v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; 
lean_dec_ref(v___x_624_);
lean_dec_ref(v_arg_623_);
lean_dec_ref(v_arg_619_);
lean_dec_ref(v_b_601_);
lean_dec_ref(v_a_600_);
lean_dec_ref(v_inst_599_);
lean_dec_ref(v_c_598_);
lean_dec_ref(v_00_u03b1_597_);
lean_inc(v_a_612_);
lean_inc_ref(v_a_611_);
lean_inc(v_a_610_);
lean_inc_ref(v_a_609_);
lean_inc(v_a_608_);
lean_inc_ref(v_a_607_);
lean_inc(v_a_606_);
lean_inc_ref(v_a_605_);
lean_inc(v_a_604_);
v___x_626_ = lean_apply_10(v_fallback_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, lean_box(0));
return v___x_626_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_627_ = l_Lean_Expr_appFnCleanup___redArg(v___x_624_);
v___x_628_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_629_ = l_Lean_Expr_isConstOf(v___x_627_, v___x_628_);
lean_dec_ref(v___x_627_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; 
lean_dec_ref(v_arg_623_);
lean_dec_ref(v_arg_619_);
lean_dec_ref(v_b_601_);
lean_dec_ref(v_a_600_);
lean_dec_ref(v_inst_599_);
lean_dec_ref(v_c_598_);
lean_dec_ref(v_00_u03b1_597_);
lean_inc(v_a_612_);
lean_inc_ref(v_a_611_);
lean_inc(v_a_610_);
lean_inc_ref(v_a_609_);
lean_inc(v_a_608_);
lean_inc_ref(v_a_607_);
lean_inc(v_a_606_);
lean_inc_ref(v_a_605_);
lean_inc(v_a_604_);
v___x_630_ = lean_apply_10(v_fallback_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, lean_box(0));
return v___x_630_;
}
else
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_623_, v_a_610_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_659_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_659_ == 0)
{
v___x_634_ = v___x_631_;
v_isShared_635_ = v_isSharedCheck_659_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_659_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_636_ = l_Lean_Expr_cleanupAnnotations(v_a_632_);
v___x_637_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_638_ = l_Lean_Expr_isConstOf(v___x_636_, v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_639_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_640_ = l_Lean_Expr_isConstOf(v___x_636_, v___x_639_);
lean_dec_ref(v___x_636_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
lean_del_object(v___x_634_);
lean_dec_ref(v_arg_619_);
lean_dec_ref(v_b_601_);
lean_dec_ref(v_a_600_);
lean_dec_ref(v_inst_599_);
lean_dec_ref(v_c_598_);
lean_dec_ref(v_00_u03b1_597_);
lean_inc(v_a_612_);
lean_inc_ref(v_a_611_);
lean_inc(v_a_610_);
lean_inc_ref(v_a_609_);
lean_inc(v_a_608_);
lean_inc_ref(v_a_607_);
lean_inc(v_a_606_);
lean_inc_ref(v_a_605_);
lean_inc(v_a_604_);
v___x_641_ = lean_apply_10(v_fallback_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, lean_box(0));
return v___x_641_;
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_648_; 
lean_dec_ref(v_fallback_603_);
v___x_642_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__10));
v___x_643_ = l_Lean_Expr_constLevels_x21(v_f_596_);
v___x_644_ = l_Lean_mkConst(v___x_642_, v___x_643_);
lean_inc_ref(v_a_600_);
v___x_645_ = l_Lean_mkApp6(v___x_644_, v_00_u03b1_597_, v_c_598_, v_inst_599_, v_a_600_, v_b_601_, v_arg_619_);
v___x_646_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_646_, 0, v_a_600_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
lean_ctor_set_uint8(v___x_646_, sizeof(void*)*2, v___x_638_);
lean_ctor_set_uint8(v___x_646_, sizeof(void*)*2 + 1, v___x_638_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_646_);
v___x_648_ = v___x_634_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
lean_dec_ref(v___x_636_);
lean_dec_ref(v_fallback_603_);
v___x_650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__12));
v___x_651_ = l_Lean_Expr_constLevels_x21(v_f_596_);
v___x_652_ = l_Lean_mkConst(v___x_650_, v___x_651_);
lean_inc_ref(v_b_601_);
v___x_653_ = l_Lean_mkApp6(v___x_652_, v_00_u03b1_597_, v_c_598_, v_inst_599_, v_a_600_, v_b_601_, v_arg_619_);
v___x_654_ = 0;
v___x_655_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_655_, 0, v_b_601_);
lean_ctor_set(v___x_655_, 1, v___x_653_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*2, v___x_654_);
lean_ctor_set_uint8(v___x_655_, sizeof(void*)*2 + 1, v___x_654_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_655_);
v___x_657_ = v___x_634_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec_ref(v_arg_619_);
lean_dec_ref(v_fallback_603_);
lean_dec_ref(v_b_601_);
lean_dec_ref(v_a_600_);
lean_dec_ref(v_inst_599_);
lean_dec_ref(v_c_598_);
lean_dec_ref(v_00_u03b1_597_);
v_a_660_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_631_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_631_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
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
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
lean_dec_ref(v_fallback_603_);
lean_dec_ref(v_b_601_);
lean_dec_ref(v_a_600_);
lean_dec_ref(v_inst_599_);
lean_dec_ref(v_c_598_);
lean_dec_ref(v_00_u03b1_597_);
v_a_668_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_614_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_614_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___boxed(lean_object** _args){
lean_object* v_f_676_ = _args[0];
lean_object* v_00_u03b1_677_ = _args[1];
lean_object* v_c_678_ = _args[2];
lean_object* v_inst_679_ = _args[3];
lean_object* v_a_680_ = _args[4];
lean_object* v_b_681_ = _args[5];
lean_object* v_instToMatch_682_ = _args[6];
lean_object* v_fallback_683_ = _args[7];
lean_object* v_a_684_ = _args[8];
lean_object* v_a_685_ = _args[9];
lean_object* v_a_686_ = _args[10];
lean_object* v_a_687_ = _args[11];
lean_object* v_a_688_ = _args[12];
lean_object* v_a_689_ = _args[13];
lean_object* v_a_690_ = _args[14];
lean_object* v_a_691_ = _args[15];
lean_object* v_a_692_ = _args[16];
lean_object* v_a_693_ = _args[17];
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(v_f_676_, v_00_u03b1_677_, v_c_678_, v_inst_679_, v_a_680_, v_b_681_, v_instToMatch_682_, v_fallback_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
lean_dec(v_a_692_);
lean_dec_ref(v_a_691_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
lean_dec_ref(v_a_687_);
lean_dec(v_a_686_);
lean_dec_ref(v_a_685_);
lean_dec(v_a_684_);
lean_dec_ref(v_f_676_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(lean_object* v_f_705_, lean_object* v_00_u03b1_706_, lean_object* v_c_707_, lean_object* v_inst_708_, lean_object* v_a_709_, lean_object* v_b_710_, lean_object* v_c_x27_711_, lean_object* v_h_712_, lean_object* v_inst_x27_713_, lean_object* v_fallback_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_x27_713_, v_a_721_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
v___x_727_ = l_Lean_Expr_cleanupAnnotations(v_a_726_);
v___x_728_ = l_Lean_Expr_isApp(v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
lean_dec_ref(v___x_727_);
lean_dec_ref(v_h_712_);
lean_dec_ref(v_c_x27_711_);
lean_dec_ref(v_b_710_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_inst_708_);
lean_dec_ref(v_c_707_);
lean_dec_ref(v_00_u03b1_706_);
lean_inc(v_a_723_);
lean_inc_ref(v_a_722_);
lean_inc(v_a_721_);
lean_inc_ref(v_a_720_);
lean_inc(v_a_719_);
lean_inc_ref(v_a_718_);
lean_inc(v_a_717_);
lean_inc_ref(v_a_716_);
lean_inc(v_a_715_);
v___x_729_ = lean_apply_10(v_fallback_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, lean_box(0));
return v___x_729_;
}
else
{
lean_object* v_arg_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v_arg_730_ = lean_ctor_get(v___x_727_, 1);
lean_inc_ref(v_arg_730_);
v___x_731_ = l_Lean_Expr_appFnCleanup___redArg(v___x_727_);
v___x_732_ = l_Lean_Expr_isApp(v___x_731_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; 
lean_dec_ref(v___x_731_);
lean_dec_ref(v_arg_730_);
lean_dec_ref(v_h_712_);
lean_dec_ref(v_c_x27_711_);
lean_dec_ref(v_b_710_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_inst_708_);
lean_dec_ref(v_c_707_);
lean_dec_ref(v_00_u03b1_706_);
lean_inc(v_a_723_);
lean_inc_ref(v_a_722_);
lean_inc(v_a_721_);
lean_inc_ref(v_a_720_);
lean_inc(v_a_719_);
lean_inc_ref(v_a_718_);
lean_inc(v_a_717_);
lean_inc_ref(v_a_716_);
lean_inc(v_a_715_);
v___x_733_ = lean_apply_10(v_fallback_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, lean_box(0));
return v___x_733_;
}
else
{
lean_object* v_arg_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v_arg_734_ = lean_ctor_get(v___x_731_, 1);
lean_inc_ref(v_arg_734_);
v___x_735_ = l_Lean_Expr_appFnCleanup___redArg(v___x_731_);
v___x_736_ = l_Lean_Expr_isApp(v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
lean_dec_ref(v___x_735_);
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_730_);
lean_dec_ref(v_h_712_);
lean_dec_ref(v_c_x27_711_);
lean_dec_ref(v_b_710_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_inst_708_);
lean_dec_ref(v_c_707_);
lean_dec_ref(v_00_u03b1_706_);
lean_inc(v_a_723_);
lean_inc_ref(v_a_722_);
lean_inc(v_a_721_);
lean_inc_ref(v_a_720_);
lean_inc(v_a_719_);
lean_inc_ref(v_a_718_);
lean_inc(v_a_717_);
lean_inc_ref(v_a_716_);
lean_inc(v_a_715_);
v___x_737_ = lean_apply_10(v_fallback_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, lean_box(0));
return v___x_737_;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_738_ = l_Lean_Expr_appFnCleanup___redArg(v___x_735_);
v___x_739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_740_ = l_Lean_Expr_isConstOf(v___x_738_, v___x_739_);
lean_dec_ref(v___x_738_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_730_);
lean_dec_ref(v_h_712_);
lean_dec_ref(v_c_x27_711_);
lean_dec_ref(v_b_710_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_inst_708_);
lean_dec_ref(v_c_707_);
lean_dec_ref(v_00_u03b1_706_);
lean_inc(v_a_723_);
lean_inc_ref(v_a_722_);
lean_inc(v_a_721_);
lean_inc_ref(v_a_720_);
lean_inc(v_a_719_);
lean_inc_ref(v_a_718_);
lean_inc(v_a_717_);
lean_inc_ref(v_a_716_);
lean_inc(v_a_715_);
v___x_741_ = lean_apply_10(v_fallback_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, lean_box(0));
return v___x_741_;
}
else
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_734_, v_a_721_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_770_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_770_ == 0)
{
v___x_745_ = v___x_742_;
v_isShared_746_ = v_isSharedCheck_770_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_742_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_770_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_747_ = l_Lean_Expr_cleanupAnnotations(v_a_743_);
v___x_748_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_749_ = l_Lean_Expr_isConstOf(v___x_747_, v___x_748_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_750_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_751_ = l_Lean_Expr_isConstOf(v___x_747_, v___x_750_);
lean_dec_ref(v___x_747_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; 
lean_del_object(v___x_745_);
lean_dec_ref(v_arg_730_);
lean_dec_ref(v_h_712_);
lean_dec_ref(v_c_x27_711_);
lean_dec_ref(v_b_710_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_inst_708_);
lean_dec_ref(v_c_707_);
lean_dec_ref(v_00_u03b1_706_);
lean_inc(v_a_723_);
lean_inc_ref(v_a_722_);
lean_inc(v_a_721_);
lean_inc_ref(v_a_720_);
lean_inc(v_a_719_);
lean_inc_ref(v_a_718_);
lean_inc(v_a_717_);
lean_inc_ref(v_a_716_);
lean_inc(v_a_715_);
v___x_752_ = lean_apply_10(v_fallback_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, lean_box(0));
return v___x_752_;
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
lean_dec_ref(v_fallback_714_);
v___x_753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1));
v___x_754_ = l_Lean_Expr_constLevels_x21(v_f_705_);
v___x_755_ = l_Lean_mkConst(v___x_753_, v___x_754_);
lean_inc_ref(v_a_709_);
v___x_756_ = l_Lean_mkApp8(v___x_755_, v_00_u03b1_706_, v_c_707_, v_inst_708_, v_a_709_, v_b_710_, v_c_x27_711_, v_h_712_, v_arg_730_);
v___x_757_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_757_, 0, v_a_709_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
lean_ctor_set_uint8(v___x_757_, sizeof(void*)*2, v___x_749_);
lean_ctor_set_uint8(v___x_757_, sizeof(void*)*2 + 1, v___x_749_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_757_);
v___x_759_ = v___x_745_;
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
else
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
lean_dec_ref(v___x_747_);
lean_dec_ref(v_fallback_714_);
v___x_761_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3));
v___x_762_ = l_Lean_Expr_constLevels_x21(v_f_705_);
v___x_763_ = l_Lean_mkConst(v___x_761_, v___x_762_);
lean_inc_ref(v_b_710_);
v___x_764_ = l_Lean_mkApp8(v___x_763_, v_00_u03b1_706_, v_c_707_, v_inst_708_, v_a_709_, v_b_710_, v_c_x27_711_, v_h_712_, v_arg_730_);
v___x_765_ = 0;
v___x_766_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_766_, 0, v_b_710_);
lean_ctor_set(v___x_766_, 1, v___x_764_);
lean_ctor_set_uint8(v___x_766_, sizeof(void*)*2, v___x_765_);
lean_ctor_set_uint8(v___x_766_, sizeof(void*)*2 + 1, v___x_765_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_766_);
v___x_768_ = v___x_745_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v_arg_730_);
lean_dec_ref(v_fallback_714_);
lean_dec_ref(v_h_712_);
lean_dec_ref(v_c_x27_711_);
lean_dec_ref(v_b_710_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_inst_708_);
lean_dec_ref(v_c_707_);
lean_dec_ref(v_00_u03b1_706_);
v_a_771_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_742_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_742_);
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
}
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec_ref(v_fallback_714_);
lean_dec_ref(v_h_712_);
lean_dec_ref(v_c_x27_711_);
lean_dec_ref(v_b_710_);
lean_dec_ref(v_a_709_);
lean_dec_ref(v_inst_708_);
lean_dec_ref(v_c_707_);
lean_dec_ref(v_00_u03b1_706_);
v_a_779_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_725_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_725_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_787_ = _args[0];
lean_object* v_00_u03b1_788_ = _args[1];
lean_object* v_c_789_ = _args[2];
lean_object* v_inst_790_ = _args[3];
lean_object* v_a_791_ = _args[4];
lean_object* v_b_792_ = _args[5];
lean_object* v_c_x27_793_ = _args[6];
lean_object* v_h_794_ = _args[7];
lean_object* v_inst_x27_795_ = _args[8];
lean_object* v_fallback_796_ = _args[9];
lean_object* v_a_797_ = _args[10];
lean_object* v_a_798_ = _args[11];
lean_object* v_a_799_ = _args[12];
lean_object* v_a_800_ = _args[13];
lean_object* v_a_801_ = _args[14];
lean_object* v_a_802_ = _args[15];
lean_object* v_a_803_ = _args[16];
lean_object* v_a_804_ = _args[17];
lean_object* v_a_805_ = _args[18];
lean_object* v_a_806_ = _args[19];
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(v_f_787_, v_00_u03b1_788_, v_c_789_, v_inst_790_, v_a_791_, v_b_792_, v_c_x27_793_, v_h_794_, v_inst_x27_795_, v_fallback_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_f_787_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0(uint8_t v___x_808_, lean_object* v_inst_809_, lean_object* v___x_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_keyedConfig_816_; uint8_t v_trackZetaDelta_817_; lean_object* v_zetaDeltaSet_818_; lean_object* v_lctx_819_; lean_object* v_localInstances_820_; lean_object* v_defEqCtx_x3f_821_; lean_object* v_synthPendingDepth_822_; lean_object* v_customCanUnfoldPredicate_x3f_823_; uint8_t v_univApprox_824_; uint8_t v_inTypeClassResolution_825_; uint8_t v_cacheInferType_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_835_; 
v_keyedConfig_816_ = lean_ctor_get(v___y_811_, 0);
v_trackZetaDelta_817_ = lean_ctor_get_uint8(v___y_811_, sizeof(void*)*7);
v_zetaDeltaSet_818_ = lean_ctor_get(v___y_811_, 1);
v_lctx_819_ = lean_ctor_get(v___y_811_, 2);
v_localInstances_820_ = lean_ctor_get(v___y_811_, 3);
v_defEqCtx_x3f_821_ = lean_ctor_get(v___y_811_, 4);
v_synthPendingDepth_822_ = lean_ctor_get(v___y_811_, 5);
v_customCanUnfoldPredicate_x3f_823_ = lean_ctor_get(v___y_811_, 6);
v_univApprox_824_ = lean_ctor_get_uint8(v___y_811_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_825_ = lean_ctor_get_uint8(v___y_811_, sizeof(void*)*7 + 2);
v_cacheInferType_826_ = lean_ctor_get_uint8(v___y_811_, sizeof(void*)*7 + 3);
v_isSharedCheck_835_ = !lean_is_exclusive(v___y_811_);
if (v_isSharedCheck_835_ == 0)
{
v___x_828_ = v___y_811_;
v_isShared_829_ = v_isSharedCheck_835_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_823_);
lean_inc(v_synthPendingDepth_822_);
lean_inc(v_defEqCtx_x3f_821_);
lean_inc(v_localInstances_820_);
lean_inc(v_lctx_819_);
lean_inc(v_zetaDeltaSet_818_);
lean_inc(v_keyedConfig_816_);
lean_dec(v___y_811_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_835_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_830_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_808_, v_keyedConfig_816_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v___x_830_);
v___x_832_ = v___x_828_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_zetaDeltaSet_818_);
lean_ctor_set(v_reuseFailAlloc_834_, 2, v_lctx_819_);
lean_ctor_set(v_reuseFailAlloc_834_, 3, v_localInstances_820_);
lean_ctor_set(v_reuseFailAlloc_834_, 4, v_defEqCtx_x3f_821_);
lean_ctor_set(v_reuseFailAlloc_834_, 5, v_synthPendingDepth_822_);
lean_ctor_set(v_reuseFailAlloc_834_, 6, v_customCanUnfoldPredicate_x3f_823_);
lean_ctor_set_uint8(v_reuseFailAlloc_834_, sizeof(void*)*7, v_trackZetaDelta_817_);
lean_ctor_set_uint8(v_reuseFailAlloc_834_, sizeof(void*)*7 + 1, v_univApprox_824_);
lean_ctor_set_uint8(v_reuseFailAlloc_834_, sizeof(void*)*7 + 2, v_inTypeClassResolution_825_);
lean_ctor_set_uint8(v_reuseFailAlloc_834_, sizeof(void*)*7 + 3, v_cacheInferType_826_);
v___x_832_ = v_reuseFailAlloc_834_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_Meta_project_x3f(v_inst_809_, v___x_810_, v___x_832_, v___y_812_, v___y_813_, v___y_814_);
lean_dec_ref(v___x_832_);
return v___x_833_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0___boxed(lean_object* v___x_836_, lean_object* v_inst_837_, lean_object* v___x_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
uint8_t v___x_15465__boxed_844_; lean_object* v_res_845_; 
v___x_15465__boxed_844_ = lean_unbox(v___x_836_);
v_res_845_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0(v___x_15465__boxed_844_, v_inst_837_, v___x_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec(v___x_838_);
return v_res_845_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_850_ = lean_box(0);
v___x_851_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__1));
v___x_852_ = l_Lean_mkConst(v___x_851_, v___x_850_);
return v___x_852_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__6(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_unsigned_to_nat(1u);
v___x_859_ = l_Lean_Level_ofNat(v___x_858_);
return v___x_859_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__7(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_860_ = lean_box(0);
v___x_861_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__6, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__6_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__6);
v___x_862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v___x_860_);
return v___x_862_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_863_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__7, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__7);
v___x_864_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__5));
v___x_865_ = l_Lean_Expr_const___override(v___x_864_, v___x_863_);
return v___x_865_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_868_ = lean_box(0);
v___x_869_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__9));
v___x_870_ = l_Lean_mkConst(v___x_869_, v___x_868_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(lean_object* v_f_881_, lean_object* v_00_u03b1_882_, lean_object* v_c_883_, lean_object* v_inst_884_, lean_object* v_a_885_, lean_object* v_b_886_, lean_object* v_fallback_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v___x_898_; uint8_t v___x_899_; lean_object* v___x_900_; lean_object* v___f_901_; lean_object* v___x_902_; 
v___x_898_ = lean_unsigned_to_nat(0u);
v___x_899_ = 5;
v___x_900_ = lean_box(v___x_899_);
lean_inc_ref(v_inst_884_);
v___f_901_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0___boxed), 8, 3);
lean_closure_set(v___f_901_, 0, v___x_900_);
lean_closure_set(v___f_901_, 1, v_inst_884_);
lean_closure_set(v___f_901_, 2, v___x_898_);
v___x_902_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_901_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref_known(v___x_902_, 1);
if (lean_obj_tag(v_a_903_) == 0)
{
lean_object* v___x_904_; 
lean_inc(v_a_896_);
lean_inc_ref(v_a_895_);
lean_inc(v_a_894_);
lean_inc_ref(v_a_893_);
lean_inc(v_a_892_);
lean_inc_ref(v_a_891_);
lean_inc(v_a_890_);
lean_inc_ref(v_a_889_);
lean_inc(v_a_888_);
lean_inc_ref(v_inst_884_);
v___x_904_ = lean_sym_simp(v_inst_884_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v___x_904_, 1);
if (lean_obj_tag(v_a_905_) == 0)
{
uint8_t v_contextDependent_906_; lean_object* v___x_907_; 
v_contextDependent_906_ = lean_ctor_get_uint8(v_a_905_, 1);
lean_dec_ref_known(v_a_905_, 0);
lean_inc_ref(v_inst_884_);
v___x_907_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(v_f_881_, v_00_u03b1_882_, v_c_883_, v_inst_884_, v_a_885_, v_b_886_, v_inst_884_, v_fallback_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; uint8_t v___y_910_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
if (v_contextDependent_906_ == 0)
{
lean_dec(v_a_908_);
return v___x_907_;
}
else
{
if (lean_obj_tag(v_a_908_) == 0)
{
uint8_t v_contextDependent_920_; 
v_contextDependent_920_ = lean_ctor_get_uint8(v_a_908_, 1);
v___y_910_ = v_contextDependent_920_;
goto v___jp_909_;
}
else
{
uint8_t v_contextDependent_921_; 
v_contextDependent_921_ = lean_ctor_get_uint8(v_a_908_, sizeof(void*)*2 + 1);
v___y_910_ = v_contextDependent_921_;
goto v___jp_909_;
}
}
v___jp_909_:
{
if (v___y_910_ == 0)
{
lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_918_; 
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; 
v_unused_919_ = lean_ctor_get(v___x_907_, 0);
lean_dec(v_unused_919_);
v___x_912_ = v___x_907_;
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
else
{
lean_dec(v___x_907_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_918_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_914_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_908_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_914_);
v___x_916_ = v___x_912_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
else
{
lean_dec(v_a_908_);
return v___x_907_;
}
}
}
else
{
return v___x_907_;
}
}
else
{
lean_object* v_e_x27_922_; uint8_t v_contextDependent_923_; lean_object* v___x_924_; 
v_e_x27_922_ = lean_ctor_get(v_a_905_, 0);
lean_inc_ref(v_e_x27_922_);
v_contextDependent_923_ = lean_ctor_get_uint8(v_a_905_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_905_, 2);
v___x_924_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(v_f_881_, v_00_u03b1_882_, v_c_883_, v_inst_884_, v_a_885_, v_b_886_, v_e_x27_922_, v_fallback_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; uint8_t v___y_927_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
if (v_contextDependent_923_ == 0)
{
lean_dec(v_a_925_);
return v___x_924_;
}
else
{
if (lean_obj_tag(v_a_925_) == 0)
{
uint8_t v_contextDependent_937_; 
v_contextDependent_937_ = lean_ctor_get_uint8(v_a_925_, 1);
v___y_927_ = v_contextDependent_937_;
goto v___jp_926_;
}
else
{
uint8_t v_contextDependent_938_; 
v_contextDependent_938_ = lean_ctor_get_uint8(v_a_925_, sizeof(void*)*2 + 1);
v___y_927_ = v_contextDependent_938_;
goto v___jp_926_;
}
}
v___jp_926_:
{
if (v___y_927_ == 0)
{
lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_935_; 
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_935_ == 0)
{
lean_object* v_unused_936_; 
v_unused_936_ = lean_ctor_get(v___x_924_, 0);
lean_dec(v_unused_936_);
v___x_929_ = v___x_924_;
v_isShared_930_ = v_isSharedCheck_935_;
goto v_resetjp_928_;
}
else
{
lean_dec(v___x_924_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_935_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_931_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_925_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_931_);
v___x_933_ = v___x_929_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
else
{
lean_dec(v_a_925_);
return v___x_924_;
}
}
}
else
{
return v___x_924_;
}
}
}
else
{
lean_dec_ref(v_fallback_887_);
lean_dec_ref(v_b_886_);
lean_dec_ref(v_a_885_);
lean_dec_ref(v_inst_884_);
lean_dec_ref(v_c_883_);
lean_dec_ref(v_00_u03b1_882_);
return v___x_904_;
}
}
else
{
lean_object* v_val_939_; lean_object* v___x_940_; 
v_val_939_ = lean_ctor_get(v_a_903_, 0);
lean_inc(v_val_939_);
lean_dec_ref_known(v_a_903_, 1);
v___x_940_ = l_Lean_Meta_Sym_shareCommonInc(v_val_939_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc_n(v_a_941_, 3);
lean_dec_ref_known(v___x_940_, 1);
v___x_942_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2);
v___x_943_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8);
v___x_944_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10);
v___x_945_ = l_Lean_mkAppB(v___x_943_, v___x_944_, v_a_941_);
lean_inc(v_a_896_);
lean_inc_ref(v_a_895_);
lean_inc(v_a_894_);
lean_inc_ref(v_a_893_);
lean_inc(v_a_892_);
lean_inc_ref(v_a_891_);
lean_inc(v_a_890_);
lean_inc_ref(v_a_889_);
lean_inc(v_a_888_);
v___x_946_ = lean_sym_simp(v_a_941_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; uint8_t v___x_948_; lean_object* v_e_x27_950_; lean_object* v_proof_951_; uint8_t v_contextDependent_952_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref_known(v___x_946_, 1);
v___x_948_ = 0;
if (lean_obj_tag(v_a_947_) == 0)
{
uint8_t v_contextDependent_989_; 
v_contextDependent_989_ = lean_ctor_get_uint8(v_a_947_, 1);
lean_dec_ref_known(v_a_947_, 0);
v_e_x27_950_ = v_a_941_;
v_proof_951_ = v___x_945_;
v_contextDependent_952_ = v_contextDependent_989_;
goto v___jp_949_;
}
else
{
lean_object* v_e_x27_990_; lean_object* v_proof_991_; uint8_t v_contextDependent_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_e_x27_990_ = lean_ctor_get(v_a_947_, 0);
lean_inc_ref_n(v_e_x27_990_, 2);
v_proof_991_ = lean_ctor_get(v_a_947_, 1);
lean_inc_ref(v_proof_991_);
v_contextDependent_992_ = lean_ctor_get_uint8(v_a_947_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_947_, 2);
lean_inc_ref(v_inst_884_);
lean_inc_ref(v_c_883_);
v___x_993_ = l_Lean_mkAppB(v___x_942_, v_c_883_, v_inst_884_);
v___x_994_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___x_993_, v_a_941_, v___x_945_, v_e_x27_990_, v_proof_991_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_994_, 1);
v_e_x27_950_ = v_e_x27_990_;
v_proof_951_ = v_a_995_;
v_contextDependent_952_ = v_contextDependent_992_;
goto v___jp_949_;
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec_ref(v_e_x27_990_);
lean_dec_ref(v_fallback_887_);
lean_dec_ref(v_b_886_);
lean_dec_ref(v_a_885_);
lean_dec_ref(v_inst_884_);
lean_dec_ref(v_c_883_);
lean_dec_ref(v_00_u03b1_882_);
v_a_996_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_994_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_994_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
v___jp_949_:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_x27_950_, v_a_894_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_980_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_980_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_980_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_980_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_958_ = l_Lean_Expr_cleanupAnnotations(v_a_954_);
v___x_959_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_960_ = l_Lean_Expr_isConstOf(v___x_958_, v___x_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_961_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_962_ = l_Lean_Expr_isConstOf(v___x_958_, v___x_961_);
lean_dec_ref(v___x_958_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
lean_del_object(v___x_956_);
lean_dec_ref(v_proof_951_);
lean_dec_ref(v_b_886_);
lean_dec_ref(v_a_885_);
lean_dec_ref(v_inst_884_);
lean_dec_ref(v_c_883_);
lean_dec_ref(v_00_u03b1_882_);
lean_inc(v_a_896_);
lean_inc_ref(v_a_895_);
lean_inc(v_a_894_);
lean_inc_ref(v_a_893_);
lean_inc(v_a_892_);
lean_inc_ref(v_a_891_);
lean_inc(v_a_890_);
lean_inc_ref(v_a_889_);
lean_inc(v_a_888_);
v___x_963_ = lean_apply_10(v_fallback_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, lean_box(0));
return v___x_963_;
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
lean_dec_ref(v_fallback_887_);
v___x_964_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__12));
v___x_965_ = l_Lean_Expr_constLevels_x21(v_f_881_);
v___x_966_ = l_Lean_mkConst(v___x_964_, v___x_965_);
lean_inc_ref(v_a_885_);
v___x_967_ = l_Lean_mkApp6(v___x_966_, v_00_u03b1_882_, v_c_883_, v_inst_884_, v_a_885_, v_b_886_, v_proof_951_);
v___x_968_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_968_, 0, v_a_885_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
lean_ctor_set_uint8(v___x_968_, sizeof(void*)*2, v___x_948_);
lean_ctor_set_uint8(v___x_968_, sizeof(void*)*2 + 1, v_contextDependent_952_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_968_);
v___x_970_ = v___x_956_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_978_; 
lean_dec_ref(v___x_958_);
lean_dec_ref(v_fallback_887_);
v___x_972_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__14));
v___x_973_ = l_Lean_Expr_constLevels_x21(v_f_881_);
v___x_974_ = l_Lean_mkConst(v___x_972_, v___x_973_);
lean_inc_ref(v_b_886_);
v___x_975_ = l_Lean_mkApp6(v___x_974_, v_00_u03b1_882_, v_c_883_, v_inst_884_, v_a_885_, v_b_886_, v_proof_951_);
v___x_976_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_976_, 0, v_b_886_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
lean_ctor_set_uint8(v___x_976_, sizeof(void*)*2, v___x_948_);
lean_ctor_set_uint8(v___x_976_, sizeof(void*)*2 + 1, v_contextDependent_952_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_976_);
v___x_978_ = v___x_956_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec_ref(v_proof_951_);
lean_dec_ref(v_fallback_887_);
lean_dec_ref(v_b_886_);
lean_dec_ref(v_a_885_);
lean_dec_ref(v_inst_884_);
lean_dec_ref(v_c_883_);
lean_dec_ref(v_00_u03b1_882_);
v_a_981_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_953_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_953_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_945_);
lean_dec(v_a_941_);
lean_dec_ref(v_fallback_887_);
lean_dec_ref(v_b_886_);
lean_dec_ref(v_a_885_);
lean_dec_ref(v_inst_884_);
lean_dec_ref(v_c_883_);
lean_dec_ref(v_00_u03b1_882_);
return v___x_946_;
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v_fallback_887_);
lean_dec_ref(v_b_886_);
lean_dec_ref(v_a_885_);
lean_dec_ref(v_inst_884_);
lean_dec_ref(v_c_883_);
lean_dec_ref(v_00_u03b1_882_);
v_a_1004_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_940_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_940_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
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
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_dec_ref(v_fallback_887_);
lean_dec_ref(v_b_886_);
lean_dec_ref(v_a_885_);
lean_dec_ref(v_inst_884_);
lean_dec_ref(v_c_883_);
lean_dec_ref(v_00_u03b1_882_);
v_a_1012_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_902_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_902_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___boxed(lean_object** _args){
lean_object* v_f_1020_ = _args[0];
lean_object* v_00_u03b1_1021_ = _args[1];
lean_object* v_c_1022_ = _args[2];
lean_object* v_inst_1023_ = _args[3];
lean_object* v_a_1024_ = _args[4];
lean_object* v_b_1025_ = _args[5];
lean_object* v_fallback_1026_ = _args[6];
lean_object* v_a_1027_ = _args[7];
lean_object* v_a_1028_ = _args[8];
lean_object* v_a_1029_ = _args[9];
lean_object* v_a_1030_ = _args[10];
lean_object* v_a_1031_ = _args[11];
lean_object* v_a_1032_ = _args[12];
lean_object* v_a_1033_ = _args[13];
lean_object* v_a_1034_ = _args[14];
lean_object* v_a_1035_ = _args[15];
lean_object* v_a_1036_ = _args[16];
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v_f_1020_, v_00_u03b1_1021_, v_c_1022_, v_inst_1023_, v_a_1024_, v_b_1025_, v_fallback_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_f_1020_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0(uint8_t v___x_1038_, lean_object* v_inst_x27_1039_, lean_object* v___x_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_keyedConfig_1046_; uint8_t v_trackZetaDelta_1047_; lean_object* v_zetaDeltaSet_1048_; lean_object* v_lctx_1049_; lean_object* v_localInstances_1050_; lean_object* v_defEqCtx_x3f_1051_; lean_object* v_synthPendingDepth_1052_; lean_object* v_customCanUnfoldPredicate_x3f_1053_; uint8_t v_univApprox_1054_; uint8_t v_inTypeClassResolution_1055_; uint8_t v_cacheInferType_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1065_; 
v_keyedConfig_1046_ = lean_ctor_get(v___y_1041_, 0);
v_trackZetaDelta_1047_ = lean_ctor_get_uint8(v___y_1041_, sizeof(void*)*7);
v_zetaDeltaSet_1048_ = lean_ctor_get(v___y_1041_, 1);
v_lctx_1049_ = lean_ctor_get(v___y_1041_, 2);
v_localInstances_1050_ = lean_ctor_get(v___y_1041_, 3);
v_defEqCtx_x3f_1051_ = lean_ctor_get(v___y_1041_, 4);
v_synthPendingDepth_1052_ = lean_ctor_get(v___y_1041_, 5);
v_customCanUnfoldPredicate_x3f_1053_ = lean_ctor_get(v___y_1041_, 6);
v_univApprox_1054_ = lean_ctor_get_uint8(v___y_1041_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1055_ = lean_ctor_get_uint8(v___y_1041_, sizeof(void*)*7 + 2);
v_cacheInferType_1056_ = lean_ctor_get_uint8(v___y_1041_, sizeof(void*)*7 + 3);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___y_1041_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1058_ = v___y_1041_;
v_isShared_1059_ = v_isSharedCheck_1065_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_1053_);
lean_inc(v_synthPendingDepth_1052_);
lean_inc(v_defEqCtx_x3f_1051_);
lean_inc(v_localInstances_1050_);
lean_inc(v_lctx_1049_);
lean_inc(v_zetaDeltaSet_1048_);
lean_inc(v_keyedConfig_1046_);
lean_dec(v___y_1041_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1065_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1060_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1038_, v_keyedConfig_1046_);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v___x_1060_);
v___x_1062_ = v___x_1058_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1060_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_zetaDeltaSet_1048_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v_lctx_1049_);
lean_ctor_set(v_reuseFailAlloc_1064_, 3, v_localInstances_1050_);
lean_ctor_set(v_reuseFailAlloc_1064_, 4, v_defEqCtx_x3f_1051_);
lean_ctor_set(v_reuseFailAlloc_1064_, 5, v_synthPendingDepth_1052_);
lean_ctor_set(v_reuseFailAlloc_1064_, 6, v_customCanUnfoldPredicate_x3f_1053_);
lean_ctor_set_uint8(v_reuseFailAlloc_1064_, sizeof(void*)*7, v_trackZetaDelta_1047_);
lean_ctor_set_uint8(v_reuseFailAlloc_1064_, sizeof(void*)*7 + 1, v_univApprox_1054_);
lean_ctor_set_uint8(v_reuseFailAlloc_1064_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1055_);
lean_ctor_set_uint8(v_reuseFailAlloc_1064_, sizeof(void*)*7 + 3, v_cacheInferType_1056_);
v___x_1062_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_Meta_project_x3f(v_inst_x27_1039_, v___x_1040_, v___x_1062_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec_ref(v___x_1062_);
return v___x_1063_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0___boxed(lean_object* v___x_1066_, lean_object* v_inst_x27_1067_, lean_object* v___x_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
uint8_t v___x_15465__boxed_1074_; lean_object* v_res_1075_; 
v___x_15465__boxed_1074_ = lean_unbox(v___x_1066_);
v_res_1075_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0(v___x_15465__boxed_1074_, v_inst_x27_1067_, v___x_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec(v___x_1068_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr(lean_object* v_f_1086_, lean_object* v_00_u03b1_1087_, lean_object* v_c_1088_, lean_object* v_inst_1089_, lean_object* v_a_1090_, lean_object* v_b_1091_, lean_object* v_c_x27_1092_, lean_object* v_h_1093_, lean_object* v_inst_x27_1094_, lean_object* v_fallback_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v___x_1106_; uint8_t v___x_1107_; lean_object* v___x_1108_; lean_object* v___f_1109_; lean_object* v___x_1110_; 
v___x_1106_ = lean_unsigned_to_nat(0u);
v___x_1107_ = 5;
v___x_1108_ = lean_box(v___x_1107_);
lean_inc_ref(v_inst_x27_1094_);
v___f_1109_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1109_, 0, v___x_1108_);
lean_closure_set(v___f_1109_, 1, v_inst_x27_1094_);
lean_closure_set(v___f_1109_, 2, v___x_1106_);
v___x_1110_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_1109_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc(v_a_1111_);
lean_dec_ref_known(v___x_1110_, 1);
if (lean_obj_tag(v_a_1111_) == 0)
{
lean_object* v___x_1112_; 
lean_inc(v_a_1104_);
lean_inc_ref(v_a_1103_);
lean_inc(v_a_1102_);
lean_inc_ref(v_a_1101_);
lean_inc(v_a_1100_);
lean_inc_ref(v_a_1099_);
lean_inc(v_a_1098_);
lean_inc_ref(v_a_1097_);
lean_inc(v_a_1096_);
lean_inc_ref(v_inst_x27_1094_);
v___x_1112_ = lean_sym_simp(v_inst_x27_1094_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v___x_1112_, 1);
if (lean_obj_tag(v_a_1113_) == 0)
{
uint8_t v_contextDependent_1114_; lean_object* v___x_1115_; 
v_contextDependent_1114_ = lean_ctor_get_uint8(v_a_1113_, 1);
lean_dec_ref_known(v_a_1113_, 0);
v___x_1115_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(v_f_1086_, v_00_u03b1_1087_, v_c_1088_, v_inst_1089_, v_a_1090_, v_b_1091_, v_c_x27_1092_, v_h_1093_, v_inst_x27_1094_, v_fallback_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; uint8_t v___y_1118_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
if (v_contextDependent_1114_ == 0)
{
lean_dec(v_a_1116_);
return v___x_1115_;
}
else
{
if (lean_obj_tag(v_a_1116_) == 0)
{
uint8_t v_contextDependent_1128_; 
v_contextDependent_1128_ = lean_ctor_get_uint8(v_a_1116_, 1);
v___y_1118_ = v_contextDependent_1128_;
goto v___jp_1117_;
}
else
{
uint8_t v_contextDependent_1129_; 
v_contextDependent_1129_ = lean_ctor_get_uint8(v_a_1116_, sizeof(void*)*2 + 1);
v___y_1118_ = v_contextDependent_1129_;
goto v___jp_1117_;
}
}
v___jp_1117_:
{
if (v___y_1118_ == 0)
{
lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1126_; 
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; 
v_unused_1127_ = lean_ctor_get(v___x_1115_, 0);
lean_dec(v_unused_1127_);
v___x_1120_ = v___x_1115_;
v_isShared_1121_ = v_isSharedCheck_1126_;
goto v_resetjp_1119_;
}
else
{
lean_dec(v___x_1115_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1126_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v___x_1124_; 
v___x_1122_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1116_);
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
}
else
{
lean_dec(v_a_1116_);
return v___x_1115_;
}
}
}
else
{
return v___x_1115_;
}
}
else
{
lean_object* v_e_x27_1130_; uint8_t v_contextDependent_1131_; lean_object* v___x_1132_; 
lean_dec_ref(v_inst_x27_1094_);
v_e_x27_1130_ = lean_ctor_get(v_a_1113_, 0);
lean_inc_ref(v_e_x27_1130_);
v_contextDependent_1131_ = lean_ctor_get_uint8(v_a_1113_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1113_, 2);
v___x_1132_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(v_f_1086_, v_00_u03b1_1087_, v_c_1088_, v_inst_1089_, v_a_1090_, v_b_1091_, v_c_x27_1092_, v_h_1093_, v_e_x27_1130_, v_fallback_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v_a_1133_; uint8_t v___y_1135_; 
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc(v_a_1133_);
if (v_contextDependent_1131_ == 0)
{
lean_dec(v_a_1133_);
return v___x_1132_;
}
else
{
if (lean_obj_tag(v_a_1133_) == 0)
{
uint8_t v_contextDependent_1145_; 
v_contextDependent_1145_ = lean_ctor_get_uint8(v_a_1133_, 1);
v___y_1135_ = v_contextDependent_1145_;
goto v___jp_1134_;
}
else
{
uint8_t v_contextDependent_1146_; 
v_contextDependent_1146_ = lean_ctor_get_uint8(v_a_1133_, sizeof(void*)*2 + 1);
v___y_1135_ = v_contextDependent_1146_;
goto v___jp_1134_;
}
}
v___jp_1134_:
{
if (v___y_1135_ == 0)
{
lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1143_; 
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; 
v_unused_1144_ = lean_ctor_get(v___x_1132_, 0);
lean_dec(v_unused_1144_);
v___x_1137_ = v___x_1132_;
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
else
{
lean_dec(v___x_1132_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1143_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1139_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1133_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 0, v___x_1139_);
v___x_1141_ = v___x_1137_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
else
{
lean_dec(v_a_1133_);
return v___x_1132_;
}
}
}
else
{
return v___x_1132_;
}
}
}
else
{
lean_dec_ref(v_fallback_1095_);
lean_dec_ref(v_inst_x27_1094_);
lean_dec_ref(v_h_1093_);
lean_dec_ref(v_c_x27_1092_);
lean_dec_ref(v_b_1091_);
lean_dec_ref(v_a_1090_);
lean_dec_ref(v_inst_1089_);
lean_dec_ref(v_c_1088_);
lean_dec_ref(v_00_u03b1_1087_);
return v___x_1112_;
}
}
else
{
lean_object* v_val_1147_; lean_object* v___x_1148_; 
v_val_1147_ = lean_ctor_get(v_a_1111_, 0);
lean_inc(v_val_1147_);
lean_dec_ref_known(v_a_1111_, 1);
v___x_1148_ = l_Lean_Meta_Sym_shareCommonInc(v_val_1147_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc_n(v_a_1149_, 3);
lean_dec_ref_known(v___x_1148_, 1);
v___x_1150_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2);
v___x_1151_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8);
v___x_1152_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10);
v___x_1153_ = l_Lean_mkAppB(v___x_1151_, v___x_1152_, v_a_1149_);
lean_inc(v_a_1104_);
lean_inc_ref(v_a_1103_);
lean_inc(v_a_1102_);
lean_inc_ref(v_a_1101_);
lean_inc(v_a_1100_);
lean_inc_ref(v_a_1099_);
lean_inc(v_a_1098_);
lean_inc_ref(v_a_1097_);
lean_inc(v_a_1096_);
v___x_1154_ = lean_sym_simp(v_a_1149_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; uint8_t v___x_1156_; lean_object* v_e_x27_1158_; lean_object* v_proof_1159_; uint8_t v_contextDependent_1160_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1154_, 1);
v___x_1156_ = 0;
if (lean_obj_tag(v_a_1155_) == 0)
{
uint8_t v_contextDependent_1197_; 
v_contextDependent_1197_ = lean_ctor_get_uint8(v_a_1155_, 1);
lean_dec_ref_known(v_a_1155_, 0);
v_e_x27_1158_ = v_a_1149_;
v_proof_1159_ = v___x_1153_;
v_contextDependent_1160_ = v_contextDependent_1197_;
goto v___jp_1157_;
}
else
{
lean_object* v_e_x27_1198_; lean_object* v_proof_1199_; uint8_t v_contextDependent_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v_e_x27_1198_ = lean_ctor_get(v_a_1155_, 0);
lean_inc_ref_n(v_e_x27_1198_, 2);
v_proof_1199_ = lean_ctor_get(v_a_1155_, 1);
lean_inc_ref(v_proof_1199_);
v_contextDependent_1200_ = lean_ctor_get_uint8(v_a_1155_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1155_, 2);
lean_inc_ref(v_inst_x27_1094_);
lean_inc_ref(v_c_x27_1092_);
v___x_1201_ = l_Lean_mkAppB(v___x_1150_, v_c_x27_1092_, v_inst_x27_1094_);
v___x_1202_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___x_1201_, v_a_1149_, v___x_1153_, v_e_x27_1198_, v_proof_1199_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
lean_dec_ref_known(v___x_1202_, 1);
v_e_x27_1158_ = v_e_x27_1198_;
v_proof_1159_ = v_a_1203_;
v_contextDependent_1160_ = v_contextDependent_1200_;
goto v___jp_1157_;
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec_ref(v_e_x27_1198_);
lean_dec_ref(v_fallback_1095_);
lean_dec_ref(v_inst_x27_1094_);
lean_dec_ref(v_h_1093_);
lean_dec_ref(v_c_x27_1092_);
lean_dec_ref(v_b_1091_);
lean_dec_ref(v_a_1090_);
lean_dec_ref(v_inst_1089_);
lean_dec_ref(v_c_1088_);
lean_dec_ref(v_00_u03b1_1087_);
v_a_1204_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1202_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1202_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
v___jp_1157_:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_x27_1158_, v_a_1102_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1188_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1164_ = v___x_1161_;
v_isShared_1165_ = v_isSharedCheck_1188_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1161_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1188_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; uint8_t v___x_1168_; 
v___x_1166_ = l_Lean_Expr_cleanupAnnotations(v_a_1162_);
v___x_1167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_1168_ = l_Lean_Expr_isConstOf(v___x_1166_, v___x_1167_);
if (v___x_1168_ == 0)
{
lean_object* v___x_1169_; uint8_t v___x_1170_; 
v___x_1169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_1170_ = l_Lean_Expr_isConstOf(v___x_1166_, v___x_1169_);
lean_dec_ref(v___x_1166_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; 
lean_del_object(v___x_1164_);
lean_dec_ref(v_proof_1159_);
lean_dec_ref(v_inst_x27_1094_);
lean_dec_ref(v_h_1093_);
lean_dec_ref(v_c_x27_1092_);
lean_dec_ref(v_b_1091_);
lean_dec_ref(v_a_1090_);
lean_dec_ref(v_inst_1089_);
lean_dec_ref(v_c_1088_);
lean_dec_ref(v_00_u03b1_1087_);
lean_inc(v_a_1104_);
lean_inc_ref(v_a_1103_);
lean_inc(v_a_1102_);
lean_inc_ref(v_a_1101_);
lean_inc(v_a_1100_);
lean_inc_ref(v_a_1099_);
lean_inc(v_a_1098_);
lean_inc_ref(v_a_1097_);
lean_inc(v_a_1096_);
v___x_1171_ = lean_apply_10(v_fallback_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, lean_box(0));
return v___x_1171_;
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1178_; 
lean_dec_ref(v_fallback_1095_);
v___x_1172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__1));
v___x_1173_ = l_Lean_Expr_constLevels_x21(v_f_1086_);
v___x_1174_ = l_Lean_mkConst(v___x_1172_, v___x_1173_);
lean_inc_ref(v_a_1090_);
v___x_1175_ = l_Lean_mkApp9(v___x_1174_, v_00_u03b1_1087_, v_c_1088_, v_inst_1089_, v_a_1090_, v_b_1091_, v_c_x27_1092_, v_h_1093_, v_inst_x27_1094_, v_proof_1159_);
v___x_1176_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1176_, 0, v_a_1090_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
lean_ctor_set_uint8(v___x_1176_, sizeof(void*)*2, v___x_1156_);
lean_ctor_set_uint8(v___x_1176_, sizeof(void*)*2 + 1, v_contextDependent_1160_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1176_);
v___x_1178_ = v___x_1164_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
else
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1186_; 
lean_dec_ref(v___x_1166_);
lean_dec_ref(v_fallback_1095_);
v___x_1180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__3));
v___x_1181_ = l_Lean_Expr_constLevels_x21(v_f_1086_);
v___x_1182_ = l_Lean_mkConst(v___x_1180_, v___x_1181_);
lean_inc_ref(v_b_1091_);
v___x_1183_ = l_Lean_mkApp9(v___x_1182_, v_00_u03b1_1087_, v_c_1088_, v_inst_1089_, v_a_1090_, v_b_1091_, v_c_x27_1092_, v_h_1093_, v_inst_x27_1094_, v_proof_1159_);
v___x_1184_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1184_, 0, v_b_1091_);
lean_ctor_set(v___x_1184_, 1, v___x_1183_);
lean_ctor_set_uint8(v___x_1184_, sizeof(void*)*2, v___x_1156_);
lean_ctor_set_uint8(v___x_1184_, sizeof(void*)*2 + 1, v_contextDependent_1160_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1184_);
v___x_1186_ = v___x_1164_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec_ref(v_proof_1159_);
lean_dec_ref(v_fallback_1095_);
lean_dec_ref(v_inst_x27_1094_);
lean_dec_ref(v_h_1093_);
lean_dec_ref(v_c_x27_1092_);
lean_dec_ref(v_b_1091_);
lean_dec_ref(v_a_1090_);
lean_dec_ref(v_inst_1089_);
lean_dec_ref(v_c_1088_);
lean_dec_ref(v_00_u03b1_1087_);
v_a_1189_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1161_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1161_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1153_);
lean_dec(v_a_1149_);
lean_dec_ref(v_fallback_1095_);
lean_dec_ref(v_inst_x27_1094_);
lean_dec_ref(v_h_1093_);
lean_dec_ref(v_c_x27_1092_);
lean_dec_ref(v_b_1091_);
lean_dec_ref(v_a_1090_);
lean_dec_ref(v_inst_1089_);
lean_dec_ref(v_c_1088_);
lean_dec_ref(v_00_u03b1_1087_);
return v___x_1154_;
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec_ref(v_fallback_1095_);
lean_dec_ref(v_inst_x27_1094_);
lean_dec_ref(v_h_1093_);
lean_dec_ref(v_c_x27_1092_);
lean_dec_ref(v_b_1091_);
lean_dec_ref(v_a_1090_);
lean_dec_ref(v_inst_1089_);
lean_dec_ref(v_c_1088_);
lean_dec_ref(v_00_u03b1_1087_);
v_a_1212_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1148_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1148_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec_ref(v_fallback_1095_);
lean_dec_ref(v_inst_x27_1094_);
lean_dec_ref(v_h_1093_);
lean_dec_ref(v_c_x27_1092_);
lean_dec_ref(v_b_1091_);
lean_dec_ref(v_a_1090_);
lean_dec_ref(v_inst_1089_);
lean_dec_ref(v_c_1088_);
lean_dec_ref(v_00_u03b1_1087_);
v_a_1220_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1110_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1110_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_1228_ = _args[0];
lean_object* v_00_u03b1_1229_ = _args[1];
lean_object* v_c_1230_ = _args[2];
lean_object* v_inst_1231_ = _args[3];
lean_object* v_a_1232_ = _args[4];
lean_object* v_b_1233_ = _args[5];
lean_object* v_c_x27_1234_ = _args[6];
lean_object* v_h_1235_ = _args[7];
lean_object* v_inst_x27_1236_ = _args[8];
lean_object* v_fallback_1237_ = _args[9];
lean_object* v_a_1238_ = _args[10];
lean_object* v_a_1239_ = _args[11];
lean_object* v_a_1240_ = _args[12];
lean_object* v_a_1241_ = _args[13];
lean_object* v_a_1242_ = _args[14];
lean_object* v_a_1243_ = _args[15];
lean_object* v_a_1244_ = _args[16];
lean_object* v_a_1245_ = _args[17];
lean_object* v_a_1246_ = _args[18];
lean_object* v_a_1247_ = _args[19];
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr(v_f_1228_, v_00_u03b1_1229_, v_c_1230_, v_inst_1231_, v_a_1232_, v_b_1233_, v_c_x27_1234_, v_h_1235_, v_inst_x27_1236_, v_fallback_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_);
lean_dec(v_a_1246_);
lean_dec_ref(v_a_1245_);
lean_dec(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec_ref(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec_ref(v_f_1228_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0(lean_object* v___x_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1249_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed(lean_object* v___x_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0(v___x_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg(lean_object* v_f_1273_, lean_object* v_a_u2081_1274_, lean_object* v_a_u2082_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(v_f_1273_, v_a_u2081_1274_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1285_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1283_, 1);
v___x_1285_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(v_a_1284_, v_a_u2082_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
return v___x_1285_;
}
else
{
lean_dec_ref(v_a_u2082_1275_);
return v___x_1283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_1286_, lean_object* v_a_u2081_1287_, lean_object* v_a_u2082_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg(v_f_1286_, v_a_u2081_1287_, v_a_u2082_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(lean_object* v_f_1297_, lean_object* v_a_u2081_1298_, lean_object* v_a_u2082_1299_, lean_object* v_a_u2083_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg(v_f_1297_, v_a_u2081_1298_, v_a_u2082_1299_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1313_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref_known(v___x_1311_, 1);
v___x_1313_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(v_a_1312_, v_a_u2083_1300_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
return v___x_1313_;
}
else
{
lean_dec_ref(v_a_u2083_1300_);
return v___x_1311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___boxed(lean_object* v_f_1314_, lean_object* v_a_u2081_1315_, lean_object* v_a_u2082_1316_, lean_object* v_a_u2083_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(v_f_1314_, v_a_u2081_1315_, v_a_u2082_1316_, v_a_u2083_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
lean_dec(v___y_1318_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(lean_object* v_f_1329_, lean_object* v_a_u2081_1330_, lean_object* v_a_u2082_1331_, lean_object* v_a_u2083_1332_, lean_object* v_a_u2084_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(v_f_1329_, v_a_u2081_1330_, v_a_u2082_1331_, v_a_u2083_1332_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v_a_1345_; lean_object* v___x_1346_; 
v_a_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_a_1345_);
lean_dec_ref_known(v___x_1344_, 1);
v___x_1346_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(v_a_1345_, v_a_u2084_1333_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
return v___x_1346_;
}
else
{
lean_dec_ref(v_a_u2084_1333_);
return v___x_1344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0___boxed(lean_object* v_f_1347_, lean_object* v_a_u2081_1348_, lean_object* v_a_u2082_1349_, lean_object* v_a_u2083_1350_, lean_object* v_a_u2084_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v_f_1347_, v_a_u2081_1348_, v_a_u2082_1349_, v_a_u2083_1350_, v_a_u2084_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2(lean_object* v___x_1368_, lean_object* v_e_x27_1369_, lean_object* v_snd_1370_, lean_object* v_arg_1371_, lean_object* v_arg_1372_, lean_object* v_e_1373_, lean_object* v_proof_1374_, uint8_t v___x_1375_, uint8_t v_contextDependent_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v___x_1387_; 
lean_inc_ref(v_snd_1370_);
lean_inc_ref(v_e_x27_1369_);
v___x_1387_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v___x_1368_, v_e_x27_1369_, v_snd_1370_, v_arg_1371_, v_arg_1372_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1399_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1390_ = v___x_1387_;
v_isShared_1391_ = v_isSharedCheck_1399_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1387_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1399_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1392_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1));
v___x_1393_ = l_Lean_Expr_replaceFn(v_e_1373_, v___x_1392_);
v___x_1394_ = l_Lean_mkApp3(v___x_1393_, v_e_x27_1369_, v_snd_1370_, v_proof_1374_);
v___x_1395_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1395_, 0, v_a_1388_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
lean_ctor_set_uint8(v___x_1395_, sizeof(void*)*2, v___x_1375_);
lean_ctor_set_uint8(v___x_1395_, sizeof(void*)*2 + 1, v_contextDependent_1376_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1395_);
v___x_1397_ = v___x_1390_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec_ref(v_proof_1374_);
lean_dec_ref(v_e_1373_);
lean_dec_ref(v_snd_1370_);
lean_dec_ref(v_e_x27_1369_);
v_a_1400_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1387_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1387_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___boxed(lean_object** _args){
lean_object* v___x_1408_ = _args[0];
lean_object* v_e_x27_1409_ = _args[1];
lean_object* v_snd_1410_ = _args[2];
lean_object* v_arg_1411_ = _args[3];
lean_object* v_arg_1412_ = _args[4];
lean_object* v_e_1413_ = _args[5];
lean_object* v_proof_1414_ = _args[6];
lean_object* v___x_1415_ = _args[7];
lean_object* v_contextDependent_1416_ = _args[8];
lean_object* v___y_1417_ = _args[9];
lean_object* v___y_1418_ = _args[10];
lean_object* v___y_1419_ = _args[11];
lean_object* v___y_1420_ = _args[12];
lean_object* v___y_1421_ = _args[13];
lean_object* v___y_1422_ = _args[14];
lean_object* v___y_1423_ = _args[15];
lean_object* v___y_1424_ = _args[16];
lean_object* v___y_1425_ = _args[17];
lean_object* v___y_1426_ = _args[18];
_start:
{
uint8_t v___x_14775__boxed_1427_; uint8_t v_contextDependent_14776__boxed_1428_; lean_object* v_res_1429_; 
v___x_14775__boxed_1427_ = lean_unbox(v___x_1415_);
v_contextDependent_14776__boxed_1428_ = lean_unbox(v_contextDependent_1416_);
v_res_1429_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2(v___x_1408_, v_e_x27_1409_, v_snd_1410_, v_arg_1411_, v_arg_1412_, v_e_1413_, v_proof_1414_, v___x_14775__boxed_1427_, v_contextDependent_14776__boxed_1428_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1(uint8_t v___x_1443_, lean_object* v_e_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___x_1458_; uint8_t v___x_1459_; 
lean_inc_ref(v_e_1444_);
v___x_1458_ = l_Lean_Expr_cleanupAnnotations(v_e_1444_);
v___x_1459_ = l_Lean_Expr_isApp(v___x_1458_);
if (v___x_1459_ == 0)
{
lean_dec_ref(v___x_1458_);
lean_dec_ref(v_e_1444_);
goto v___jp_1455_;
}
else
{
lean_object* v_arg_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v_arg_1460_ = lean_ctor_get(v___x_1458_, 1);
lean_inc_ref(v_arg_1460_);
v___x_1461_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1458_);
v___x_1462_ = l_Lean_Expr_isApp(v___x_1461_);
if (v___x_1462_ == 0)
{
lean_dec_ref(v___x_1461_);
lean_dec_ref(v_arg_1460_);
lean_dec_ref(v_e_1444_);
goto v___jp_1455_;
}
else
{
lean_object* v_arg_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; 
v_arg_1463_ = lean_ctor_get(v___x_1461_, 1);
lean_inc_ref(v_arg_1463_);
v___x_1464_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1461_);
v___x_1465_ = l_Lean_Expr_isApp(v___x_1464_);
if (v___x_1465_ == 0)
{
lean_dec_ref(v___x_1464_);
lean_dec_ref(v_arg_1463_);
lean_dec_ref(v_arg_1460_);
lean_dec_ref(v_e_1444_);
goto v___jp_1455_;
}
else
{
lean_object* v_arg_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v_arg_1466_ = lean_ctor_get(v___x_1464_, 1);
lean_inc_ref(v_arg_1466_);
v___x_1467_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1464_);
v___x_1468_ = l_Lean_Expr_isApp(v___x_1467_);
if (v___x_1468_ == 0)
{
lean_dec_ref(v___x_1467_);
lean_dec_ref(v_arg_1466_);
lean_dec_ref(v_arg_1463_);
lean_dec_ref(v_arg_1460_);
lean_dec_ref(v_e_1444_);
goto v___jp_1455_;
}
else
{
lean_object* v_arg_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; 
v_arg_1469_ = lean_ctor_get(v___x_1467_, 1);
lean_inc_ref(v_arg_1469_);
v___x_1470_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1467_);
v___x_1471_ = l_Lean_Expr_isApp(v___x_1470_);
if (v___x_1471_ == 0)
{
lean_dec_ref(v___x_1470_);
lean_dec_ref(v_arg_1469_);
lean_dec_ref(v_arg_1466_);
lean_dec_ref(v_arg_1463_);
lean_dec_ref(v_arg_1460_);
lean_dec_ref(v_e_1444_);
goto v___jp_1455_;
}
else
{
lean_object* v_arg_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; 
v_arg_1472_ = lean_ctor_get(v___x_1470_, 1);
lean_inc_ref(v_arg_1472_);
v___x_1473_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1470_);
v___x_1474_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1));
v___x_1475_ = l_Lean_Expr_isConstOf(v___x_1473_, v___x_1474_);
if (v___x_1475_ == 0)
{
lean_dec_ref(v___x_1473_);
lean_dec_ref(v_arg_1472_);
lean_dec_ref(v_arg_1469_);
lean_dec_ref(v_arg_1466_);
lean_dec_ref(v_arg_1463_);
lean_dec_ref(v_arg_1460_);
lean_dec_ref(v_e_1444_);
goto v___jp_1455_;
}
else
{
lean_object* v___x_1476_; 
lean_inc(v___y_1453_);
lean_inc_ref(v___y_1452_);
lean_inc(v___y_1451_);
lean_inc_ref(v___y_1450_);
lean_inc(v___y_1449_);
lean_inc_ref(v___y_1448_);
lean_inc(v___y_1447_);
lean_inc_ref(v___y_1446_);
lean_inc(v___y_1445_);
lean_inc_ref(v_arg_1469_);
v___x_1476_ = lean_sym_simp(v_arg_1469_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref_known(v___x_1476_, 1);
if (lean_obj_tag(v_a_1477_) == 0)
{
uint8_t v_contextDependent_1478_; lean_object* v___x_1479_; 
lean_dec_ref(v_e_1444_);
v_contextDependent_1478_ = lean_ctor_get_uint8(v_a_1477_, 1);
lean_dec_ref_known(v_a_1477_, 0);
v___x_1479_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_1469_, v___y_1448_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1520_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1520_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1520_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
uint8_t v___x_1484_; 
v___x_1484_ = lean_unbox(v_a_1480_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; 
lean_del_object(v___x_1482_);
v___x_1485_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_1469_, v___y_1448_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1503_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1503_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1503_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
uint8_t v___x_1490_; 
v___x_1490_ = lean_unbox(v_a_1486_);
lean_dec(v_a_1486_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; lean_object* v___f_1492_; lean_object* v___x_1493_; 
lean_del_object(v___x_1488_);
lean_dec(v_a_1480_);
v___x_1491_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_1475_, v_contextDependent_1478_);
v___f_1492_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1492_, 0, v___x_1491_);
v___x_1493_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v___x_1473_, v_arg_1472_, v_arg_1469_, v_arg_1466_, v_arg_1463_, v_arg_1460_, v___f_1492_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec_ref(v___x_1473_);
return v___x_1493_;
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; lean_object* v___x_1501_; 
lean_dec_ref(v_arg_1469_);
lean_dec_ref(v_arg_1466_);
v___x_1494_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__2));
v___x_1495_ = l_Lean_Expr_constLevels_x21(v___x_1473_);
lean_dec_ref(v___x_1473_);
v___x_1496_ = l_Lean_mkConst(v___x_1494_, v___x_1495_);
lean_inc_ref(v_arg_1460_);
v___x_1497_ = l_Lean_mkApp3(v___x_1496_, v_arg_1472_, v_arg_1463_, v_arg_1460_);
v___x_1498_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1498_, 0, v_arg_1460_);
lean_ctor_set(v___x_1498_, 1, v___x_1497_);
v___x_1499_ = lean_unbox(v_a_1480_);
lean_dec(v_a_1480_);
lean_ctor_set_uint8(v___x_1498_, sizeof(void*)*2, v___x_1499_);
lean_ctor_set_uint8(v___x_1498_, sizeof(void*)*2 + 1, v_contextDependent_1478_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v___x_1498_);
v___x_1501_ = v___x_1488_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1498_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
else
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
lean_dec(v_a_1480_);
lean_dec_ref(v___x_1473_);
lean_dec_ref(v_arg_1472_);
lean_dec_ref(v_arg_1469_);
lean_dec_ref(v_arg_1466_);
lean_dec_ref(v_arg_1463_);
lean_dec_ref(v_arg_1460_);
v_a_1504_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v___x_1485_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1485_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1518_; 
lean_dec(v_a_1480_);
lean_dec_ref(v_arg_1469_);
lean_dec_ref(v_arg_1466_);
v___x_1512_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__3));
v___x_1513_ = l_Lean_Expr_constLevels_x21(v___x_1473_);
lean_dec_ref(v___x_1473_);
v___x_1514_ = l_Lean_mkConst(v___x_1512_, v___x_1513_);
lean_inc_ref(v_arg_1463_);
v___x_1515_ = l_Lean_mkApp3(v___x_1514_, v_arg_1472_, v_arg_1463_, v_arg_1460_);
v___x_1516_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1516_, 0, v_arg_1463_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
lean_ctor_set_uint8(v___x_1516_, sizeof(void*)*2, v___x_1443_);
lean_ctor_set_uint8(v___x_1516_, sizeof(void*)*2 + 1, v_contextDependent_1478_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v___x_1516_);
v___x_1518_ = v___x_1482_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1516_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
else
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec_ref(v___x_1473_);
lean_dec_ref(v_arg_1472_);
lean_dec_ref(v_arg_1469_);
lean_dec_ref(v_arg_1466_);
lean_dec_ref(v_arg_1463_);
lean_dec_ref(v_arg_1460_);
v_a_1521_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1479_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1479_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
}
else
{
lean_object* v_e_x27_1529_; lean_object* v_proof_1530_; uint8_t v_contextDependent_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1609_; 
v_e_x27_1529_ = lean_ctor_get(v_a_1477_, 0);
v_proof_1530_ = lean_ctor_get(v_a_1477_, 1);
v_contextDependent_1531_ = lean_ctor_get_uint8(v_a_1477_, sizeof(void*)*2 + 1);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_a_1477_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1533_ = v_a_1477_;
v_isShared_1534_ = v_isSharedCheck_1609_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_proof_1530_);
lean_inc(v_e_x27_1529_);
lean_dec(v_a_1477_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1609_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_1529_, v___y_1448_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1600_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1538_ = v___x_1535_;
v_isShared_1539_ = v_isSharedCheck_1600_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1535_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1600_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
uint8_t v___x_1540_; 
v___x_1540_ = lean_unbox(v_a_1536_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; 
lean_del_object(v___x_1538_);
v___x_1541_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_1529_, v___y_1448_);
lean_dec_ref(v_e_x27_1529_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1582_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1544_ = v___x_1541_;
v_isShared_1545_ = v_isSharedCheck_1582_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1582_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
uint8_t v___x_1546_; 
v___x_1546_ = lean_unbox(v_a_1542_);
lean_dec(v_a_1542_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; 
lean_del_object(v___x_1544_);
lean_dec(v_a_1536_);
lean_del_object(v___x_1533_);
lean_dec_ref(v_proof_1530_);
lean_inc_ref(v_arg_1466_);
v___x_1547_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance(v_arg_1466_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v_fst_1549_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v___x_1547_, 1);
v_fst_1549_ = lean_ctor_get(v_a_1548_, 0);
lean_inc(v_fst_1549_);
if (lean_obj_tag(v_fst_1549_) == 0)
{
uint8_t v_contextDependent_1550_; lean_object* v___x_1551_; lean_object* v___f_1552_; lean_object* v___x_1553_; 
lean_dec(v_a_1548_);
lean_dec_ref(v_e_1444_);
v_contextDependent_1550_ = lean_ctor_get_uint8(v_fst_1549_, 1);
lean_dec_ref_known(v_fst_1549_, 0);
v___x_1551_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_1475_, v_contextDependent_1550_);
v___f_1552_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1552_, 0, v___x_1551_);
v___x_1553_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v___x_1473_, v_arg_1472_, v_arg_1469_, v_arg_1466_, v_arg_1463_, v_arg_1460_, v___f_1552_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec_ref(v___x_1473_);
return v___x_1553_;
}
else
{
lean_object* v_snd_1554_; lean_object* v_e_x27_1555_; lean_object* v_proof_1556_; uint8_t v_contextDependent_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___f_1562_; lean_object* v___x_1563_; 
v_snd_1554_ = lean_ctor_get(v_a_1548_, 1);
lean_inc_n(v_snd_1554_, 2);
lean_dec(v_a_1548_);
v_e_x27_1555_ = lean_ctor_get(v_fst_1549_, 0);
lean_inc_ref_n(v_e_x27_1555_, 2);
v_proof_1556_ = lean_ctor_get(v_fst_1549_, 1);
lean_inc_ref_n(v_proof_1556_, 2);
v_contextDependent_1557_ = lean_ctor_get_uint8(v_fst_1549_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_1549_, 2);
v___x_1558_ = lean_unsigned_to_nat(4u);
v___x_1559_ = l_Lean_Expr_getBoundedAppFn(v___x_1558_, v_e_1444_);
v___x_1560_ = lean_box(v___x_1475_);
v___x_1561_ = lean_box(v_contextDependent_1557_);
lean_inc_ref(v_arg_1460_);
lean_inc_ref(v_arg_1463_);
v___f_1562_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___boxed), 19, 9);
lean_closure_set(v___f_1562_, 0, v___x_1559_);
lean_closure_set(v___f_1562_, 1, v_e_x27_1555_);
lean_closure_set(v___f_1562_, 2, v_snd_1554_);
lean_closure_set(v___f_1562_, 3, v_arg_1463_);
lean_closure_set(v___f_1562_, 4, v_arg_1460_);
lean_closure_set(v___f_1562_, 5, v_e_1444_);
lean_closure_set(v___f_1562_, 6, v_proof_1556_);
lean_closure_set(v___f_1562_, 7, v___x_1560_);
lean_closure_set(v___f_1562_, 8, v___x_1561_);
v___x_1563_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr(v___x_1473_, v_arg_1472_, v_arg_1469_, v_arg_1466_, v_arg_1463_, v_arg_1460_, v_e_x27_1555_, v_proof_1556_, v_snd_1554_, v___f_1562_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec_ref(v___x_1473_);
return v___x_1563_;
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec_ref(v___x_1473_);
lean_dec_ref(v_arg_1472_);
lean_dec_ref(v_arg_1469_);
lean_dec_ref(v_arg_1466_);
lean_dec_ref(v_arg_1463_);
lean_dec_ref(v_arg_1460_);
lean_dec_ref(v_e_1444_);
v_a_1564_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1547_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1547_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
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
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; 
lean_dec_ref(v___x_1473_);
lean_dec_ref(v_arg_1472_);
lean_dec_ref(v_arg_1469_);
lean_dec_ref(v_arg_1466_);
lean_dec_ref(v_arg_1463_);
v___x_1572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__5));
v___x_1573_ = l_Lean_Expr_replaceFn(v_e_1444_, v___x_1572_);
v___x_1574_ = l_Lean_Expr_app___override(v___x_1573_, v_proof_1530_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 1, v___x_1574_);
lean_ctor_set(v___x_1533_, 0, v_arg_1460_);
v___x_1576_ = v___x_1533_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_arg_1460_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
uint8_t v___x_1577_; lean_object* v___x_1579_; 
v___x_1577_ = lean_unbox(v_a_1536_);
lean_dec(v_a_1536_);
lean_ctor_set_uint8(v___x_1576_, sizeof(void*)*2, v___x_1577_);
lean_ctor_set_uint8(v___x_1576_, sizeof(void*)*2 + 1, v_contextDependent_1531_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v___x_1576_);
v___x_1579_ = v___x_1544_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1576_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec(v_a_1536_);
lean_del_object(v___x_1533_);
lean_dec_ref(v_proof_1530_);
lean_dec_ref(v___x_1473_);
lean_dec_ref(v_arg_1472_);
lean_dec_ref(v_arg_1469_);
lean_dec_ref(v_arg_1466_);
lean_dec_ref(v_arg_1463_);
lean_dec_ref(v_arg_1460_);
lean_dec_ref(v_e_1444_);
v_a_1583_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1541_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1541_);
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
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1595_; 
lean_dec(v_a_1536_);
lean_dec_ref(v_e_x27_1529_);
lean_dec_ref(v___x_1473_);
lean_dec_ref(v_arg_1472_);
lean_dec_ref(v_arg_1469_);
lean_dec_ref(v_arg_1466_);
lean_dec_ref(v_arg_1460_);
v___x_1591_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__7));
v___x_1592_ = l_Lean_Expr_replaceFn(v_e_1444_, v___x_1591_);
v___x_1593_ = l_Lean_Expr_app___override(v___x_1592_, v_proof_1530_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 1, v___x_1593_);
lean_ctor_set(v___x_1533_, 0, v_arg_1463_);
v___x_1595_ = v___x_1533_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_arg_1463_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v___x_1593_);
lean_ctor_set_uint8(v_reuseFailAlloc_1599_, sizeof(void*)*2 + 1, v_contextDependent_1531_);
v___x_1595_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1597_; 
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*2, v___x_1443_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v___x_1595_);
v___x_1597_ = v___x_1538_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_del_object(v___x_1533_);
lean_dec_ref(v_proof_1530_);
lean_dec_ref(v_e_x27_1529_);
lean_dec_ref(v___x_1473_);
lean_dec_ref(v_arg_1472_);
lean_dec_ref(v_arg_1469_);
lean_dec_ref(v_arg_1466_);
lean_dec_ref(v_arg_1463_);
lean_dec_ref(v_arg_1460_);
lean_dec_ref(v_e_1444_);
v_a_1601_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1535_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1535_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1473_);
lean_dec_ref(v_arg_1472_);
lean_dec_ref(v_arg_1469_);
lean_dec_ref(v_arg_1466_);
lean_dec_ref(v_arg_1463_);
lean_dec_ref(v_arg_1460_);
lean_dec_ref(v_e_1444_);
return v___x_1476_;
}
}
}
}
}
}
}
v___jp_1455_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1456_, 0, v___x_1443_);
lean_ctor_set_uint8(v___x_1456_, 1, v___x_1443_);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
return v___x_1457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___boxed(lean_object* v___x_1610_, lean_object* v_e_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
uint8_t v___x_14898__boxed_1622_; lean_object* v_res_1623_; 
v___x_14898__boxed_1622_ = lean_unbox(v___x_1610_);
v_res_1623_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1(v___x_14898__boxed_1622_, v_e_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv(lean_object* v_e_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v_numArgs_1635_; lean_object* v___x_1636_; uint8_t v___x_1637_; 
v_numArgs_1635_ = l_Lean_Expr_getAppNumArgs(v_e_1624_);
v___x_1636_ = lean_unsigned_to_nat(5u);
v___x_1637_ = lean_nat_dec_lt(v_numArgs_1635_, v___x_1636_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; lean_object* v___f_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1638_ = lean_box(v___x_1637_);
v___f_1639_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___boxed), 12, 1);
lean_closure_set(v___f_1639_, 0, v___x_1638_);
v___x_1640_ = lean_nat_sub(v_numArgs_1635_, v___x_1636_);
lean_dec(v_numArgs_1635_);
v___x_1641_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_1624_, v___x_1640_, v___f_1639_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
lean_dec(v___x_1640_);
return v___x_1641_;
}
else
{
uint8_t v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
lean_dec(v_numArgs_1635_);
lean_dec_ref(v_e_1624_);
v___x_1642_ = 0;
v___x_1643_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1643_, 0, v___x_1637_);
lean_ctor_set_uint8(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1643_);
return v___x_1644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed(lean_object* v_e_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv(v_e_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
lean_dec(v_a_1648_);
lean_dec_ref(v_a_1647_);
lean_dec(v_a_1646_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(lean_object* v_f_1657_, lean_object* v_a_u2081_1658_, lean_object* v_a_u2082_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg(v_f_1657_, v_a_u2081_1658_, v_a_u2082_1659_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___boxed(lean_object* v_f_1671_, lean_object* v_a_u2081_1672_, lean_object* v_a_u2082_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(v_f_1671_, v_a_u2081_1672_, v_a_u2082_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1742_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_));
v___x_1743_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_));
v___x_1744_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed), 11, 0);
v___x_1745_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_1742_, v___x_1743_, v___x_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17____boxed(lean_object* v_a_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_();
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1749_; uint8_t v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_));
v___x_1750_ = 0;
v___x_1751_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed), 11, 0);
v___x_1752_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_1749_, v___x_1750_, v___x_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_19____boxed(lean_object* v_a_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_19_();
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(lean_object* v_f_1765_, lean_object* v_00_u03b1_1766_, lean_object* v_c_1767_, lean_object* v_inst_1768_, lean_object* v_a_1769_, lean_object* v_b_1770_, lean_object* v_instToMatch_1771_, lean_object* v_fallback_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_instToMatch_1771_, v_a_1779_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1783_, 1);
v___x_1785_ = l_Lean_Expr_cleanupAnnotations(v_a_1784_);
v___x_1786_ = l_Lean_Expr_isApp(v___x_1785_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; 
lean_dec_ref(v___x_1785_);
lean_dec_ref(v_b_1770_);
lean_dec_ref(v_a_1769_);
lean_dec_ref(v_inst_1768_);
lean_dec_ref(v_c_1767_);
lean_dec_ref(v_00_u03b1_1766_);
lean_inc(v_a_1781_);
lean_inc_ref(v_a_1780_);
lean_inc(v_a_1779_);
lean_inc_ref(v_a_1778_);
lean_inc(v_a_1777_);
lean_inc_ref(v_a_1776_);
lean_inc(v_a_1775_);
lean_inc_ref(v_a_1774_);
lean_inc(v_a_1773_);
v___x_1787_ = lean_apply_10(v_fallback_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, lean_box(0));
return v___x_1787_;
}
else
{
lean_object* v_arg_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v_arg_1788_ = lean_ctor_get(v___x_1785_, 1);
lean_inc_ref(v_arg_1788_);
v___x_1789_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1785_);
v___x_1790_ = l_Lean_Expr_isApp(v___x_1789_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1791_; 
lean_dec_ref(v___x_1789_);
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_b_1770_);
lean_dec_ref(v_a_1769_);
lean_dec_ref(v_inst_1768_);
lean_dec_ref(v_c_1767_);
lean_dec_ref(v_00_u03b1_1766_);
lean_inc(v_a_1781_);
lean_inc_ref(v_a_1780_);
lean_inc(v_a_1779_);
lean_inc_ref(v_a_1778_);
lean_inc(v_a_1777_);
lean_inc_ref(v_a_1776_);
lean_inc(v_a_1775_);
lean_inc_ref(v_a_1774_);
lean_inc(v_a_1773_);
v___x_1791_ = lean_apply_10(v_fallback_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, lean_box(0));
return v___x_1791_;
}
else
{
lean_object* v_arg_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v_arg_1792_ = lean_ctor_get(v___x_1789_, 1);
lean_inc_ref(v_arg_1792_);
v___x_1793_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1789_);
v___x_1794_ = l_Lean_Expr_isApp(v___x_1793_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; 
lean_dec_ref(v___x_1793_);
lean_dec_ref(v_arg_1792_);
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_b_1770_);
lean_dec_ref(v_a_1769_);
lean_dec_ref(v_inst_1768_);
lean_dec_ref(v_c_1767_);
lean_dec_ref(v_00_u03b1_1766_);
lean_inc(v_a_1781_);
lean_inc_ref(v_a_1780_);
lean_inc(v_a_1779_);
lean_inc_ref(v_a_1778_);
lean_inc(v_a_1777_);
lean_inc_ref(v_a_1776_);
lean_inc(v_a_1775_);
lean_inc_ref(v_a_1774_);
lean_inc(v_a_1773_);
v___x_1795_ = lean_apply_10(v_fallback_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, lean_box(0));
return v___x_1795_;
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; 
v___x_1796_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1793_);
v___x_1797_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_1798_ = l_Lean_Expr_isConstOf(v___x_1796_, v___x_1797_);
lean_dec_ref(v___x_1796_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; 
lean_dec_ref(v_arg_1792_);
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_b_1770_);
lean_dec_ref(v_a_1769_);
lean_dec_ref(v_inst_1768_);
lean_dec_ref(v_c_1767_);
lean_dec_ref(v_00_u03b1_1766_);
lean_inc(v_a_1781_);
lean_inc_ref(v_a_1780_);
lean_inc(v_a_1779_);
lean_inc_ref(v_a_1778_);
lean_inc(v_a_1777_);
lean_inc_ref(v_a_1776_);
lean_inc(v_a_1775_);
lean_inc_ref(v_a_1774_);
lean_inc(v_a_1773_);
v___x_1799_ = lean_apply_10(v_fallback_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, lean_box(0));
return v___x_1799_;
}
else
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1792_, v_a_1779_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1801_);
lean_dec_ref_known(v___x_1800_, 1);
v___x_1802_ = l_Lean_Expr_cleanupAnnotations(v_a_1801_);
v___x_1803_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_1804_ = l_Lean_Expr_isConstOf(v___x_1802_, v___x_1803_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_1806_ = l_Lean_Expr_isConstOf(v___x_1802_, v___x_1805_);
lean_dec_ref(v___x_1802_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; 
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_b_1770_);
lean_dec_ref(v_a_1769_);
lean_dec_ref(v_inst_1768_);
lean_dec_ref(v_c_1767_);
lean_dec_ref(v_00_u03b1_1766_);
lean_inc(v_a_1781_);
lean_inc_ref(v_a_1780_);
lean_inc(v_a_1779_);
lean_inc_ref(v_a_1778_);
lean_inc(v_a_1777_);
lean_inc_ref(v_a_1776_);
lean_inc(v_a_1775_);
lean_inc_ref(v_a_1774_);
lean_inc(v_a_1773_);
v___x_1807_ = lean_apply_10(v_fallback_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, lean_box(0));
return v___x_1807_;
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
lean_dec_ref(v_fallback_1772_);
v___x_1808_ = lean_unsigned_to_nat(1u);
v___x_1809_ = lean_mk_empty_array_with_capacity(v___x_1808_);
lean_inc_ref(v_arg_1788_);
v___x_1810_ = lean_array_push(v___x_1809_, v_arg_1788_);
lean_inc_ref(v_a_1769_);
v___x_1811_ = l_Lean_Expr_betaRev(v_a_1769_, v___x_1810_, v___x_1804_, v___x_1804_);
lean_dec_ref(v___x_1810_);
v___x_1812_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1811_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1825_; 
v_a_1813_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1815_ = v___x_1812_;
v_isShared_1816_ = v_isSharedCheck_1825_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1812_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1825_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1823_; 
v___x_1817_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1));
v___x_1818_ = l_Lean_Expr_constLevels_x21(v_f_1765_);
v___x_1819_ = l_Lean_mkConst(v___x_1817_, v___x_1818_);
v___x_1820_ = l_Lean_mkApp6(v___x_1819_, v_00_u03b1_1766_, v_c_1767_, v_inst_1768_, v_a_1769_, v_b_1770_, v_arg_1788_);
v___x_1821_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1821_, 0, v_a_1813_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
lean_ctor_set_uint8(v___x_1821_, sizeof(void*)*2, v___x_1804_);
lean_ctor_set_uint8(v___x_1821_, sizeof(void*)*2 + 1, v___x_1804_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1821_);
v___x_1823_ = v___x_1815_;
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
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_b_1770_);
lean_dec_ref(v_a_1769_);
lean_dec_ref(v_inst_1768_);
lean_dec_ref(v_c_1767_);
lean_dec_ref(v_00_u03b1_1766_);
v_a_1826_ = lean_ctor_get(v___x_1812_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1812_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1812_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1812_);
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
else
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_dec_ref(v___x_1802_);
lean_dec_ref(v_fallback_1772_);
v___x_1834_ = lean_unsigned_to_nat(1u);
v___x_1835_ = lean_mk_empty_array_with_capacity(v___x_1834_);
lean_inc_ref(v_arg_1788_);
v___x_1836_ = lean_array_push(v___x_1835_, v_arg_1788_);
v___x_1837_ = 0;
lean_inc_ref(v_b_1770_);
v___x_1838_ = l_Lean_Expr_betaRev(v_b_1770_, v___x_1836_, v___x_1837_, v___x_1837_);
lean_dec_ref(v___x_1836_);
v___x_1839_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1838_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1852_; 
v_a_1840_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1842_ = v___x_1839_;
v_isShared_1843_ = v_isSharedCheck_1852_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1839_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1852_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1844_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3));
v___x_1845_ = l_Lean_Expr_constLevels_x21(v_f_1765_);
v___x_1846_ = l_Lean_mkConst(v___x_1844_, v___x_1845_);
v___x_1847_ = l_Lean_mkApp6(v___x_1846_, v_00_u03b1_1766_, v_c_1767_, v_inst_1768_, v_a_1769_, v_b_1770_, v_arg_1788_);
v___x_1848_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1848_, 0, v_a_1840_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
lean_ctor_set_uint8(v___x_1848_, sizeof(void*)*2, v___x_1837_);
lean_ctor_set_uint8(v___x_1848_, sizeof(void*)*2 + 1, v___x_1837_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 0, v___x_1848_);
v___x_1850_ = v___x_1842_;
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
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_b_1770_);
lean_dec_ref(v_a_1769_);
lean_dec_ref(v_inst_1768_);
lean_dec_ref(v_c_1767_);
lean_dec_ref(v_00_u03b1_1766_);
v_a_1853_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1839_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1839_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec_ref(v_arg_1788_);
lean_dec_ref(v_fallback_1772_);
lean_dec_ref(v_b_1770_);
lean_dec_ref(v_a_1769_);
lean_dec_ref(v_inst_1768_);
lean_dec_ref(v_c_1767_);
lean_dec_ref(v_00_u03b1_1766_);
v_a_1861_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1800_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1800_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
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
}
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec_ref(v_fallback_1772_);
lean_dec_ref(v_b_1770_);
lean_dec_ref(v_a_1769_);
lean_dec_ref(v_inst_1768_);
lean_dec_ref(v_c_1767_);
lean_dec_ref(v_00_u03b1_1766_);
v_a_1869_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1783_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1783_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___boxed(lean_object** _args){
lean_object* v_f_1877_ = _args[0];
lean_object* v_00_u03b1_1878_ = _args[1];
lean_object* v_c_1879_ = _args[2];
lean_object* v_inst_1880_ = _args[3];
lean_object* v_a_1881_ = _args[4];
lean_object* v_b_1882_ = _args[5];
lean_object* v_instToMatch_1883_ = _args[6];
lean_object* v_fallback_1884_ = _args[7];
lean_object* v_a_1885_ = _args[8];
lean_object* v_a_1886_ = _args[9];
lean_object* v_a_1887_ = _args[10];
lean_object* v_a_1888_ = _args[11];
lean_object* v_a_1889_ = _args[12];
lean_object* v_a_1890_ = _args[13];
lean_object* v_a_1891_ = _args[14];
lean_object* v_a_1892_ = _args[15];
lean_object* v_a_1893_ = _args[16];
lean_object* v_a_1894_ = _args[17];
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_1877_, v_00_u03b1_1878_, v_c_1879_, v_inst_1880_, v_a_1881_, v_b_1882_, v_instToMatch_1883_, v_fallback_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
lean_dec(v_a_1889_);
lean_dec_ref(v_a_1888_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec(v_a_1885_);
lean_dec_ref(v_f_1877_);
return v_res_1895_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1900_ = lean_box(0);
v___x_1901_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__1));
v___x_1902_ = l_Lean_mkConst(v___x_1901_, v___x_1900_);
return v___x_1902_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1912_ = lean_box(0);
v___x_1913_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__6));
v___x_1914_ = l_Lean_mkConst(v___x_1913_, v___x_1912_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(lean_object* v_f_1920_, lean_object* v_00_u03b1_1921_, lean_object* v_c_1922_, lean_object* v_inst_1923_, lean_object* v_a_1924_, lean_object* v_b_1925_, lean_object* v_c_x27_1926_, lean_object* v_h_1927_, lean_object* v_inst_x27_1928_, lean_object* v_fallback_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_x27_1928_, v_a_1936_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1940_, 1);
v___x_1942_ = l_Lean_Expr_cleanupAnnotations(v_a_1941_);
v___x_1943_ = l_Lean_Expr_isApp(v___x_1942_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; 
lean_dec_ref(v___x_1942_);
lean_dec_ref(v_h_1927_);
lean_dec_ref(v_c_x27_1926_);
lean_dec_ref(v_b_1925_);
lean_dec_ref(v_a_1924_);
lean_dec_ref(v_inst_1923_);
lean_dec_ref(v_c_1922_);
lean_dec_ref(v_00_u03b1_1921_);
lean_inc(v_a_1938_);
lean_inc_ref(v_a_1937_);
lean_inc(v_a_1936_);
lean_inc_ref(v_a_1935_);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
lean_inc(v_a_1932_);
lean_inc_ref(v_a_1931_);
lean_inc(v_a_1930_);
v___x_1944_ = lean_apply_10(v_fallback_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, lean_box(0));
return v___x_1944_;
}
else
{
lean_object* v_arg_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; 
v_arg_1945_ = lean_ctor_get(v___x_1942_, 1);
lean_inc_ref(v_arg_1945_);
v___x_1946_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1942_);
v___x_1947_ = l_Lean_Expr_isApp(v___x_1946_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; 
lean_dec_ref(v___x_1946_);
lean_dec_ref(v_arg_1945_);
lean_dec_ref(v_h_1927_);
lean_dec_ref(v_c_x27_1926_);
lean_dec_ref(v_b_1925_);
lean_dec_ref(v_a_1924_);
lean_dec_ref(v_inst_1923_);
lean_dec_ref(v_c_1922_);
lean_dec_ref(v_00_u03b1_1921_);
lean_inc(v_a_1938_);
lean_inc_ref(v_a_1937_);
lean_inc(v_a_1936_);
lean_inc_ref(v_a_1935_);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
lean_inc(v_a_1932_);
lean_inc_ref(v_a_1931_);
lean_inc(v_a_1930_);
v___x_1948_ = lean_apply_10(v_fallback_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, lean_box(0));
return v___x_1948_;
}
else
{
lean_object* v_arg_1949_; lean_object* v___x_1950_; uint8_t v___x_1951_; 
v_arg_1949_ = lean_ctor_get(v___x_1946_, 1);
lean_inc_ref(v_arg_1949_);
v___x_1950_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1946_);
v___x_1951_ = l_Lean_Expr_isApp(v___x_1950_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; 
lean_dec_ref(v___x_1950_);
lean_dec_ref(v_arg_1949_);
lean_dec_ref(v_arg_1945_);
lean_dec_ref(v_h_1927_);
lean_dec_ref(v_c_x27_1926_);
lean_dec_ref(v_b_1925_);
lean_dec_ref(v_a_1924_);
lean_dec_ref(v_inst_1923_);
lean_dec_ref(v_c_1922_);
lean_dec_ref(v_00_u03b1_1921_);
lean_inc(v_a_1938_);
lean_inc_ref(v_a_1937_);
lean_inc(v_a_1936_);
lean_inc_ref(v_a_1935_);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
lean_inc(v_a_1932_);
lean_inc_ref(v_a_1931_);
lean_inc(v_a_1930_);
v___x_1952_ = lean_apply_10(v_fallback_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, lean_box(0));
return v___x_1952_;
}
else
{
lean_object* v___x_1953_; lean_object* v___x_1954_; uint8_t v___x_1955_; 
v___x_1953_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1950_);
v___x_1954_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_1955_ = l_Lean_Expr_isConstOf(v___x_1953_, v___x_1954_);
lean_dec_ref(v___x_1953_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; 
lean_dec_ref(v_arg_1949_);
lean_dec_ref(v_arg_1945_);
lean_dec_ref(v_h_1927_);
lean_dec_ref(v_c_x27_1926_);
lean_dec_ref(v_b_1925_);
lean_dec_ref(v_a_1924_);
lean_dec_ref(v_inst_1923_);
lean_dec_ref(v_c_1922_);
lean_dec_ref(v_00_u03b1_1921_);
lean_inc(v_a_1938_);
lean_inc_ref(v_a_1937_);
lean_inc(v_a_1936_);
lean_inc_ref(v_a_1935_);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
lean_inc(v_a_1932_);
lean_inc_ref(v_a_1931_);
lean_inc(v_a_1930_);
v___x_1956_ = lean_apply_10(v_fallback_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, lean_box(0));
return v___x_1956_;
}
else
{
lean_object* v___x_1957_; 
v___x_1957_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1949_, v_a_1936_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v___x_1959_ = l_Lean_Expr_cleanupAnnotations(v_a_1958_);
v___x_1960_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_1961_ = l_Lean_Expr_isConstOf(v___x_1959_, v___x_1960_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1962_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_1963_ = l_Lean_Expr_isConstOf(v___x_1959_, v___x_1962_);
lean_dec_ref(v___x_1959_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; 
lean_dec_ref(v_arg_1945_);
lean_dec_ref(v_h_1927_);
lean_dec_ref(v_c_x27_1926_);
lean_dec_ref(v_b_1925_);
lean_dec_ref(v_a_1924_);
lean_dec_ref(v_inst_1923_);
lean_dec_ref(v_c_1922_);
lean_dec_ref(v_00_u03b1_1921_);
lean_inc(v_a_1938_);
lean_inc_ref(v_a_1937_);
lean_inc(v_a_1936_);
lean_inc_ref(v_a_1935_);
lean_inc(v_a_1934_);
lean_inc_ref(v_a_1933_);
lean_inc(v_a_1932_);
lean_inc_ref(v_a_1931_);
lean_inc(v_a_1930_);
v___x_1964_ = lean_apply_10(v_fallback_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, lean_box(0));
return v___x_1964_;
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_dec_ref(v_fallback_1929_);
v___x_1965_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2);
lean_inc_ref(v_arg_1945_);
lean_inc_ref(v_h_1927_);
lean_inc_ref(v_c_x27_1926_);
lean_inc_ref(v_c_1922_);
v___x_1966_ = l_Lean_mkApp4(v___x_1965_, v_c_1922_, v_c_x27_1926_, v_h_1927_, v_arg_1945_);
v___x_1967_ = lean_unsigned_to_nat(1u);
v___x_1968_ = lean_mk_empty_array_with_capacity(v___x_1967_);
v___x_1969_ = lean_array_push(v___x_1968_, v___x_1966_);
lean_inc_ref(v_a_1924_);
v___x_1970_ = l_Lean_Expr_betaRev(v_a_1924_, v___x_1969_, v___x_1961_, v___x_1961_);
lean_dec_ref(v___x_1969_);
v___x_1971_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1970_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1984_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1974_ = v___x_1971_;
v_isShared_1975_ = v_isSharedCheck_1984_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1971_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1984_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1982_; 
v___x_1976_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4));
v___x_1977_ = l_Lean_Expr_constLevels_x21(v_f_1920_);
v___x_1978_ = l_Lean_mkConst(v___x_1976_, v___x_1977_);
v___x_1979_ = l_Lean_mkApp8(v___x_1978_, v_00_u03b1_1921_, v_c_1922_, v_inst_1923_, v_a_1924_, v_b_1925_, v_c_x27_1926_, v_h_1927_, v_arg_1945_);
v___x_1980_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1980_, 0, v_a_1972_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
lean_ctor_set_uint8(v___x_1980_, sizeof(void*)*2, v___x_1961_);
lean_ctor_set_uint8(v___x_1980_, sizeof(void*)*2 + 1, v___x_1961_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v___x_1980_);
v___x_1982_ = v___x_1974_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec_ref(v_arg_1945_);
lean_dec_ref(v_h_1927_);
lean_dec_ref(v_c_x27_1926_);
lean_dec_ref(v_b_1925_);
lean_dec_ref(v_a_1924_);
lean_dec_ref(v_inst_1923_);
lean_dec_ref(v_c_1922_);
lean_dec_ref(v_00_u03b1_1921_);
v_a_1985_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1971_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1971_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
}
else
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
lean_dec_ref(v___x_1959_);
lean_dec_ref(v_fallback_1929_);
v___x_1993_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7);
lean_inc_ref(v_arg_1945_);
lean_inc_ref(v_h_1927_);
lean_inc_ref(v_c_x27_1926_);
lean_inc_ref(v_c_1922_);
v___x_1994_ = l_Lean_mkApp4(v___x_1993_, v_c_1922_, v_c_x27_1926_, v_h_1927_, v_arg_1945_);
v___x_1995_ = lean_unsigned_to_nat(1u);
v___x_1996_ = lean_mk_empty_array_with_capacity(v___x_1995_);
v___x_1997_ = lean_array_push(v___x_1996_, v___x_1994_);
v___x_1998_ = 0;
lean_inc_ref(v_b_1925_);
v___x_1999_ = l_Lean_Expr_betaRev(v_b_1925_, v___x_1997_, v___x_1998_, v___x_1998_);
lean_dec_ref(v___x_1997_);
v___x_2000_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1999_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2013_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2013_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2013_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2011_; 
v___x_2005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9));
v___x_2006_ = l_Lean_Expr_constLevels_x21(v_f_1920_);
v___x_2007_ = l_Lean_mkConst(v___x_2005_, v___x_2006_);
v___x_2008_ = l_Lean_mkApp8(v___x_2007_, v_00_u03b1_1921_, v_c_1922_, v_inst_1923_, v_a_1924_, v_b_1925_, v_c_x27_1926_, v_h_1927_, v_arg_1945_);
v___x_2009_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2009_, 0, v_a_2001_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
lean_ctor_set_uint8(v___x_2009_, sizeof(void*)*2, v___x_1998_);
lean_ctor_set_uint8(v___x_2009_, sizeof(void*)*2 + 1, v___x_1998_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2009_);
v___x_2011_ = v___x_2003_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_dec_ref(v_arg_1945_);
lean_dec_ref(v_h_1927_);
lean_dec_ref(v_c_x27_1926_);
lean_dec_ref(v_b_1925_);
lean_dec_ref(v_a_1924_);
lean_dec_ref(v_inst_1923_);
lean_dec_ref(v_c_1922_);
lean_dec_ref(v_00_u03b1_1921_);
v_a_2014_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_2000_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_2000_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
}
else
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec_ref(v_arg_1945_);
lean_dec_ref(v_fallback_1929_);
lean_dec_ref(v_h_1927_);
lean_dec_ref(v_c_x27_1926_);
lean_dec_ref(v_b_1925_);
lean_dec_ref(v_a_1924_);
lean_dec_ref(v_inst_1923_);
lean_dec_ref(v_c_1922_);
lean_dec_ref(v_00_u03b1_1921_);
v_a_2022_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_1957_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_1957_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
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
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec_ref(v_fallback_1929_);
lean_dec_ref(v_h_1927_);
lean_dec_ref(v_c_x27_1926_);
lean_dec_ref(v_b_1925_);
lean_dec_ref(v_a_1924_);
lean_dec_ref(v_inst_1923_);
lean_dec_ref(v_c_1922_);
lean_dec_ref(v_00_u03b1_1921_);
v_a_2030_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_1940_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_1940_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_2038_ = _args[0];
lean_object* v_00_u03b1_2039_ = _args[1];
lean_object* v_c_2040_ = _args[2];
lean_object* v_inst_2041_ = _args[3];
lean_object* v_a_2042_ = _args[4];
lean_object* v_b_2043_ = _args[5];
lean_object* v_c_x27_2044_ = _args[6];
lean_object* v_h_2045_ = _args[7];
lean_object* v_inst_x27_2046_ = _args[8];
lean_object* v_fallback_2047_ = _args[9];
lean_object* v_a_2048_ = _args[10];
lean_object* v_a_2049_ = _args[11];
lean_object* v_a_2050_ = _args[12];
lean_object* v_a_2051_ = _args[13];
lean_object* v_a_2052_ = _args[14];
lean_object* v_a_2053_ = _args[15];
lean_object* v_a_2054_ = _args[16];
lean_object* v_a_2055_ = _args[17];
lean_object* v_a_2056_ = _args[18];
lean_object* v_a_2057_ = _args[19];
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(v_f_2038_, v_00_u03b1_2039_, v_c_2040_, v_inst_2041_, v_a_2042_, v_b_2043_, v_c_x27_2044_, v_h_2045_, v_inst_x27_2046_, v_fallback_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
lean_dec(v_a_2050_);
lean_dec_ref(v_a_2049_);
lean_dec(v_a_2048_);
lean_dec_ref(v_f_2038_);
return v_res_2058_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2(void){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2062_ = lean_box(0);
v___x_2063_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__1));
v___x_2064_ = l_Lean_mkConst(v___x_2063_, v___x_2062_);
return v___x_2064_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5(void){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2068_ = lean_box(0);
v___x_2069_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__4));
v___x_2070_ = l_Lean_mkConst(v___x_2069_, v___x_2068_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(lean_object* v_f_2071_, lean_object* v_00_u03b1_2072_, lean_object* v_c_2073_, lean_object* v_inst_2074_, lean_object* v_a_2075_, lean_object* v_b_2076_, lean_object* v_fallback_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v___x_2088_; uint8_t v___x_2089_; lean_object* v___x_2090_; lean_object* v___f_2091_; lean_object* v___x_2092_; 
v___x_2088_ = lean_unsigned_to_nat(0u);
v___x_2089_ = 5;
v___x_2090_ = lean_box(v___x_2089_);
lean_inc_ref(v_inst_2074_);
v___f_2091_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2091_, 0, v___x_2090_);
lean_closure_set(v___f_2091_, 1, v_inst_2074_);
lean_closure_set(v___f_2091_, 2, v___x_2088_);
v___x_2092_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2091_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
if (lean_obj_tag(v_a_2093_) == 0)
{
lean_object* v___x_2094_; 
lean_inc(v_a_2086_);
lean_inc_ref(v_a_2085_);
lean_inc(v_a_2084_);
lean_inc_ref(v_a_2083_);
lean_inc(v_a_2082_);
lean_inc_ref(v_a_2081_);
lean_inc(v_a_2080_);
lean_inc_ref(v_a_2079_);
lean_inc(v_a_2078_);
lean_inc_ref(v_inst_2074_);
v___x_2094_ = lean_sym_simp(v_inst_2074_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
if (lean_obj_tag(v_a_2095_) == 0)
{
uint8_t v_contextDependent_2096_; lean_object* v___x_2097_; 
v_contextDependent_2096_ = lean_ctor_get_uint8(v_a_2095_, 1);
lean_dec_ref_known(v_a_2095_, 0);
lean_inc_ref(v_inst_2074_);
v___x_2097_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_2071_, v_00_u03b1_2072_, v_c_2073_, v_inst_2074_, v_a_2075_, v_b_2076_, v_inst_2074_, v_fallback_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; uint8_t v___y_2100_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
if (v_contextDependent_2096_ == 0)
{
lean_dec(v_a_2098_);
return v___x_2097_;
}
else
{
if (lean_obj_tag(v_a_2098_) == 0)
{
uint8_t v_contextDependent_2110_; 
v_contextDependent_2110_ = lean_ctor_get_uint8(v_a_2098_, 1);
v___y_2100_ = v_contextDependent_2110_;
goto v___jp_2099_;
}
else
{
uint8_t v_contextDependent_2111_; 
v_contextDependent_2111_ = lean_ctor_get_uint8(v_a_2098_, sizeof(void*)*2 + 1);
v___y_2100_ = v_contextDependent_2111_;
goto v___jp_2099_;
}
}
v___jp_2099_:
{
if (v___y_2100_ == 0)
{
lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2108_; 
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2108_ == 0)
{
lean_object* v_unused_2109_; 
v_unused_2109_ = lean_ctor_get(v___x_2097_, 0);
lean_dec(v_unused_2109_);
v___x_2102_ = v___x_2097_;
v_isShared_2103_ = v_isSharedCheck_2108_;
goto v_resetjp_2101_;
}
else
{
lean_dec(v___x_2097_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2108_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2104_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2098_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2104_);
v___x_2106_ = v___x_2102_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
else
{
lean_dec(v_a_2098_);
return v___x_2097_;
}
}
}
else
{
return v___x_2097_;
}
}
else
{
lean_object* v_e_x27_2112_; uint8_t v_contextDependent_2113_; lean_object* v___x_2114_; 
v_e_x27_2112_ = lean_ctor_get(v_a_2095_, 0);
lean_inc_ref(v_e_x27_2112_);
v_contextDependent_2113_ = lean_ctor_get_uint8(v_a_2095_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2095_, 2);
v___x_2114_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_2071_, v_00_u03b1_2072_, v_c_2073_, v_inst_2074_, v_a_2075_, v_b_2076_, v_e_x27_2112_, v_fallback_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; uint8_t v___y_2117_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
if (v_contextDependent_2113_ == 0)
{
lean_dec(v_a_2115_);
return v___x_2114_;
}
else
{
if (lean_obj_tag(v_a_2115_) == 0)
{
uint8_t v_contextDependent_2127_; 
v_contextDependent_2127_ = lean_ctor_get_uint8(v_a_2115_, 1);
v___y_2117_ = v_contextDependent_2127_;
goto v___jp_2116_;
}
else
{
uint8_t v_contextDependent_2128_; 
v_contextDependent_2128_ = lean_ctor_get_uint8(v_a_2115_, sizeof(void*)*2 + 1);
v___y_2117_ = v_contextDependent_2128_;
goto v___jp_2116_;
}
}
v___jp_2116_:
{
if (v___y_2117_ == 0)
{
lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2125_; 
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2125_ == 0)
{
lean_object* v_unused_2126_; 
v_unused_2126_ = lean_ctor_get(v___x_2114_, 0);
lean_dec(v_unused_2126_);
v___x_2119_ = v___x_2114_;
v_isShared_2120_ = v_isSharedCheck_2125_;
goto v_resetjp_2118_;
}
else
{
lean_dec(v___x_2114_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2125_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2121_; lean_object* v___x_2123_; 
v___x_2121_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2115_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v___x_2121_);
v___x_2123_ = v___x_2119_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2121_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
else
{
lean_dec(v_a_2115_);
return v___x_2114_;
}
}
}
else
{
return v___x_2114_;
}
}
}
else
{
lean_dec_ref(v_fallback_2077_);
lean_dec_ref(v_b_2076_);
lean_dec_ref(v_a_2075_);
lean_dec_ref(v_inst_2074_);
lean_dec_ref(v_c_2073_);
lean_dec_ref(v_00_u03b1_2072_);
return v___x_2094_;
}
}
else
{
lean_object* v_val_2129_; lean_object* v___x_2130_; 
v_val_2129_ = lean_ctor_get(v_a_2093_, 0);
lean_inc(v_val_2129_);
lean_dec_ref_known(v_a_2093_, 1);
v___x_2130_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2129_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc_n(v_a_2131_, 3);
lean_dec_ref_known(v___x_2130_, 1);
v___x_2132_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2);
v___x_2133_ = lean_unsigned_to_nat(1u);
v___x_2134_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8);
v___x_2135_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10);
v___x_2136_ = l_Lean_mkAppB(v___x_2134_, v___x_2135_, v_a_2131_);
lean_inc(v_a_2086_);
lean_inc_ref(v_a_2085_);
lean_inc(v_a_2084_);
lean_inc_ref(v_a_2083_);
lean_inc(v_a_2082_);
lean_inc_ref(v_a_2081_);
lean_inc(v_a_2080_);
lean_inc_ref(v_a_2079_);
lean_inc(v_a_2078_);
v___x_2137_ = lean_sym_simp(v_a_2131_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; uint8_t v___x_2139_; lean_object* v_e_x27_2141_; lean_object* v_proof_2142_; uint8_t v_contextDependent_2143_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v___x_2139_ = 0;
if (lean_obj_tag(v_a_2138_) == 0)
{
uint8_t v_contextDependent_2234_; 
v_contextDependent_2234_ = lean_ctor_get_uint8(v_a_2138_, 1);
lean_dec_ref_known(v_a_2138_, 0);
v_e_x27_2141_ = v_a_2131_;
v_proof_2142_ = v___x_2136_;
v_contextDependent_2143_ = v_contextDependent_2234_;
goto v___jp_2140_;
}
else
{
lean_object* v_e_x27_2235_; lean_object* v_proof_2236_; uint8_t v_contextDependent_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v_e_x27_2235_ = lean_ctor_get(v_a_2138_, 0);
lean_inc_ref_n(v_e_x27_2235_, 2);
v_proof_2236_ = lean_ctor_get(v_a_2138_, 1);
lean_inc_ref(v_proof_2236_);
v_contextDependent_2237_ = lean_ctor_get_uint8(v_a_2138_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2138_, 2);
lean_inc_ref(v_inst_2074_);
lean_inc_ref(v_c_2073_);
v___x_2238_ = l_Lean_mkAppB(v___x_2132_, v_c_2073_, v_inst_2074_);
v___x_2239_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___x_2238_, v_a_2131_, v___x_2136_, v_e_x27_2235_, v_proof_2236_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v___x_2239_, 1);
v_e_x27_2141_ = v_e_x27_2235_;
v_proof_2142_ = v_a_2240_;
v_contextDependent_2143_ = v_contextDependent_2237_;
goto v___jp_2140_;
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec_ref(v_e_x27_2235_);
lean_dec_ref(v_fallback_2077_);
lean_dec_ref(v_b_2076_);
lean_dec_ref(v_a_2075_);
lean_dec_ref(v_inst_2074_);
lean_dec_ref(v_c_2073_);
lean_dec_ref(v_00_u03b1_2072_);
v_a_2241_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2239_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2239_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
v___jp_2140_:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_x27_2141_, v_a_2084_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref_known(v___x_2144_, 1);
v___x_2146_ = l_Lean_Expr_cleanupAnnotations(v_a_2145_);
v___x_2147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_2148_ = l_Lean_Expr_isConstOf(v___x_2146_, v___x_2147_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; uint8_t v___x_2150_; 
v___x_2149_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_2150_ = l_Lean_Expr_isConstOf(v___x_2146_, v___x_2149_);
lean_dec_ref(v___x_2146_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; 
lean_dec_ref(v_proof_2142_);
lean_dec_ref(v_b_2076_);
lean_dec_ref(v_a_2075_);
lean_dec_ref(v_inst_2074_);
lean_dec_ref(v_c_2073_);
lean_dec_ref(v_00_u03b1_2072_);
lean_inc(v_a_2086_);
lean_inc_ref(v_a_2085_);
lean_inc(v_a_2084_);
lean_inc_ref(v_a_2083_);
lean_inc(v_a_2082_);
lean_inc_ref(v_a_2081_);
lean_inc(v_a_2080_);
lean_inc_ref(v_a_2079_);
lean_inc(v_a_2078_);
v___x_2151_ = lean_apply_10(v_fallback_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_, lean_box(0));
return v___x_2151_;
}
else
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
lean_dec_ref(v_fallback_2077_);
v___x_2152_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2);
lean_inc_ref(v_inst_2074_);
lean_inc_ref(v_c_2073_);
v___x_2153_ = l_Lean_mkApp3(v___x_2152_, v_c_2073_, v_inst_2074_, v_proof_2142_);
v___x_2154_ = l_Lean_Meta_Sym_shareCommon(v___x_2153_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc_n(v_a_2155_, 2);
lean_dec_ref_known(v___x_2154_, 1);
v___x_2156_ = lean_mk_empty_array_with_capacity(v___x_2133_);
v___x_2157_ = lean_array_push(v___x_2156_, v_a_2155_);
lean_inc_ref(v_a_2075_);
v___x_2158_ = l_Lean_Expr_betaRev(v_a_2075_, v___x_2157_, v___x_2139_, v___x_2139_);
lean_dec_ref(v___x_2157_);
v___x_2159_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2158_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2172_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2162_ = v___x_2159_;
v_isShared_2163_ = v_isSharedCheck_2172_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2159_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2172_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1));
v___x_2165_ = l_Lean_Expr_constLevels_x21(v_f_2071_);
v___x_2166_ = l_Lean_mkConst(v___x_2164_, v___x_2165_);
v___x_2167_ = l_Lean_mkApp6(v___x_2166_, v_00_u03b1_2072_, v_c_2073_, v_inst_2074_, v_a_2075_, v_b_2076_, v_a_2155_);
v___x_2168_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2168_, 0, v_a_2160_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
lean_ctor_set_uint8(v___x_2168_, sizeof(void*)*2, v___x_2139_);
lean_ctor_set_uint8(v___x_2168_, sizeof(void*)*2 + 1, v_contextDependent_2143_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v___x_2168_);
v___x_2170_ = v___x_2162_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_a_2155_);
lean_dec_ref(v_b_2076_);
lean_dec_ref(v_a_2075_);
lean_dec_ref(v_inst_2074_);
lean_dec_ref(v_c_2073_);
lean_dec_ref(v_00_u03b1_2072_);
v_a_2173_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2159_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2159_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec_ref(v_b_2076_);
lean_dec_ref(v_a_2075_);
lean_dec_ref(v_inst_2074_);
lean_dec_ref(v_c_2073_);
lean_dec_ref(v_00_u03b1_2072_);
v_a_2181_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2154_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2154_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
else
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_dec_ref(v___x_2146_);
lean_dec_ref(v_fallback_2077_);
v___x_2189_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5);
lean_inc_ref(v_inst_2074_);
lean_inc_ref(v_c_2073_);
v___x_2190_ = l_Lean_mkApp3(v___x_2189_, v_c_2073_, v_inst_2074_, v_proof_2142_);
v___x_2191_ = l_Lean_Meta_Sym_shareCommon(v___x_2190_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc_n(v_a_2192_, 2);
lean_dec_ref_known(v___x_2191_, 1);
v___x_2193_ = lean_mk_empty_array_with_capacity(v___x_2133_);
v___x_2194_ = lean_array_push(v___x_2193_, v_a_2192_);
lean_inc_ref(v_b_2076_);
v___x_2195_ = l_Lean_Expr_betaRev(v_b_2076_, v___x_2194_, v___x_2139_, v___x_2139_);
lean_dec_ref(v___x_2194_);
v___x_2196_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2195_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2209_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2199_ = v___x_2196_;
v_isShared_2200_ = v_isSharedCheck_2209_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2196_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2209_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2207_; 
v___x_2201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3));
v___x_2202_ = l_Lean_Expr_constLevels_x21(v_f_2071_);
v___x_2203_ = l_Lean_mkConst(v___x_2201_, v___x_2202_);
v___x_2204_ = l_Lean_mkApp6(v___x_2203_, v_00_u03b1_2072_, v_c_2073_, v_inst_2074_, v_a_2075_, v_b_2076_, v_a_2192_);
v___x_2205_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2205_, 0, v_a_2197_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
lean_ctor_set_uint8(v___x_2205_, sizeof(void*)*2, v___x_2139_);
lean_ctor_set_uint8(v___x_2205_, sizeof(void*)*2 + 1, v_contextDependent_2143_);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 0, v___x_2205_);
v___x_2207_ = v___x_2199_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec(v_a_2192_);
lean_dec_ref(v_b_2076_);
lean_dec_ref(v_a_2075_);
lean_dec_ref(v_inst_2074_);
lean_dec_ref(v_c_2073_);
lean_dec_ref(v_00_u03b1_2072_);
v_a_2210_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2196_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2196_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2215_; 
if (v_isShared_2213_ == 0)
{
v___x_2215_ = v___x_2212_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_a_2210_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec_ref(v_b_2076_);
lean_dec_ref(v_a_2075_);
lean_dec_ref(v_inst_2074_);
lean_dec_ref(v_c_2073_);
lean_dec_ref(v_00_u03b1_2072_);
v_a_2218_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2191_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2191_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec_ref(v_proof_2142_);
lean_dec_ref(v_fallback_2077_);
lean_dec_ref(v_b_2076_);
lean_dec_ref(v_a_2075_);
lean_dec_ref(v_inst_2074_);
lean_dec_ref(v_c_2073_);
lean_dec_ref(v_00_u03b1_2072_);
v_a_2226_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2144_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2144_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2136_);
lean_dec(v_a_2131_);
lean_dec_ref(v_fallback_2077_);
lean_dec_ref(v_b_2076_);
lean_dec_ref(v_a_2075_);
lean_dec_ref(v_inst_2074_);
lean_dec_ref(v_c_2073_);
lean_dec_ref(v_00_u03b1_2072_);
return v___x_2137_;
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_dec_ref(v_fallback_2077_);
lean_dec_ref(v_b_2076_);
lean_dec_ref(v_a_2075_);
lean_dec_ref(v_inst_2074_);
lean_dec_ref(v_c_2073_);
lean_dec_ref(v_00_u03b1_2072_);
v_a_2249_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2130_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2130_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec_ref(v_fallback_2077_);
lean_dec_ref(v_b_2076_);
lean_dec_ref(v_a_2075_);
lean_dec_ref(v_inst_2074_);
lean_dec_ref(v_c_2073_);
lean_dec_ref(v_00_u03b1_2072_);
v_a_2257_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2092_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2092_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___boxed(lean_object** _args){
lean_object* v_f_2265_ = _args[0];
lean_object* v_00_u03b1_2266_ = _args[1];
lean_object* v_c_2267_ = _args[2];
lean_object* v_inst_2268_ = _args[3];
lean_object* v_a_2269_ = _args[4];
lean_object* v_b_2270_ = _args[5];
lean_object* v_fallback_2271_ = _args[6];
lean_object* v_a_2272_ = _args[7];
lean_object* v_a_2273_ = _args[8];
lean_object* v_a_2274_ = _args[9];
lean_object* v_a_2275_ = _args[10];
lean_object* v_a_2276_ = _args[11];
lean_object* v_a_2277_ = _args[12];
lean_object* v_a_2278_ = _args[13];
lean_object* v_a_2279_ = _args[14];
lean_object* v_a_2280_ = _args[15];
lean_object* v_a_2281_ = _args[16];
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v_f_2265_, v_00_u03b1_2266_, v_c_2267_, v_inst_2268_, v_a_2269_, v_b_2270_, v_fallback_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_);
lean_dec(v_a_2280_);
lean_dec_ref(v_a_2279_);
lean_dec(v_a_2278_);
lean_dec_ref(v_a_2277_);
lean_dec(v_a_2276_);
lean_dec_ref(v_a_2275_);
lean_dec(v_a_2274_);
lean_dec_ref(v_a_2273_);
lean_dec(v_a_2272_);
lean_dec_ref(v_f_2265_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr(lean_object* v_f_2283_, lean_object* v_00_u03b1_2284_, lean_object* v_c_2285_, lean_object* v_inst_2286_, lean_object* v_a_2287_, lean_object* v_b_2288_, lean_object* v_c_x27_2289_, lean_object* v_h_2290_, lean_object* v_inst_x27_2291_, lean_object* v_fallback_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v___x_2303_; uint8_t v___x_2304_; lean_object* v___x_2305_; lean_object* v___f_2306_; lean_object* v___x_2307_; 
v___x_2303_ = lean_unsigned_to_nat(0u);
v___x_2304_ = 5;
v___x_2305_ = lean_box(v___x_2304_);
lean_inc_ref(v_inst_x27_2291_);
v___f_2306_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2306_, 0, v___x_2305_);
lean_closure_set(v___f_2306_, 1, v_inst_x27_2291_);
lean_closure_set(v___f_2306_, 2, v___x_2303_);
v___x_2307_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2306_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
lean_dec_ref_known(v___x_2307_, 1);
if (lean_obj_tag(v_a_2308_) == 0)
{
lean_object* v___x_2309_; 
lean_inc(v_a_2301_);
lean_inc_ref(v_a_2300_);
lean_inc(v_a_2299_);
lean_inc_ref(v_a_2298_);
lean_inc(v_a_2297_);
lean_inc_ref(v_a_2296_);
lean_inc(v_a_2295_);
lean_inc_ref(v_a_2294_);
lean_inc(v_a_2293_);
lean_inc_ref(v_inst_x27_2291_);
v___x_2309_ = lean_sym_simp(v_inst_x27_2291_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
lean_dec_ref_known(v___x_2309_, 1);
if (lean_obj_tag(v_a_2310_) == 0)
{
uint8_t v_contextDependent_2311_; lean_object* v___x_2312_; 
v_contextDependent_2311_ = lean_ctor_get_uint8(v_a_2310_, 1);
lean_dec_ref_known(v_a_2310_, 0);
v___x_2312_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(v_f_2283_, v_00_u03b1_2284_, v_c_2285_, v_inst_2286_, v_a_2287_, v_b_2288_, v_c_x27_2289_, v_h_2290_, v_inst_x27_2291_, v_fallback_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; uint8_t v___y_2315_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
if (v_contextDependent_2311_ == 0)
{
lean_dec(v_a_2313_);
return v___x_2312_;
}
else
{
if (lean_obj_tag(v_a_2313_) == 0)
{
uint8_t v_contextDependent_2325_; 
v_contextDependent_2325_ = lean_ctor_get_uint8(v_a_2313_, 1);
v___y_2315_ = v_contextDependent_2325_;
goto v___jp_2314_;
}
else
{
uint8_t v_contextDependent_2326_; 
v_contextDependent_2326_ = lean_ctor_get_uint8(v_a_2313_, sizeof(void*)*2 + 1);
v___y_2315_ = v_contextDependent_2326_;
goto v___jp_2314_;
}
}
v___jp_2314_:
{
if (v___y_2315_ == 0)
{
lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2323_; 
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2323_ == 0)
{
lean_object* v_unused_2324_; 
v_unused_2324_ = lean_ctor_get(v___x_2312_, 0);
lean_dec(v_unused_2324_);
v___x_2317_ = v___x_2312_;
v_isShared_2318_ = v_isSharedCheck_2323_;
goto v_resetjp_2316_;
}
else
{
lean_dec(v___x_2312_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2323_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2319_; lean_object* v___x_2321_; 
v___x_2319_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2313_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 0, v___x_2319_);
v___x_2321_ = v___x_2317_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2319_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
else
{
lean_dec(v_a_2313_);
return v___x_2312_;
}
}
}
else
{
return v___x_2312_;
}
}
else
{
lean_object* v_e_x27_2327_; uint8_t v_contextDependent_2328_; lean_object* v___x_2329_; 
lean_dec_ref(v_inst_x27_2291_);
v_e_x27_2327_ = lean_ctor_get(v_a_2310_, 0);
lean_inc_ref(v_e_x27_2327_);
v_contextDependent_2328_ = lean_ctor_get_uint8(v_a_2310_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2310_, 2);
v___x_2329_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(v_f_2283_, v_00_u03b1_2284_, v_c_2285_, v_inst_2286_, v_a_2287_, v_b_2288_, v_c_x27_2289_, v_h_2290_, v_e_x27_2327_, v_fallback_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; uint8_t v___y_2332_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
if (v_contextDependent_2328_ == 0)
{
lean_dec(v_a_2330_);
return v___x_2329_;
}
else
{
if (lean_obj_tag(v_a_2330_) == 0)
{
uint8_t v_contextDependent_2342_; 
v_contextDependent_2342_ = lean_ctor_get_uint8(v_a_2330_, 1);
v___y_2332_ = v_contextDependent_2342_;
goto v___jp_2331_;
}
else
{
uint8_t v_contextDependent_2343_; 
v_contextDependent_2343_ = lean_ctor_get_uint8(v_a_2330_, sizeof(void*)*2 + 1);
v___y_2332_ = v_contextDependent_2343_;
goto v___jp_2331_;
}
}
v___jp_2331_:
{
if (v___y_2332_ == 0)
{
lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2340_; 
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2340_ == 0)
{
lean_object* v_unused_2341_; 
v_unused_2341_ = lean_ctor_get(v___x_2329_, 0);
lean_dec(v_unused_2341_);
v___x_2334_ = v___x_2329_;
v_isShared_2335_ = v_isSharedCheck_2340_;
goto v_resetjp_2333_;
}
else
{
lean_dec(v___x_2329_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2340_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2336_; lean_object* v___x_2338_; 
v___x_2336_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2330_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 0, v___x_2336_);
v___x_2338_ = v___x_2334_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
else
{
lean_dec(v_a_2330_);
return v___x_2329_;
}
}
}
else
{
return v___x_2329_;
}
}
}
else
{
lean_dec_ref(v_fallback_2292_);
lean_dec_ref(v_inst_x27_2291_);
lean_dec_ref(v_h_2290_);
lean_dec_ref(v_c_x27_2289_);
lean_dec_ref(v_b_2288_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v_inst_2286_);
lean_dec_ref(v_c_2285_);
lean_dec_ref(v_00_u03b1_2284_);
return v___x_2309_;
}
}
else
{
lean_object* v_val_2344_; lean_object* v___x_2345_; 
v_val_2344_ = lean_ctor_get(v_a_2308_, 0);
lean_inc(v_val_2344_);
lean_dec_ref_known(v_a_2308_, 1);
v___x_2345_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2344_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc_n(v_a_2346_, 3);
lean_dec_ref_known(v___x_2345_, 1);
v___x_2347_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2);
v___x_2348_ = lean_unsigned_to_nat(1u);
v___x_2349_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8);
v___x_2350_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10);
v___x_2351_ = l_Lean_mkAppB(v___x_2349_, v___x_2350_, v_a_2346_);
lean_inc(v_a_2301_);
lean_inc_ref(v_a_2300_);
lean_inc(v_a_2299_);
lean_inc_ref(v_a_2298_);
lean_inc(v_a_2297_);
lean_inc_ref(v_a_2296_);
lean_inc(v_a_2295_);
lean_inc_ref(v_a_2294_);
lean_inc(v_a_2293_);
v___x_2352_ = lean_sym_simp(v_a_2346_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; uint8_t v___x_2354_; lean_object* v_e_x27_2356_; lean_object* v_proof_2357_; uint8_t v_contextDependent_2358_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc(v_a_2353_);
lean_dec_ref_known(v___x_2352_, 1);
v___x_2354_ = 0;
if (lean_obj_tag(v_a_2353_) == 0)
{
uint8_t v_contextDependent_2453_; 
v_contextDependent_2453_ = lean_ctor_get_uint8(v_a_2353_, 1);
lean_dec_ref_known(v_a_2353_, 0);
v_e_x27_2356_ = v_a_2346_;
v_proof_2357_ = v___x_2351_;
v_contextDependent_2358_ = v_contextDependent_2453_;
goto v___jp_2355_;
}
else
{
lean_object* v_e_x27_2454_; lean_object* v_proof_2455_; uint8_t v_contextDependent_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v_e_x27_2454_ = lean_ctor_get(v_a_2353_, 0);
lean_inc_ref_n(v_e_x27_2454_, 2);
v_proof_2455_ = lean_ctor_get(v_a_2353_, 1);
lean_inc_ref(v_proof_2455_);
v_contextDependent_2456_ = lean_ctor_get_uint8(v_a_2353_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2353_, 2);
lean_inc_ref(v_inst_x27_2291_);
lean_inc_ref(v_c_x27_2289_);
v___x_2457_ = l_Lean_mkAppB(v___x_2347_, v_c_x27_2289_, v_inst_x27_2291_);
v___x_2458_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___x_2457_, v_a_2346_, v___x_2351_, v_e_x27_2454_, v_proof_2455_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___x_2458_, 1);
v_e_x27_2356_ = v_e_x27_2454_;
v_proof_2357_ = v_a_2459_;
v_contextDependent_2358_ = v_contextDependent_2456_;
goto v___jp_2355_;
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec_ref(v_e_x27_2454_);
lean_dec_ref(v_fallback_2292_);
lean_dec_ref(v_inst_x27_2291_);
lean_dec_ref(v_h_2290_);
lean_dec_ref(v_c_x27_2289_);
lean_dec_ref(v_b_2288_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v_inst_2286_);
lean_dec_ref(v_c_2285_);
lean_dec_ref(v_00_u03b1_2284_);
v_a_2460_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2458_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2458_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
v___jp_2355_:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_x27_2356_, v_a_2299_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; uint8_t v___x_2363_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
lean_dec_ref_known(v___x_2359_, 1);
v___x_2361_ = l_Lean_Expr_cleanupAnnotations(v_a_2360_);
v___x_2362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_2363_ = l_Lean_Expr_isConstOf(v___x_2361_, v___x_2362_);
if (v___x_2363_ == 0)
{
lean_object* v___x_2364_; uint8_t v___x_2365_; 
v___x_2364_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_2365_ = l_Lean_Expr_isConstOf(v___x_2361_, v___x_2364_);
lean_dec_ref(v___x_2361_);
if (v___x_2365_ == 0)
{
lean_object* v___x_2366_; 
lean_dec_ref(v_proof_2357_);
lean_dec_ref(v_inst_x27_2291_);
lean_dec_ref(v_h_2290_);
lean_dec_ref(v_c_x27_2289_);
lean_dec_ref(v_b_2288_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v_inst_2286_);
lean_dec_ref(v_c_2285_);
lean_dec_ref(v_00_u03b1_2284_);
lean_inc(v_a_2301_);
lean_inc_ref(v_a_2300_);
lean_inc(v_a_2299_);
lean_inc_ref(v_a_2298_);
lean_inc(v_a_2297_);
lean_inc_ref(v_a_2296_);
lean_inc(v_a_2295_);
lean_inc_ref(v_a_2294_);
lean_inc(v_a_2293_);
v___x_2366_ = lean_apply_10(v_fallback_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, lean_box(0));
return v___x_2366_;
}
else
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
lean_dec_ref(v_fallback_2292_);
v___x_2367_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2);
lean_inc_ref(v_c_x27_2289_);
v___x_2368_ = l_Lean_mkApp3(v___x_2367_, v_c_x27_2289_, v_inst_x27_2291_, v_proof_2357_);
v___x_2369_ = l_Lean_Meta_Sym_shareCommon(v___x_2368_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc_n(v_a_2370_, 2);
lean_dec_ref_known(v___x_2369_, 1);
v___x_2371_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2);
lean_inc_ref(v_h_2290_);
lean_inc_ref(v_c_x27_2289_);
lean_inc_ref(v_c_2285_);
v___x_2372_ = l_Lean_mkApp4(v___x_2371_, v_c_2285_, v_c_x27_2289_, v_h_2290_, v_a_2370_);
v___x_2373_ = lean_mk_empty_array_with_capacity(v___x_2348_);
v___x_2374_ = lean_array_push(v___x_2373_, v___x_2372_);
lean_inc_ref(v_a_2287_);
v___x_2375_ = l_Lean_Expr_betaRev(v_a_2287_, v___x_2374_, v___x_2354_, v___x_2354_);
lean_dec_ref(v___x_2374_);
v___x_2376_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2375_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2389_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2389_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2389_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2387_; 
v___x_2381_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4));
v___x_2382_ = l_Lean_Expr_constLevels_x21(v_f_2283_);
v___x_2383_ = l_Lean_mkConst(v___x_2381_, v___x_2382_);
v___x_2384_ = l_Lean_mkApp8(v___x_2383_, v_00_u03b1_2284_, v_c_2285_, v_inst_2286_, v_a_2287_, v_b_2288_, v_c_x27_2289_, v_h_2290_, v_a_2370_);
v___x_2385_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2385_, 0, v_a_2377_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
lean_ctor_set_uint8(v___x_2385_, sizeof(void*)*2, v___x_2354_);
lean_ctor_set_uint8(v___x_2385_, sizeof(void*)*2 + 1, v_contextDependent_2358_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2385_);
v___x_2387_ = v___x_2379_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec(v_a_2370_);
lean_dec_ref(v_h_2290_);
lean_dec_ref(v_c_x27_2289_);
lean_dec_ref(v_b_2288_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v_inst_2286_);
lean_dec_ref(v_c_2285_);
lean_dec_ref(v_00_u03b1_2284_);
v_a_2390_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2376_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2376_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
lean_dec_ref(v_h_2290_);
lean_dec_ref(v_c_x27_2289_);
lean_dec_ref(v_b_2288_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v_inst_2286_);
lean_dec_ref(v_c_2285_);
lean_dec_ref(v_00_u03b1_2284_);
v_a_2398_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2369_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2369_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
}
else
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
lean_dec_ref(v___x_2361_);
lean_dec_ref(v_fallback_2292_);
v___x_2406_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5);
lean_inc_ref(v_c_x27_2289_);
v___x_2407_ = l_Lean_mkApp3(v___x_2406_, v_c_x27_2289_, v_inst_x27_2291_, v_proof_2357_);
v___x_2408_ = l_Lean_Meta_Sym_shareCommon(v___x_2407_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc_n(v_a_2409_, 2);
lean_dec_ref_known(v___x_2408_, 1);
v___x_2410_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7);
lean_inc_ref(v_h_2290_);
lean_inc_ref(v_c_x27_2289_);
lean_inc_ref(v_c_2285_);
v___x_2411_ = l_Lean_mkApp4(v___x_2410_, v_c_2285_, v_c_x27_2289_, v_h_2290_, v_a_2409_);
v___x_2412_ = lean_mk_empty_array_with_capacity(v___x_2348_);
v___x_2413_ = lean_array_push(v___x_2412_, v___x_2411_);
lean_inc_ref(v_b_2288_);
v___x_2414_ = l_Lean_Expr_betaRev(v_b_2288_, v___x_2413_, v___x_2354_, v___x_2354_);
lean_dec_ref(v___x_2413_);
v___x_2415_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2414_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2428_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2418_ = v___x_2415_;
v_isShared_2419_ = v_isSharedCheck_2428_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2428_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2426_; 
v___x_2420_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9));
v___x_2421_ = l_Lean_Expr_constLevels_x21(v_f_2283_);
v___x_2422_ = l_Lean_mkConst(v___x_2420_, v___x_2421_);
v___x_2423_ = l_Lean_mkApp8(v___x_2422_, v_00_u03b1_2284_, v_c_2285_, v_inst_2286_, v_a_2287_, v_b_2288_, v_c_x27_2289_, v_h_2290_, v_a_2409_);
v___x_2424_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2424_, 0, v_a_2416_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
lean_ctor_set_uint8(v___x_2424_, sizeof(void*)*2, v___x_2354_);
lean_ctor_set_uint8(v___x_2424_, sizeof(void*)*2 + 1, v_contextDependent_2358_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2424_);
v___x_2426_ = v___x_2418_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_dec(v_a_2409_);
lean_dec_ref(v_h_2290_);
lean_dec_ref(v_c_x27_2289_);
lean_dec_ref(v_b_2288_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v_inst_2286_);
lean_dec_ref(v_c_2285_);
lean_dec_ref(v_00_u03b1_2284_);
v_a_2429_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2415_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2415_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec_ref(v_h_2290_);
lean_dec_ref(v_c_x27_2289_);
lean_dec_ref(v_b_2288_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v_inst_2286_);
lean_dec_ref(v_c_2285_);
lean_dec_ref(v_00_u03b1_2284_);
v_a_2437_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2408_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2408_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_dec_ref(v_proof_2357_);
lean_dec_ref(v_fallback_2292_);
lean_dec_ref(v_inst_x27_2291_);
lean_dec_ref(v_h_2290_);
lean_dec_ref(v_c_x27_2289_);
lean_dec_ref(v_b_2288_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v_inst_2286_);
lean_dec_ref(v_c_2285_);
lean_dec_ref(v_00_u03b1_2284_);
v_a_2445_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2359_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2359_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2351_);
lean_dec(v_a_2346_);
lean_dec_ref(v_fallback_2292_);
lean_dec_ref(v_inst_x27_2291_);
lean_dec_ref(v_h_2290_);
lean_dec_ref(v_c_x27_2289_);
lean_dec_ref(v_b_2288_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v_inst_2286_);
lean_dec_ref(v_c_2285_);
lean_dec_ref(v_00_u03b1_2284_);
return v___x_2352_;
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec_ref(v_fallback_2292_);
lean_dec_ref(v_inst_x27_2291_);
lean_dec_ref(v_h_2290_);
lean_dec_ref(v_c_x27_2289_);
lean_dec_ref(v_b_2288_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v_inst_2286_);
lean_dec_ref(v_c_2285_);
lean_dec_ref(v_00_u03b1_2284_);
v_a_2468_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2345_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2345_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
}
else
{
lean_object* v_a_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
lean_dec_ref(v_fallback_2292_);
lean_dec_ref(v_inst_x27_2291_);
lean_dec_ref(v_h_2290_);
lean_dec_ref(v_c_x27_2289_);
lean_dec_ref(v_b_2288_);
lean_dec_ref(v_a_2287_);
lean_dec_ref(v_inst_2286_);
lean_dec_ref(v_c_2285_);
lean_dec_ref(v_00_u03b1_2284_);
v_a_2476_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2478_ = v___x_2307_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_a_2476_);
lean_dec(v___x_2307_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2476_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_2484_ = _args[0];
lean_object* v_00_u03b1_2485_ = _args[1];
lean_object* v_c_2486_ = _args[2];
lean_object* v_inst_2487_ = _args[3];
lean_object* v_a_2488_ = _args[4];
lean_object* v_b_2489_ = _args[5];
lean_object* v_c_x27_2490_ = _args[6];
lean_object* v_h_2491_ = _args[7];
lean_object* v_inst_x27_2492_ = _args[8];
lean_object* v_fallback_2493_ = _args[9];
lean_object* v_a_2494_ = _args[10];
lean_object* v_a_2495_ = _args[11];
lean_object* v_a_2496_ = _args[12];
lean_object* v_a_2497_ = _args[13];
lean_object* v_a_2498_ = _args[14];
lean_object* v_a_2499_ = _args[15];
lean_object* v_a_2500_ = _args[16];
lean_object* v_a_2501_ = _args[17];
lean_object* v_a_2502_ = _args[18];
lean_object* v_a_2503_ = _args[19];
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr(v_f_2484_, v_00_u03b1_2485_, v_c_2486_, v_inst_2487_, v_a_2488_, v_b_2489_, v_c_x27_2490_, v_h_2491_, v_inst_x27_2492_, v_fallback_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
lean_dec(v_a_2500_);
lean_dec_ref(v_a_2499_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
lean_dec(v_a_2496_);
lean_dec_ref(v_a_2495_);
lean_dec(v_a_2494_);
lean_dec_ref(v_f_2484_);
return v_res_2504_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_unsigned_to_nat(0u);
v___x_2509_ = l_Lean_mkBVar(v___x_2508_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2(lean_object* v_proof_2515_, lean_object* v_arg_2516_, lean_object* v_e_x27_2517_, lean_object* v_arg_2518_, uint8_t v_a_2519_, lean_object* v_arg_2520_, lean_object* v___x_2521_, lean_object* v_snd_2522_, lean_object* v_e_2523_, uint8_t v___x_2524_, uint8_t v_contextDependent_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = l_Lean_Meta_Sym_shareCommon(v_proof_2515_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v___x_2538_; uint8_t v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc_n(v_a_2537_, 2);
lean_dec_ref_known(v___x_2536_, 1);
v___x_2538_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__1));
v___x_2539_ = 0;
v___x_2540_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2);
v___x_2541_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__2);
lean_inc_ref_n(v_e_x27_2517_, 2);
lean_inc_ref(v_arg_2516_);
v___x_2542_ = l_Lean_mkApp4(v___x_2540_, v_arg_2516_, v_e_x27_2517_, v_a_2537_, v___x_2541_);
v___x_2543_ = lean_unsigned_to_nat(1u);
v___x_2544_ = lean_mk_empty_array_with_capacity(v___x_2543_);
lean_inc_ref(v___x_2544_);
v___x_2545_ = lean_array_push(v___x_2544_, v___x_2542_);
v___x_2546_ = l_Lean_Expr_betaRev(v_arg_2518_, v___x_2545_, v_a_2519_, v_a_2519_);
lean_dec_ref(v___x_2545_);
v___x_2547_ = l_Lean_mkLambda(v___x_2538_, v___x_2539_, v_e_x27_2517_, v___x_2546_);
v___x_2548_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2547_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc(v_a_2549_);
lean_dec_ref_known(v___x_2548_, 1);
lean_inc_ref_n(v_e_x27_2517_, 2);
v___x_2550_ = l_Lean_mkNot(v_e_x27_2517_);
v___x_2551_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7);
lean_inc(v_a_2537_);
v___x_2552_ = l_Lean_mkApp4(v___x_2551_, v_arg_2516_, v_e_x27_2517_, v_a_2537_, v___x_2541_);
v___x_2553_ = lean_array_push(v___x_2544_, v___x_2552_);
v___x_2554_ = l_Lean_Expr_betaRev(v_arg_2520_, v___x_2553_, v_a_2519_, v_a_2519_);
lean_dec_ref(v___x_2553_);
v___x_2555_ = l_Lean_mkLambda(v___x_2538_, v___x_2539_, v___x_2550_, v___x_2554_);
v___x_2556_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2555_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2558_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
lean_dec_ref_known(v___x_2556_, 1);
lean_inc_ref(v_snd_2522_);
lean_inc_ref(v_e_x27_2517_);
v___x_2558_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v___x_2521_, v_e_x27_2517_, v_snd_2522_, v_a_2549_, v_a_2557_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2570_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2561_ = v___x_2558_;
v_isShared_2562_ = v_isSharedCheck_2570_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2558_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2570_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2568_; 
v___x_2563_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__4));
v___x_2564_ = l_Lean_Expr_replaceFn(v_e_2523_, v___x_2563_);
v___x_2565_ = l_Lean_mkApp3(v___x_2564_, v_e_x27_2517_, v_snd_2522_, v_a_2537_);
v___x_2566_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2566_, 0, v_a_2559_);
lean_ctor_set(v___x_2566_, 1, v___x_2565_);
lean_ctor_set_uint8(v___x_2566_, sizeof(void*)*2, v___x_2524_);
lean_ctor_set_uint8(v___x_2566_, sizeof(void*)*2 + 1, v_contextDependent_2525_);
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2566_);
v___x_2568_ = v___x_2561_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v___x_2566_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
else
{
lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2578_; 
lean_dec(v_a_2537_);
lean_dec_ref(v_e_2523_);
lean_dec_ref(v_snd_2522_);
lean_dec_ref(v_e_x27_2517_);
v_a_2571_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2578_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2573_ = v___x_2558_;
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2558_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2578_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
lean_dec(v_a_2549_);
lean_dec(v_a_2537_);
lean_dec_ref(v_e_2523_);
lean_dec_ref(v_snd_2522_);
lean_dec_ref(v___x_2521_);
lean_dec_ref(v_e_x27_2517_);
v_a_2579_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2556_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2556_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v_a_2579_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
else
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2594_; 
lean_dec_ref(v___x_2544_);
lean_dec(v_a_2537_);
lean_dec_ref(v_e_2523_);
lean_dec_ref(v_snd_2522_);
lean_dec_ref(v___x_2521_);
lean_dec_ref(v_arg_2520_);
lean_dec_ref(v_e_x27_2517_);
lean_dec_ref(v_arg_2516_);
v_a_2587_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2589_ = v___x_2548_;
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2548_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2587_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec_ref(v_e_2523_);
lean_dec_ref(v_snd_2522_);
lean_dec_ref(v___x_2521_);
lean_dec_ref(v_arg_2520_);
lean_dec_ref(v_arg_2518_);
lean_dec_ref(v_e_x27_2517_);
lean_dec_ref(v_arg_2516_);
v_a_2595_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2536_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2536_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___boxed(lean_object** _args){
lean_object* v_proof_2603_ = _args[0];
lean_object* v_arg_2604_ = _args[1];
lean_object* v_e_x27_2605_ = _args[2];
lean_object* v_arg_2606_ = _args[3];
lean_object* v_a_2607_ = _args[4];
lean_object* v_arg_2608_ = _args[5];
lean_object* v___x_2609_ = _args[6];
lean_object* v_snd_2610_ = _args[7];
lean_object* v_e_2611_ = _args[8];
lean_object* v___x_2612_ = _args[9];
lean_object* v_contextDependent_2613_ = _args[10];
lean_object* v___y_2614_ = _args[11];
lean_object* v___y_2615_ = _args[12];
lean_object* v___y_2616_ = _args[13];
lean_object* v___y_2617_ = _args[14];
lean_object* v___y_2618_ = _args[15];
lean_object* v___y_2619_ = _args[16];
lean_object* v___y_2620_ = _args[17];
lean_object* v___y_2621_ = _args[18];
lean_object* v___y_2622_ = _args[19];
lean_object* v___y_2623_ = _args[20];
_start:
{
uint8_t v_a_30533__boxed_2624_; uint8_t v___x_30537__boxed_2625_; uint8_t v_contextDependent_30538__boxed_2626_; lean_object* v_res_2627_; 
v_a_30533__boxed_2624_ = lean_unbox(v_a_2607_);
v___x_30537__boxed_2625_ = lean_unbox(v___x_2612_);
v_contextDependent_30538__boxed_2626_ = lean_unbox(v_contextDependent_2613_);
v_res_2627_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2(v_proof_2603_, v_arg_2604_, v_e_x27_2605_, v_arg_2606_, v_a_30533__boxed_2624_, v_arg_2608_, v___x_2609_, v_snd_2610_, v_e_2611_, v___x_30537__boxed_2625_, v_contextDependent_30538__boxed_2626_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
return v_res_2627_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = lean_box(0);
v___x_2635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
v___x_2636_ = l_Lean_mkConst(v___x_2635_, v___x_2634_);
return v___x_2636_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2637_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4);
v___x_2638_ = lean_unsigned_to_nat(1u);
v___x_2639_ = lean_mk_empty_array_with_capacity(v___x_2638_);
v___x_2640_ = lean_array_push(v___x_2639_, v___x_2637_);
return v___x_2640_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2647_ = lean_box(0);
v___x_2648_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8));
v___x_2649_ = l_Lean_mkConst(v___x_2648_, v___x_2647_);
return v___x_2649_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2650_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
v___x_2651_ = lean_unsigned_to_nat(1u);
v___x_2652_ = lean_mk_empty_array_with_capacity(v___x_2651_);
v___x_2653_ = lean_array_push(v___x_2652_, v___x_2650_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(uint8_t v___x_2662_, lean_object* v_e_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v___x_2677_; uint8_t v___x_2678_; 
lean_inc_ref(v_e_2663_);
v___x_2677_ = l_Lean_Expr_cleanupAnnotations(v_e_2663_);
v___x_2678_ = l_Lean_Expr_isApp(v___x_2677_);
if (v___x_2678_ == 0)
{
lean_dec_ref(v___x_2677_);
lean_dec_ref(v_e_2663_);
goto v___jp_2674_;
}
else
{
lean_object* v_arg_2679_; lean_object* v___x_2680_; uint8_t v___x_2681_; 
v_arg_2679_ = lean_ctor_get(v___x_2677_, 1);
lean_inc_ref(v_arg_2679_);
v___x_2680_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2677_);
v___x_2681_ = l_Lean_Expr_isApp(v___x_2680_);
if (v___x_2681_ == 0)
{
lean_dec_ref(v___x_2680_);
lean_dec_ref(v_arg_2679_);
lean_dec_ref(v_e_2663_);
goto v___jp_2674_;
}
else
{
lean_object* v_arg_2682_; lean_object* v___x_2683_; uint8_t v___x_2684_; 
v_arg_2682_ = lean_ctor_get(v___x_2680_, 1);
lean_inc_ref(v_arg_2682_);
v___x_2683_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2680_);
v___x_2684_ = l_Lean_Expr_isApp(v___x_2683_);
if (v___x_2684_ == 0)
{
lean_dec_ref(v___x_2683_);
lean_dec_ref(v_arg_2682_);
lean_dec_ref(v_arg_2679_);
lean_dec_ref(v_e_2663_);
goto v___jp_2674_;
}
else
{
lean_object* v_arg_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; 
v_arg_2685_ = lean_ctor_get(v___x_2683_, 1);
lean_inc_ref(v_arg_2685_);
v___x_2686_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2683_);
v___x_2687_ = l_Lean_Expr_isApp(v___x_2686_);
if (v___x_2687_ == 0)
{
lean_dec_ref(v___x_2686_);
lean_dec_ref(v_arg_2685_);
lean_dec_ref(v_arg_2682_);
lean_dec_ref(v_arg_2679_);
lean_dec_ref(v_e_2663_);
goto v___jp_2674_;
}
else
{
lean_object* v_arg_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; 
v_arg_2688_ = lean_ctor_get(v___x_2686_, 1);
lean_inc_ref(v_arg_2688_);
v___x_2689_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2686_);
v___x_2690_ = l_Lean_Expr_isApp(v___x_2689_);
if (v___x_2690_ == 0)
{
lean_dec_ref(v___x_2689_);
lean_dec_ref(v_arg_2688_);
lean_dec_ref(v_arg_2685_);
lean_dec_ref(v_arg_2682_);
lean_dec_ref(v_arg_2679_);
lean_dec_ref(v_e_2663_);
goto v___jp_2674_;
}
else
{
lean_object* v_arg_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; 
v_arg_2691_ = lean_ctor_get(v___x_2689_, 1);
lean_inc_ref(v_arg_2691_);
v___x_2692_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2689_);
v___x_2693_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1));
v___x_2694_ = l_Lean_Expr_isConstOf(v___x_2692_, v___x_2693_);
if (v___x_2694_ == 0)
{
lean_dec_ref(v___x_2692_);
lean_dec_ref(v_arg_2691_);
lean_dec_ref(v_arg_2688_);
lean_dec_ref(v_arg_2685_);
lean_dec_ref(v_arg_2682_);
lean_dec_ref(v_arg_2679_);
lean_dec_ref(v_e_2663_);
goto v___jp_2674_;
}
else
{
lean_object* v___x_2695_; 
lean_inc(v___y_2672_);
lean_inc_ref(v___y_2671_);
lean_inc(v___y_2670_);
lean_inc_ref(v___y_2669_);
lean_inc(v___y_2668_);
lean_inc_ref(v___y_2667_);
lean_inc(v___y_2666_);
lean_inc_ref(v___y_2665_);
lean_inc(v___y_2664_);
lean_inc_ref(v_arg_2688_);
v___x_2695_ = lean_sym_simp(v_arg_2688_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref_known(v___x_2695_, 1);
if (lean_obj_tag(v_a_2696_) == 0)
{
uint8_t v_contextDependent_2697_; lean_object* v___x_2698_; 
lean_dec_ref(v_e_2663_);
v_contextDependent_2697_ = lean_ctor_get_uint8(v_a_2696_, 1);
lean_dec_ref_known(v_a_2696_, 0);
v___x_2698_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_2688_, v___y_2667_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; uint8_t v___x_2700_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2698_, 1);
v___x_2700_ = lean_unbox(v_a_2699_);
if (v___x_2700_ == 0)
{
lean_object* v___x_2701_; 
v___x_2701_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_2688_, v___y_2667_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; uint8_t v___x_2703_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2701_, 1);
v___x_2703_ = lean_unbox(v_a_2702_);
lean_dec(v_a_2702_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2704_; lean_object* v___f_2705_; lean_object* v___x_2706_; 
lean_dec(v_a_2699_);
v___x_2704_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_2694_, v_contextDependent_2697_);
v___f_2705_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2705_, 0, v___x_2704_);
v___x_2706_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v___x_2692_, v_arg_2691_, v_arg_2688_, v_arg_2685_, v_arg_2682_, v_arg_2679_, v___f_2705_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec_ref(v___x_2692_);
return v___x_2706_;
}
else
{
lean_object* v___x_2707_; uint8_t v___x_2708_; uint8_t v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
lean_dec_ref(v_arg_2688_);
lean_dec_ref(v_arg_2685_);
v___x_2707_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5);
v___x_2708_ = lean_unbox(v_a_2699_);
v___x_2709_ = lean_unbox(v_a_2699_);
lean_inc_ref(v_arg_2679_);
v___x_2710_ = l_Lean_Expr_betaRev(v_arg_2679_, v___x_2707_, v___x_2708_, v___x_2709_);
v___x_2711_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2710_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2725_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2714_ = v___x_2711_;
v_isShared_2715_ = v_isSharedCheck_2725_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2711_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2725_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; uint8_t v___x_2721_; lean_object* v___x_2723_; 
v___x_2716_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6));
v___x_2717_ = l_Lean_Expr_constLevels_x21(v___x_2692_);
lean_dec_ref(v___x_2692_);
v___x_2718_ = l_Lean_mkConst(v___x_2716_, v___x_2717_);
v___x_2719_ = l_Lean_mkApp3(v___x_2718_, v_arg_2691_, v_arg_2682_, v_arg_2679_);
v___x_2720_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2720_, 0, v_a_2712_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
v___x_2721_ = lean_unbox(v_a_2699_);
lean_dec(v_a_2699_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*2, v___x_2721_);
lean_ctor_set_uint8(v___x_2720_, sizeof(void*)*2 + 1, v_contextDependent_2697_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 0, v___x_2720_);
v___x_2723_ = v___x_2714_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2720_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
else
{
lean_object* v_a_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2733_; 
lean_dec(v_a_2699_);
lean_dec_ref(v___x_2692_);
lean_dec_ref(v_arg_2691_);
lean_dec_ref(v_arg_2682_);
lean_dec_ref(v_arg_2679_);
v_a_2726_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2728_ = v___x_2711_;
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
else
{
lean_inc(v_a_2726_);
lean_dec(v___x_2711_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2733_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2731_; 
if (v_isShared_2729_ == 0)
{
v___x_2731_ = v___x_2728_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_a_2726_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec(v_a_2699_);
lean_dec_ref(v___x_2692_);
lean_dec_ref(v_arg_2691_);
lean_dec_ref(v_arg_2688_);
lean_dec_ref(v_arg_2685_);
lean_dec_ref(v_arg_2682_);
lean_dec_ref(v_arg_2679_);
v_a_2734_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2701_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2701_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
else
{
lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
lean_dec(v_a_2699_);
lean_dec_ref(v_arg_2688_);
lean_dec_ref(v_arg_2685_);
v___x_2742_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10);
lean_inc_ref(v_arg_2682_);
v___x_2743_ = l_Lean_Expr_betaRev(v_arg_2682_, v___x_2742_, v___x_2662_, v___x_2662_);
v___x_2744_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2743_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2757_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2747_ = v___x_2744_;
v_isShared_2748_ = v_isSharedCheck_2757_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2744_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2757_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2755_; 
v___x_2749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11));
v___x_2750_ = l_Lean_Expr_constLevels_x21(v___x_2692_);
lean_dec_ref(v___x_2692_);
v___x_2751_ = l_Lean_mkConst(v___x_2749_, v___x_2750_);
v___x_2752_ = l_Lean_mkApp3(v___x_2751_, v_arg_2691_, v_arg_2682_, v_arg_2679_);
v___x_2753_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2753_, 0, v_a_2745_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
lean_ctor_set_uint8(v___x_2753_, sizeof(void*)*2, v___x_2662_);
lean_ctor_set_uint8(v___x_2753_, sizeof(void*)*2 + 1, v_contextDependent_2697_);
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 0, v___x_2753_);
v___x_2755_ = v___x_2747_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec_ref(v___x_2692_);
lean_dec_ref(v_arg_2691_);
lean_dec_ref(v_arg_2682_);
lean_dec_ref(v_arg_2679_);
v_a_2758_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2744_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2744_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec_ref(v___x_2692_);
lean_dec_ref(v_arg_2691_);
lean_dec_ref(v_arg_2688_);
lean_dec_ref(v_arg_2685_);
lean_dec_ref(v_arg_2682_);
lean_dec_ref(v_arg_2679_);
v_a_2766_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2698_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2698_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
else
{
lean_object* v_e_x27_2774_; lean_object* v_proof_2775_; uint8_t v_contextDependent_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2906_; 
v_e_x27_2774_ = lean_ctor_get(v_a_2696_, 0);
v_proof_2775_ = lean_ctor_get(v_a_2696_, 1);
v_contextDependent_2776_ = lean_ctor_get_uint8(v_a_2696_, sizeof(void*)*2 + 1);
v_isSharedCheck_2906_ = !lean_is_exclusive(v_a_2696_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2778_ = v_a_2696_;
v_isShared_2779_ = v_isSharedCheck_2906_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_proof_2775_);
lean_inc(v_e_x27_2774_);
lean_dec(v_a_2696_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2906_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_2774_, v___y_2667_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; uint8_t v___x_2782_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v___x_2780_, 1);
v___x_2782_ = lean_unbox(v_a_2781_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2783_; 
v___x_2783_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_2774_, v___y_2667_);
lean_dec_ref(v_e_x27_2774_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_a_2784_; uint8_t v___x_2785_; 
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2784_);
lean_dec_ref_known(v___x_2783_, 1);
v___x_2785_ = lean_unbox(v_a_2784_);
if (v___x_2785_ == 0)
{
lean_object* v___x_2786_; 
lean_dec(v_a_2781_);
lean_del_object(v___x_2778_);
lean_dec_ref(v_proof_2775_);
lean_inc_ref(v_arg_2685_);
v___x_2786_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance(v_arg_2685_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v_fst_2788_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref_known(v___x_2786_, 1);
v_fst_2788_ = lean_ctor_get(v_a_2787_, 0);
lean_inc(v_fst_2788_);
if (lean_obj_tag(v_fst_2788_) == 0)
{
uint8_t v_contextDependent_2789_; lean_object* v___x_2790_; lean_object* v___f_2791_; lean_object* v___x_2792_; 
lean_dec(v_a_2787_);
lean_dec(v_a_2784_);
lean_dec_ref(v_e_2663_);
v_contextDependent_2789_ = lean_ctor_get_uint8(v_fst_2788_, 1);
lean_dec_ref_known(v_fst_2788_, 0);
v___x_2790_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_2694_, v_contextDependent_2789_);
v___f_2791_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2791_, 0, v___x_2790_);
v___x_2792_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v___x_2692_, v_arg_2691_, v_arg_2688_, v_arg_2685_, v_arg_2682_, v_arg_2679_, v___f_2791_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec_ref(v___x_2692_);
return v___x_2792_;
}
else
{
lean_object* v_snd_2793_; lean_object* v_e_x27_2794_; lean_object* v_proof_2795_; uint8_t v_contextDependent_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___f_2801_; lean_object* v___x_2802_; 
v_snd_2793_ = lean_ctor_get(v_a_2787_, 1);
lean_inc_n(v_snd_2793_, 2);
lean_dec(v_a_2787_);
v_e_x27_2794_ = lean_ctor_get(v_fst_2788_, 0);
lean_inc_ref_n(v_e_x27_2794_, 2);
v_proof_2795_ = lean_ctor_get(v_fst_2788_, 1);
lean_inc_ref_n(v_proof_2795_, 2);
v_contextDependent_2796_ = lean_ctor_get_uint8(v_fst_2788_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_2788_, 2);
v___x_2797_ = lean_unsigned_to_nat(4u);
v___x_2798_ = l_Lean_Expr_getBoundedAppFn(v___x_2797_, v_e_2663_);
v___x_2799_ = lean_box(v___x_2694_);
v___x_2800_ = lean_box(v_contextDependent_2796_);
lean_inc_ref(v_arg_2679_);
lean_inc_ref(v_arg_2682_);
lean_inc_ref(v_arg_2688_);
v___f_2801_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___boxed), 21, 11);
lean_closure_set(v___f_2801_, 0, v_proof_2795_);
lean_closure_set(v___f_2801_, 1, v_arg_2688_);
lean_closure_set(v___f_2801_, 2, v_e_x27_2794_);
lean_closure_set(v___f_2801_, 3, v_arg_2682_);
lean_closure_set(v___f_2801_, 4, v_a_2784_);
lean_closure_set(v___f_2801_, 5, v_arg_2679_);
lean_closure_set(v___f_2801_, 6, v___x_2798_);
lean_closure_set(v___f_2801_, 7, v_snd_2793_);
lean_closure_set(v___f_2801_, 8, v_e_2663_);
lean_closure_set(v___f_2801_, 9, v___x_2799_);
lean_closure_set(v___f_2801_, 10, v___x_2800_);
v___x_2802_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr(v___x_2692_, v_arg_2691_, v_arg_2688_, v_arg_2685_, v_arg_2682_, v_arg_2679_, v_e_x27_2794_, v_proof_2795_, v_snd_2793_, v___f_2801_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
lean_dec_ref(v___x_2692_);
return v___x_2802_;
}
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_dec(v_a_2784_);
lean_dec_ref(v___x_2692_);
lean_dec_ref(v_arg_2691_);
lean_dec_ref(v_arg_2688_);
lean_dec_ref(v_arg_2685_);
lean_dec_ref(v_arg_2682_);
lean_dec_ref(v_arg_2679_);
lean_dec_ref(v_e_2663_);
v_a_2803_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2786_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2786_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
else
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
lean_dec(v_a_2784_);
lean_dec_ref(v___x_2692_);
lean_dec_ref(v_arg_2691_);
lean_dec_ref(v_arg_2685_);
lean_dec_ref(v_arg_2682_);
lean_inc_ref(v_proof_2775_);
v___x_2811_ = l_Lean_Meta_mkOfEqFalseCore(v_arg_2688_, v_proof_2775_);
v___x_2812_ = l_Lean_Meta_Sym_shareCommon(v___x_2811_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; uint8_t v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2812_, 1);
v___x_2814_ = lean_unsigned_to_nat(1u);
v___x_2815_ = lean_mk_empty_array_with_capacity(v___x_2814_);
v___x_2816_ = lean_array_push(v___x_2815_, v_a_2813_);
v___x_2817_ = lean_unbox(v_a_2781_);
v___x_2818_ = lean_unbox(v_a_2781_);
v___x_2819_ = l_Lean_Expr_betaRev(v_arg_2679_, v___x_2816_, v___x_2817_, v___x_2818_);
lean_dec_ref(v___x_2816_);
v___x_2820_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2819_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2835_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2823_ = v___x_2820_;
v_isShared_2824_ = v_isSharedCheck_2835_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2820_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2835_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2829_; 
v___x_2825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13));
v___x_2826_ = l_Lean_Expr_replaceFn(v_e_2663_, v___x_2825_);
v___x_2827_ = l_Lean_Expr_app___override(v___x_2826_, v_proof_2775_);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 1, v___x_2827_);
lean_ctor_set(v___x_2778_, 0, v_a_2821_);
v___x_2829_ = v___x_2778_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2821_);
lean_ctor_set(v_reuseFailAlloc_2834_, 1, v___x_2827_);
v___x_2829_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
uint8_t v___x_2830_; lean_object* v___x_2832_; 
v___x_2830_ = lean_unbox(v_a_2781_);
lean_dec(v_a_2781_);
lean_ctor_set_uint8(v___x_2829_, sizeof(void*)*2, v___x_2830_);
lean_ctor_set_uint8(v___x_2829_, sizeof(void*)*2 + 1, v_contextDependent_2776_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 0, v___x_2829_);
v___x_2832_ = v___x_2823_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2829_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
lean_dec(v_a_2781_);
lean_del_object(v___x_2778_);
lean_dec_ref(v_proof_2775_);
lean_dec_ref(v_e_2663_);
v_a_2836_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2820_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2820_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
}
else
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
lean_dec(v_a_2781_);
lean_del_object(v___x_2778_);
lean_dec_ref(v_proof_2775_);
lean_dec_ref(v_arg_2679_);
lean_dec_ref(v_e_2663_);
v_a_2844_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___x_2812_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2812_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2844_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec(v_a_2781_);
lean_del_object(v___x_2778_);
lean_dec_ref(v_proof_2775_);
lean_dec_ref(v___x_2692_);
lean_dec_ref(v_arg_2691_);
lean_dec_ref(v_arg_2688_);
lean_dec_ref(v_arg_2685_);
lean_dec_ref(v_arg_2682_);
lean_dec_ref(v_arg_2679_);
lean_dec_ref(v_e_2663_);
v_a_2852_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2783_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2783_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
else
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
lean_dec(v_a_2781_);
lean_dec_ref(v_e_x27_2774_);
lean_dec_ref(v___x_2692_);
lean_dec_ref(v_arg_2691_);
lean_dec_ref(v_arg_2685_);
lean_dec_ref(v_arg_2679_);
lean_inc_ref(v_proof_2775_);
v___x_2860_ = l_Lean_Meta_mkOfEqTrueCore(v_arg_2688_, v_proof_2775_);
v___x_2861_ = l_Lean_Meta_Sym_shareCommon(v___x_2860_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
v___x_2863_ = lean_unsigned_to_nat(1u);
v___x_2864_ = lean_mk_empty_array_with_capacity(v___x_2863_);
v___x_2865_ = lean_array_push(v___x_2864_, v_a_2862_);
v___x_2866_ = l_Lean_Expr_betaRev(v_arg_2682_, v___x_2865_, v___x_2662_, v___x_2662_);
lean_dec_ref(v___x_2865_);
v___x_2867_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2866_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2881_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2870_ = v___x_2867_;
v_isShared_2871_ = v_isSharedCheck_2881_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2867_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2881_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2876_; 
v___x_2872_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15));
v___x_2873_ = l_Lean_Expr_replaceFn(v_e_2663_, v___x_2872_);
v___x_2874_ = l_Lean_Expr_app___override(v___x_2873_, v_proof_2775_);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 1, v___x_2874_);
lean_ctor_set(v___x_2778_, 0, v_a_2868_);
v___x_2876_ = v___x_2778_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2868_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v___x_2874_);
lean_ctor_set_uint8(v_reuseFailAlloc_2880_, sizeof(void*)*2 + 1, v_contextDependent_2776_);
v___x_2876_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
lean_object* v___x_2878_; 
lean_ctor_set_uint8(v___x_2876_, sizeof(void*)*2, v___x_2662_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 0, v___x_2876_);
v___x_2878_ = v___x_2870_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_del_object(v___x_2778_);
lean_dec_ref(v_proof_2775_);
lean_dec_ref(v_e_2663_);
v_a_2882_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2867_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2867_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_del_object(v___x_2778_);
lean_dec_ref(v_proof_2775_);
lean_dec_ref(v_arg_2682_);
lean_dec_ref(v_e_2663_);
v_a_2890_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2861_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2861_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_del_object(v___x_2778_);
lean_dec_ref(v_proof_2775_);
lean_dec_ref(v_e_x27_2774_);
lean_dec_ref(v___x_2692_);
lean_dec_ref(v_arg_2691_);
lean_dec_ref(v_arg_2688_);
lean_dec_ref(v_arg_2685_);
lean_dec_ref(v_arg_2682_);
lean_dec_ref(v_arg_2679_);
lean_dec_ref(v_e_2663_);
v_a_2898_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2780_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2780_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2692_);
lean_dec_ref(v_arg_2691_);
lean_dec_ref(v_arg_2688_);
lean_dec_ref(v_arg_2685_);
lean_dec_ref(v_arg_2682_);
lean_dec_ref(v_arg_2679_);
lean_dec_ref(v_e_2663_);
return v___x_2695_;
}
}
}
}
}
}
}
v___jp_2674_:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2675_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2675_, 0, v___x_2662_);
lean_ctor_set_uint8(v___x_2675_, 1, v___x_2662_);
v___x_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2675_);
return v___x_2676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed(lean_object* v___x_2907_, lean_object* v_e_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
uint8_t v___x_30804__boxed_2919_; lean_object* v_res_2920_; 
v___x_30804__boxed_2919_ = lean_unbox(v___x_2907_);
v_res_2920_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(v___x_30804__boxed_2919_, v_e_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv(lean_object* v_e_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_, lean_object* v_a_2926_, lean_object* v_a_2927_, lean_object* v_a_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v_numArgs_2932_; lean_object* v___x_2933_; uint8_t v___x_2934_; 
v_numArgs_2932_ = l_Lean_Expr_getAppNumArgs(v_e_2921_);
v___x_2933_ = lean_unsigned_to_nat(5u);
v___x_2934_ = lean_nat_dec_lt(v_numArgs_2932_, v___x_2933_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; lean_object* v___f_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2935_ = lean_box(v___x_2934_);
v___f_2936_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2936_, 0, v___x_2935_);
v___x_2937_ = lean_nat_sub(v_numArgs_2932_, v___x_2933_);
lean_dec(v_numArgs_2932_);
v___x_2938_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_2921_, v___x_2937_, v___f_2936_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_, v_a_2926_, v_a_2927_, v_a_2928_, v_a_2929_, v_a_2930_);
lean_dec(v___x_2937_);
return v___x_2938_;
}
else
{
uint8_t v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; 
lean_dec(v_numArgs_2932_);
lean_dec_ref(v_e_2921_);
v___x_2939_ = 0;
v___x_2940_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2940_, 0, v___x_2934_);
lean_ctor_set_uint8(v___x_2940_, 1, v___x_2939_);
v___x_2941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
return v___x_2941_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed(lean_object* v_e_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv(v_e_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_);
lean_dec(v_a_2951_);
lean_dec_ref(v_a_2950_);
lean_dec(v_a_2949_);
lean_dec_ref(v_a_2948_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
lean_dec(v_a_2943_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2972_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17_));
v___x_2973_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17_));
v___x_2974_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed), 11, 0);
v___x_2975_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_2972_, v___x_2973_, v___x_2974_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17____boxed(lean_object* v_a_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17_();
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_2979_; uint8_t v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2979_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17_));
v___x_2980_ = 0;
v___x_2981_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed), 11, 0);
v___x_2982_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_2979_, v___x_2980_, v___x_2981_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_19____boxed(lean_object* v_a_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_19_();
return v_res_2984_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2(void){
_start:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2990_ = lean_box(0);
v___x_2991_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1));
v___x_2992_ = l_Lean_mkConst(v___x_2991_, v___x_2990_);
return v___x_2992_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5(void){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2998_ = lean_box(0);
v___x_2999_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4));
v___x_3000_ = l_Lean_mkConst(v___x_2999_, v___x_2998_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(lean_object* v_p_3001_, lean_object* v_inst_3002_, lean_object* v_instToMatch_3003_, lean_object* v_fallback_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v___x_3015_; 
v___x_3015_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_instToMatch_3003_, v_a_3011_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3017_; uint8_t v___x_3018_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3015_, 1);
v___x_3017_ = l_Lean_Expr_cleanupAnnotations(v_a_3016_);
v___x_3018_ = l_Lean_Expr_isApp(v___x_3017_);
if (v___x_3018_ == 0)
{
lean_object* v___x_3019_; 
lean_dec_ref(v___x_3017_);
lean_dec_ref(v_inst_3002_);
lean_dec_ref(v_p_3001_);
lean_inc(v_a_3013_);
lean_inc_ref(v_a_3012_);
lean_inc(v_a_3011_);
lean_inc_ref(v_a_3010_);
lean_inc(v_a_3009_);
lean_inc_ref(v_a_3008_);
lean_inc(v_a_3007_);
lean_inc_ref(v_a_3006_);
lean_inc(v_a_3005_);
v___x_3019_ = lean_apply_10(v_fallback_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, lean_box(0));
return v___x_3019_;
}
else
{
lean_object* v_arg_3020_; lean_object* v___x_3021_; uint8_t v___x_3022_; 
v_arg_3020_ = lean_ctor_get(v___x_3017_, 1);
lean_inc_ref(v_arg_3020_);
v___x_3021_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3017_);
v___x_3022_ = l_Lean_Expr_isApp(v___x_3021_);
if (v___x_3022_ == 0)
{
lean_object* v___x_3023_; 
lean_dec_ref(v___x_3021_);
lean_dec_ref(v_arg_3020_);
lean_dec_ref(v_inst_3002_);
lean_dec_ref(v_p_3001_);
lean_inc(v_a_3013_);
lean_inc_ref(v_a_3012_);
lean_inc(v_a_3011_);
lean_inc_ref(v_a_3010_);
lean_inc(v_a_3009_);
lean_inc_ref(v_a_3008_);
lean_inc(v_a_3007_);
lean_inc_ref(v_a_3006_);
lean_inc(v_a_3005_);
v___x_3023_ = lean_apply_10(v_fallback_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, lean_box(0));
return v___x_3023_;
}
else
{
lean_object* v_arg_3024_; lean_object* v___x_3025_; uint8_t v___x_3026_; 
v_arg_3024_ = lean_ctor_get(v___x_3021_, 1);
lean_inc_ref(v_arg_3024_);
v___x_3025_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3021_);
v___x_3026_ = l_Lean_Expr_isApp(v___x_3025_);
if (v___x_3026_ == 0)
{
lean_object* v___x_3027_; 
lean_dec_ref(v___x_3025_);
lean_dec_ref(v_arg_3024_);
lean_dec_ref(v_arg_3020_);
lean_dec_ref(v_inst_3002_);
lean_dec_ref(v_p_3001_);
lean_inc(v_a_3013_);
lean_inc_ref(v_a_3012_);
lean_inc(v_a_3011_);
lean_inc_ref(v_a_3010_);
lean_inc(v_a_3009_);
lean_inc_ref(v_a_3008_);
lean_inc(v_a_3007_);
lean_inc_ref(v_a_3006_);
lean_inc(v_a_3005_);
v___x_3027_ = lean_apply_10(v_fallback_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, lean_box(0));
return v___x_3027_;
}
else
{
lean_object* v___x_3028_; lean_object* v___x_3029_; uint8_t v___x_3030_; 
v___x_3028_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3025_);
v___x_3029_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_3030_ = l_Lean_Expr_isConstOf(v___x_3028_, v___x_3029_);
lean_dec_ref(v___x_3028_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3031_; 
lean_dec_ref(v_arg_3024_);
lean_dec_ref(v_arg_3020_);
lean_dec_ref(v_inst_3002_);
lean_dec_ref(v_p_3001_);
lean_inc(v_a_3013_);
lean_inc_ref(v_a_3012_);
lean_inc(v_a_3011_);
lean_inc_ref(v_a_3010_);
lean_inc(v_a_3009_);
lean_inc_ref(v_a_3008_);
lean_inc(v_a_3007_);
lean_inc_ref(v_a_3006_);
lean_inc(v_a_3005_);
v___x_3031_ = lean_apply_10(v_fallback_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, lean_box(0));
return v___x_3031_;
}
else
{
lean_object* v___x_3032_; 
v___x_3032_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_3024_, v_a_3011_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; uint8_t v___x_3036_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
v___x_3034_ = l_Lean_Expr_cleanupAnnotations(v_a_3033_);
v___x_3035_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_3036_ = l_Lean_Expr_isConstOf(v___x_3034_, v___x_3035_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; uint8_t v___x_3038_; 
v___x_3037_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_3038_ = l_Lean_Expr_isConstOf(v___x_3034_, v___x_3037_);
lean_dec_ref(v___x_3034_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; 
lean_dec_ref(v_arg_3020_);
lean_dec_ref(v_inst_3002_);
lean_dec_ref(v_p_3001_);
lean_inc(v_a_3013_);
lean_inc_ref(v_a_3012_);
lean_inc(v_a_3011_);
lean_inc_ref(v_a_3010_);
lean_inc(v_a_3009_);
lean_inc_ref(v_a_3008_);
lean_inc(v_a_3007_);
lean_inc_ref(v_a_3006_);
lean_inc(v_a_3005_);
v___x_3039_ = lean_apply_10(v_fallback_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, lean_box(0));
return v___x_3039_;
}
else
{
lean_object* v___x_3040_; 
lean_dec_ref(v_fallback_3004_);
v___x_3040_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_3008_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3051_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3043_ = v___x_3040_;
v_isShared_3044_ = v_isSharedCheck_3051_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3040_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3051_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3045_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2);
v___x_3046_ = l_Lean_mkApp3(v___x_3045_, v_p_3001_, v_inst_3002_, v_arg_3020_);
v___x_3047_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3047_, 0, v_a_3041_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
lean_ctor_set_uint8(v___x_3047_, sizeof(void*)*2, v___x_3036_);
lean_ctor_set_uint8(v___x_3047_, sizeof(void*)*2 + 1, v___x_3036_);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v___x_3047_);
v___x_3049_ = v___x_3043_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3047_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
lean_dec_ref(v_arg_3020_);
lean_dec_ref(v_inst_3002_);
lean_dec_ref(v_p_3001_);
v_a_3052_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_3040_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3040_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
}
else
{
lean_object* v___x_3060_; 
lean_dec_ref(v___x_3034_);
lean_dec_ref(v_fallback_3004_);
v___x_3060_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_3008_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3072_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3063_ = v___x_3060_;
v_isShared_3064_ = v_isSharedCheck_3072_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3060_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3072_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; uint8_t v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3070_; 
v___x_3065_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5);
v___x_3066_ = l_Lean_mkApp3(v___x_3065_, v_p_3001_, v_inst_3002_, v_arg_3020_);
v___x_3067_ = 0;
v___x_3068_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3068_, 0, v_a_3061_);
lean_ctor_set(v___x_3068_, 1, v___x_3066_);
lean_ctor_set_uint8(v___x_3068_, sizeof(void*)*2, v___x_3067_);
lean_ctor_set_uint8(v___x_3068_, sizeof(void*)*2 + 1, v___x_3067_);
if (v_isShared_3064_ == 0)
{
lean_ctor_set(v___x_3063_, 0, v___x_3068_);
v___x_3070_ = v___x_3063_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3068_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
lean_dec_ref(v_arg_3020_);
lean_dec_ref(v_inst_3002_);
lean_dec_ref(v_p_3001_);
v_a_3073_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3060_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3060_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3078_; 
if (v_isShared_3076_ == 0)
{
v___x_3078_ = v___x_3075_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec_ref(v_arg_3020_);
lean_dec_ref(v_fallback_3004_);
lean_dec_ref(v_inst_3002_);
lean_dec_ref(v_p_3001_);
v_a_3081_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3032_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3032_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
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
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec_ref(v_fallback_3004_);
lean_dec_ref(v_inst_3002_);
lean_dec_ref(v_p_3001_);
v_a_3089_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3015_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3015_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___boxed(lean_object* v_p_3097_, lean_object* v_inst_3098_, lean_object* v_instToMatch_3099_, lean_object* v_fallback_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_3097_, v_inst_3098_, v_instToMatch_3099_, v_fallback_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_, v_a_3105_, v_a_3106_, v_a_3107_, v_a_3108_, v_a_3109_);
lean_dec(v_a_3109_);
lean_dec_ref(v_a_3108_);
lean_dec(v_a_3107_);
lean_dec_ref(v_a_3106_);
lean_dec(v_a_3105_);
lean_dec_ref(v_a_3104_);
lean_dec(v_a_3103_);
lean_dec_ref(v_a_3102_);
lean_dec(v_a_3101_);
return v_res_3111_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2(void){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3117_ = lean_box(0);
v___x_3118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1));
v___x_3119_ = l_Lean_mkConst(v___x_3118_, v___x_3117_);
return v___x_3119_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5(void){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3125_ = lean_box(0);
v___x_3126_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4));
v___x_3127_ = l_Lean_mkConst(v___x_3126_, v___x_3125_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(lean_object* v_p_3128_, lean_object* v_p_x27_3129_, lean_object* v_h_3130_, lean_object* v_inst_3131_, lean_object* v_inst_x27_3132_, lean_object* v_fallback_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_){
_start:
{
lean_object* v___x_3144_; 
v___x_3144_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_x27_3132_, v_a_3140_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3146_; uint8_t v___x_3147_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref_known(v___x_3144_, 1);
v___x_3146_ = l_Lean_Expr_cleanupAnnotations(v_a_3145_);
v___x_3147_ = l_Lean_Expr_isApp(v___x_3146_);
if (v___x_3147_ == 0)
{
lean_object* v___x_3148_; 
lean_dec_ref(v___x_3146_);
lean_dec_ref(v_inst_3131_);
lean_dec_ref(v_h_3130_);
lean_dec_ref(v_p_x27_3129_);
lean_dec_ref(v_p_3128_);
lean_inc(v_a_3142_);
lean_inc_ref(v_a_3141_);
lean_inc(v_a_3140_);
lean_inc_ref(v_a_3139_);
lean_inc(v_a_3138_);
lean_inc_ref(v_a_3137_);
lean_inc(v_a_3136_);
lean_inc_ref(v_a_3135_);
lean_inc(v_a_3134_);
v___x_3148_ = lean_apply_10(v_fallback_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, lean_box(0));
return v___x_3148_;
}
else
{
lean_object* v_arg_3149_; lean_object* v___x_3150_; uint8_t v___x_3151_; 
v_arg_3149_ = lean_ctor_get(v___x_3146_, 1);
lean_inc_ref(v_arg_3149_);
v___x_3150_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3146_);
v___x_3151_ = l_Lean_Expr_isApp(v___x_3150_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; 
lean_dec_ref(v___x_3150_);
lean_dec_ref(v_arg_3149_);
lean_dec_ref(v_inst_3131_);
lean_dec_ref(v_h_3130_);
lean_dec_ref(v_p_x27_3129_);
lean_dec_ref(v_p_3128_);
lean_inc(v_a_3142_);
lean_inc_ref(v_a_3141_);
lean_inc(v_a_3140_);
lean_inc_ref(v_a_3139_);
lean_inc(v_a_3138_);
lean_inc_ref(v_a_3137_);
lean_inc(v_a_3136_);
lean_inc_ref(v_a_3135_);
lean_inc(v_a_3134_);
v___x_3152_ = lean_apply_10(v_fallback_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, lean_box(0));
return v___x_3152_;
}
else
{
lean_object* v_arg_3153_; lean_object* v___x_3154_; uint8_t v___x_3155_; 
v_arg_3153_ = lean_ctor_get(v___x_3150_, 1);
lean_inc_ref(v_arg_3153_);
v___x_3154_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3150_);
v___x_3155_ = l_Lean_Expr_isApp(v___x_3154_);
if (v___x_3155_ == 0)
{
lean_object* v___x_3156_; 
lean_dec_ref(v___x_3154_);
lean_dec_ref(v_arg_3153_);
lean_dec_ref(v_arg_3149_);
lean_dec_ref(v_inst_3131_);
lean_dec_ref(v_h_3130_);
lean_dec_ref(v_p_x27_3129_);
lean_dec_ref(v_p_3128_);
lean_inc(v_a_3142_);
lean_inc_ref(v_a_3141_);
lean_inc(v_a_3140_);
lean_inc_ref(v_a_3139_);
lean_inc(v_a_3138_);
lean_inc_ref(v_a_3137_);
lean_inc(v_a_3136_);
lean_inc_ref(v_a_3135_);
lean_inc(v_a_3134_);
v___x_3156_ = lean_apply_10(v_fallback_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, lean_box(0));
return v___x_3156_;
}
else
{
lean_object* v___x_3157_; lean_object* v___x_3158_; uint8_t v___x_3159_; 
v___x_3157_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3154_);
v___x_3158_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_3159_ = l_Lean_Expr_isConstOf(v___x_3157_, v___x_3158_);
lean_dec_ref(v___x_3157_);
if (v___x_3159_ == 0)
{
lean_object* v___x_3160_; 
lean_dec_ref(v_arg_3153_);
lean_dec_ref(v_arg_3149_);
lean_dec_ref(v_inst_3131_);
lean_dec_ref(v_h_3130_);
lean_dec_ref(v_p_x27_3129_);
lean_dec_ref(v_p_3128_);
lean_inc(v_a_3142_);
lean_inc_ref(v_a_3141_);
lean_inc(v_a_3140_);
lean_inc_ref(v_a_3139_);
lean_inc(v_a_3138_);
lean_inc_ref(v_a_3137_);
lean_inc(v_a_3136_);
lean_inc_ref(v_a_3135_);
lean_inc(v_a_3134_);
v___x_3160_ = lean_apply_10(v_fallback_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, lean_box(0));
return v___x_3160_;
}
else
{
lean_object* v___x_3161_; 
v___x_3161_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_3153_, v_a_3140_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_a_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; uint8_t v___x_3165_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
lean_inc(v_a_3162_);
lean_dec_ref_known(v___x_3161_, 1);
v___x_3163_ = l_Lean_Expr_cleanupAnnotations(v_a_3162_);
v___x_3164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_3165_ = l_Lean_Expr_isConstOf(v___x_3163_, v___x_3164_);
if (v___x_3165_ == 0)
{
lean_object* v___x_3166_; uint8_t v___x_3167_; 
v___x_3166_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_3167_ = l_Lean_Expr_isConstOf(v___x_3163_, v___x_3166_);
lean_dec_ref(v___x_3163_);
if (v___x_3167_ == 0)
{
lean_object* v___x_3168_; 
lean_dec_ref(v_arg_3149_);
lean_dec_ref(v_inst_3131_);
lean_dec_ref(v_h_3130_);
lean_dec_ref(v_p_x27_3129_);
lean_dec_ref(v_p_3128_);
lean_inc(v_a_3142_);
lean_inc_ref(v_a_3141_);
lean_inc(v_a_3140_);
lean_inc_ref(v_a_3139_);
lean_inc(v_a_3138_);
lean_inc_ref(v_a_3137_);
lean_inc(v_a_3136_);
lean_inc_ref(v_a_3135_);
lean_inc(v_a_3134_);
v___x_3168_ = lean_apply_10(v_fallback_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, lean_box(0));
return v___x_3168_;
}
else
{
lean_object* v___x_3169_; 
lean_dec_ref(v_fallback_3133_);
v___x_3169_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_3137_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3180_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3172_ = v___x_3169_;
v_isShared_3173_ = v_isSharedCheck_3180_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3169_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3180_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3178_; 
v___x_3174_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2);
v___x_3175_ = l_Lean_mkApp5(v___x_3174_, v_p_3128_, v_p_x27_3129_, v_h_3130_, v_inst_3131_, v_arg_3149_);
v___x_3176_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3176_, 0, v_a_3170_);
lean_ctor_set(v___x_3176_, 1, v___x_3175_);
lean_ctor_set_uint8(v___x_3176_, sizeof(void*)*2, v___x_3165_);
lean_ctor_set_uint8(v___x_3176_, sizeof(void*)*2 + 1, v___x_3165_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 0, v___x_3176_);
v___x_3178_ = v___x_3172_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3176_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec_ref(v_arg_3149_);
lean_dec_ref(v_inst_3131_);
lean_dec_ref(v_h_3130_);
lean_dec_ref(v_p_x27_3129_);
lean_dec_ref(v_p_3128_);
v_a_3181_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3169_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3169_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
}
else
{
lean_object* v___x_3189_; 
lean_dec_ref(v___x_3163_);
lean_dec_ref(v_fallback_3133_);
v___x_3189_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_3137_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3201_; 
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3192_ = v___x_3189_;
v_isShared_3193_ = v_isSharedCheck_3201_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3189_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3201_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; uint8_t v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3199_; 
v___x_3194_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5);
v___x_3195_ = l_Lean_mkApp5(v___x_3194_, v_p_3128_, v_p_x27_3129_, v_h_3130_, v_inst_3131_, v_arg_3149_);
v___x_3196_ = 0;
v___x_3197_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3197_, 0, v_a_3190_);
lean_ctor_set(v___x_3197_, 1, v___x_3195_);
lean_ctor_set_uint8(v___x_3197_, sizeof(void*)*2, v___x_3196_);
lean_ctor_set_uint8(v___x_3197_, sizeof(void*)*2 + 1, v___x_3196_);
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 0, v___x_3197_);
v___x_3199_ = v___x_3192_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3197_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec_ref(v_arg_3149_);
lean_dec_ref(v_inst_3131_);
lean_dec_ref(v_h_3130_);
lean_dec_ref(v_p_x27_3129_);
lean_dec_ref(v_p_3128_);
v_a_3202_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3189_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3189_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
lean_dec_ref(v_arg_3149_);
lean_dec_ref(v_fallback_3133_);
lean_dec_ref(v_inst_3131_);
lean_dec_ref(v_h_3130_);
lean_dec_ref(v_p_x27_3129_);
lean_dec_ref(v_p_3128_);
v_a_3210_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___x_3161_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3161_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
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
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
lean_dec_ref(v_fallback_3133_);
lean_dec_ref(v_inst_3131_);
lean_dec_ref(v_h_3130_);
lean_dec_ref(v_p_x27_3129_);
lean_dec_ref(v_p_3128_);
v_a_3218_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3144_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3144_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___boxed(lean_object* v_p_3226_, lean_object* v_p_x27_3227_, lean_object* v_h_3228_, lean_object* v_inst_3229_, lean_object* v_inst_x27_3230_, lean_object* v_fallback_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_){
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_3226_, v_p_x27_3227_, v_h_3228_, v_inst_3229_, v_inst_x27_3230_, v_fallback_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_);
lean_dec(v_a_3240_);
lean_dec_ref(v_a_3239_);
lean_dec(v_a_3238_);
lean_dec_ref(v_a_3237_);
lean_dec(v_a_3236_);
lean_dec_ref(v_a_3235_);
lean_dec(v_a_3234_);
lean_dec_ref(v_a_3233_);
lean_dec(v_a_3232_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(lean_object* v_p_3243_, lean_object* v_inst_3244_, lean_object* v_fallback_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_){
_start:
{
lean_object* v___x_3256_; uint8_t v___x_3257_; lean_object* v___x_3258_; lean_object* v___f_3259_; lean_object* v___x_3260_; 
v___x_3256_ = lean_unsigned_to_nat(0u);
v___x_3257_ = 5;
v___x_3258_ = lean_box(v___x_3257_);
lean_inc_ref(v_inst_3244_);
v___f_3259_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3259_, 0, v___x_3258_);
lean_closure_set(v___f_3259_, 1, v_inst_3244_);
lean_closure_set(v___f_3259_, 2, v___x_3256_);
v___x_3260_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_3259_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_a_3261_);
lean_dec_ref_known(v___x_3260_, 1);
if (lean_obj_tag(v_a_3261_) == 0)
{
lean_object* v___x_3262_; 
lean_inc(v_a_3254_);
lean_inc_ref(v_a_3253_);
lean_inc(v_a_3252_);
lean_inc_ref(v_a_3251_);
lean_inc(v_a_3250_);
lean_inc_ref(v_a_3249_);
lean_inc(v_a_3248_);
lean_inc_ref(v_a_3247_);
lean_inc(v_a_3246_);
lean_inc_ref(v_inst_3244_);
v___x_3262_ = lean_sym_simp(v_inst_3244_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_a_3263_; 
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_a_3263_);
lean_dec_ref_known(v___x_3262_, 1);
if (lean_obj_tag(v_a_3263_) == 0)
{
uint8_t v_contextDependent_3264_; lean_object* v___x_3265_; 
v_contextDependent_3264_ = lean_ctor_get_uint8(v_a_3263_, 1);
lean_dec_ref_known(v_a_3263_, 0);
lean_inc_ref(v_inst_3244_);
v___x_3265_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_3243_, v_inst_3244_, v_inst_3244_, v_fallback_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; uint8_t v___y_3268_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3266_);
if (v_contextDependent_3264_ == 0)
{
lean_dec(v_a_3266_);
return v___x_3265_;
}
else
{
if (lean_obj_tag(v_a_3266_) == 0)
{
uint8_t v_contextDependent_3278_; 
v_contextDependent_3278_ = lean_ctor_get_uint8(v_a_3266_, 1);
v___y_3268_ = v_contextDependent_3278_;
goto v___jp_3267_;
}
else
{
uint8_t v_contextDependent_3279_; 
v_contextDependent_3279_ = lean_ctor_get_uint8(v_a_3266_, sizeof(void*)*2 + 1);
v___y_3268_ = v_contextDependent_3279_;
goto v___jp_3267_;
}
}
v___jp_3267_:
{
if (v___y_3268_ == 0)
{
lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3276_; 
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3276_ == 0)
{
lean_object* v_unused_3277_; 
v_unused_3277_ = lean_ctor_get(v___x_3265_, 0);
lean_dec(v_unused_3277_);
v___x_3270_ = v___x_3265_;
v_isShared_3271_ = v_isSharedCheck_3276_;
goto v_resetjp_3269_;
}
else
{
lean_dec(v___x_3265_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3276_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3272_; lean_object* v___x_3274_; 
v___x_3272_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3266_);
if (v_isShared_3271_ == 0)
{
lean_ctor_set(v___x_3270_, 0, v___x_3272_);
v___x_3274_ = v___x_3270_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3272_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
else
{
lean_dec(v_a_3266_);
return v___x_3265_;
}
}
}
else
{
return v___x_3265_;
}
}
else
{
lean_object* v_e_x27_3280_; uint8_t v_contextDependent_3281_; lean_object* v___x_3282_; 
v_e_x27_3280_ = lean_ctor_get(v_a_3263_, 0);
lean_inc_ref(v_e_x27_3280_);
v_contextDependent_3281_ = lean_ctor_get_uint8(v_a_3263_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_3263_, 2);
v___x_3282_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_3243_, v_inst_3244_, v_e_x27_3280_, v_fallback_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v_a_3283_; uint8_t v___y_3285_; 
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_a_3283_);
if (v_contextDependent_3281_ == 0)
{
lean_dec(v_a_3283_);
return v___x_3282_;
}
else
{
if (lean_obj_tag(v_a_3283_) == 0)
{
uint8_t v_contextDependent_3295_; 
v_contextDependent_3295_ = lean_ctor_get_uint8(v_a_3283_, 1);
v___y_3285_ = v_contextDependent_3295_;
goto v___jp_3284_;
}
else
{
uint8_t v_contextDependent_3296_; 
v_contextDependent_3296_ = lean_ctor_get_uint8(v_a_3283_, sizeof(void*)*2 + 1);
v___y_3285_ = v_contextDependent_3296_;
goto v___jp_3284_;
}
}
v___jp_3284_:
{
if (v___y_3285_ == 0)
{
lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3293_; 
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3293_ == 0)
{
lean_object* v_unused_3294_; 
v_unused_3294_ = lean_ctor_get(v___x_3282_, 0);
lean_dec(v_unused_3294_);
v___x_3287_ = v___x_3282_;
v_isShared_3288_ = v_isSharedCheck_3293_;
goto v_resetjp_3286_;
}
else
{
lean_dec(v___x_3282_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3293_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3289_; lean_object* v___x_3291_; 
v___x_3289_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3283_);
if (v_isShared_3288_ == 0)
{
lean_ctor_set(v___x_3287_, 0, v___x_3289_);
v___x_3291_ = v___x_3287_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v___x_3289_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
else
{
lean_dec(v_a_3283_);
return v___x_3282_;
}
}
}
else
{
return v___x_3282_;
}
}
}
else
{
lean_dec_ref(v_fallback_3245_);
lean_dec_ref(v_inst_3244_);
lean_dec_ref(v_p_3243_);
return v___x_3262_;
}
}
else
{
lean_object* v_val_3297_; lean_object* v___x_3298_; 
lean_dec_ref(v_fallback_3245_);
lean_dec_ref(v_inst_3244_);
lean_dec_ref(v_p_3243_);
v_val_3297_ = lean_ctor_get(v_a_3261_, 0);
lean_inc(v_val_3297_);
lean_dec_ref_known(v_a_3261_, 1);
v___x_3298_ = l_Lean_Meta_Sym_shareCommonInc(v_val_3297_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3311_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3301_ = v___x_3298_;
v_isShared_3302_ = v_isSharedCheck_3311_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3298_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3311_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; uint8_t v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3309_; 
v___x_3303_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8);
v___x_3304_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10);
lean_inc(v_a_3299_);
v___x_3305_ = l_Lean_mkAppB(v___x_3303_, v___x_3304_, v_a_3299_);
v___x_3306_ = 0;
v___x_3307_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3307_, 0, v_a_3299_);
lean_ctor_set(v___x_3307_, 1, v___x_3305_);
lean_ctor_set_uint8(v___x_3307_, sizeof(void*)*2, v___x_3306_);
lean_ctor_set_uint8(v___x_3307_, sizeof(void*)*2 + 1, v___x_3306_);
if (v_isShared_3302_ == 0)
{
lean_ctor_set(v___x_3301_, 0, v___x_3307_);
v___x_3309_ = v___x_3301_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___x_3307_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
else
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3319_; 
v_a_3312_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3314_ = v___x_3298_;
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3298_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3317_; 
if (v_isShared_3315_ == 0)
{
v___x_3317_ = v___x_3314_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
}
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_dec_ref(v_fallback_3245_);
lean_dec_ref(v_inst_3244_);
lean_dec_ref(v_p_3243_);
v_a_3320_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3260_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3260_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
return v___x_3325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable___boxed(lean_object* v_p_3328_, lean_object* v_inst_3329_, lean_object* v_fallback_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(v_p_3328_, v_inst_3329_, v_fallback_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_);
lean_dec(v_a_3339_);
lean_dec_ref(v_a_3338_);
lean_dec(v_a_3337_);
lean_dec_ref(v_a_3336_);
lean_dec(v_a_3335_);
lean_dec_ref(v_a_3334_);
lean_dec(v_a_3333_);
lean_dec_ref(v_a_3332_);
lean_dec(v_a_3331_);
return v_res_3341_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__2(void){
_start:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3347_ = lean_box(0);
v___x_3348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__1));
v___x_3349_ = l_Lean_mkConst(v___x_3348_, v___x_3347_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(lean_object* v_p_3350_, lean_object* v_p_x27_3351_, lean_object* v_h_3352_, lean_object* v_inst_3353_, lean_object* v_inst_x27_3354_, lean_object* v_fallback_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_){
_start:
{
lean_object* v___x_3366_; uint8_t v___x_3367_; lean_object* v___x_3368_; lean_object* v___f_3369_; lean_object* v___x_3370_; 
v___x_3366_ = lean_unsigned_to_nat(0u);
v___x_3367_ = 5;
v___x_3368_ = lean_box(v___x_3367_);
lean_inc_ref(v_inst_x27_3354_);
v___f_3369_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3369_, 0, v___x_3368_);
lean_closure_set(v___f_3369_, 1, v_inst_x27_3354_);
lean_closure_set(v___f_3369_, 2, v___x_3366_);
v___x_3370_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_3369_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
lean_inc(v_a_3371_);
lean_dec_ref_known(v___x_3370_, 1);
if (lean_obj_tag(v_a_3371_) == 0)
{
lean_object* v___x_3372_; 
lean_inc(v_a_3364_);
lean_inc_ref(v_a_3363_);
lean_inc(v_a_3362_);
lean_inc_ref(v_a_3361_);
lean_inc(v_a_3360_);
lean_inc_ref(v_a_3359_);
lean_inc(v_a_3358_);
lean_inc_ref(v_a_3357_);
lean_inc(v_a_3356_);
lean_inc_ref(v_inst_x27_3354_);
v___x_3372_ = lean_sym_simp(v_inst_x27_3354_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc(v_a_3373_);
lean_dec_ref_known(v___x_3372_, 1);
if (lean_obj_tag(v_a_3373_) == 0)
{
uint8_t v_contextDependent_3374_; lean_object* v___x_3375_; 
v_contextDependent_3374_ = lean_ctor_get_uint8(v_a_3373_, 1);
lean_dec_ref_known(v_a_3373_, 0);
v___x_3375_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_3350_, v_p_x27_3351_, v_h_3352_, v_inst_3353_, v_inst_x27_3354_, v_fallback_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; uint8_t v___y_3378_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc(v_a_3376_);
if (v_contextDependent_3374_ == 0)
{
lean_dec(v_a_3376_);
return v___x_3375_;
}
else
{
if (lean_obj_tag(v_a_3376_) == 0)
{
uint8_t v_contextDependent_3388_; 
v_contextDependent_3388_ = lean_ctor_get_uint8(v_a_3376_, 1);
v___y_3378_ = v_contextDependent_3388_;
goto v___jp_3377_;
}
else
{
uint8_t v_contextDependent_3389_; 
v_contextDependent_3389_ = lean_ctor_get_uint8(v_a_3376_, sizeof(void*)*2 + 1);
v___y_3378_ = v_contextDependent_3389_;
goto v___jp_3377_;
}
}
v___jp_3377_:
{
if (v___y_3378_ == 0)
{
lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3386_; 
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3386_ == 0)
{
lean_object* v_unused_3387_; 
v_unused_3387_ = lean_ctor_get(v___x_3375_, 0);
lean_dec(v_unused_3387_);
v___x_3380_ = v___x_3375_;
v_isShared_3381_ = v_isSharedCheck_3386_;
goto v_resetjp_3379_;
}
else
{
lean_dec(v___x_3375_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3386_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3382_; lean_object* v___x_3384_; 
v___x_3382_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3376_);
if (v_isShared_3381_ == 0)
{
lean_ctor_set(v___x_3380_, 0, v___x_3382_);
v___x_3384_ = v___x_3380_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3382_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
else
{
lean_dec(v_a_3376_);
return v___x_3375_;
}
}
}
else
{
return v___x_3375_;
}
}
else
{
lean_object* v_e_x27_3390_; uint8_t v_contextDependent_3391_; lean_object* v___x_3392_; 
lean_dec_ref(v_inst_x27_3354_);
v_e_x27_3390_ = lean_ctor_get(v_a_3373_, 0);
lean_inc_ref(v_e_x27_3390_);
v_contextDependent_3391_ = lean_ctor_get_uint8(v_a_3373_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_3373_, 2);
v___x_3392_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_3350_, v_p_x27_3351_, v_h_3352_, v_inst_3353_, v_e_x27_3390_, v_fallback_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; uint8_t v___y_3395_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
if (v_contextDependent_3391_ == 0)
{
lean_dec(v_a_3393_);
return v___x_3392_;
}
else
{
if (lean_obj_tag(v_a_3393_) == 0)
{
uint8_t v_contextDependent_3405_; 
v_contextDependent_3405_ = lean_ctor_get_uint8(v_a_3393_, 1);
v___y_3395_ = v_contextDependent_3405_;
goto v___jp_3394_;
}
else
{
uint8_t v_contextDependent_3406_; 
v_contextDependent_3406_ = lean_ctor_get_uint8(v_a_3393_, sizeof(void*)*2 + 1);
v___y_3395_ = v_contextDependent_3406_;
goto v___jp_3394_;
}
}
v___jp_3394_:
{
if (v___y_3395_ == 0)
{
lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3403_; 
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3403_ == 0)
{
lean_object* v_unused_3404_; 
v_unused_3404_ = lean_ctor_get(v___x_3392_, 0);
lean_dec(v_unused_3404_);
v___x_3397_ = v___x_3392_;
v_isShared_3398_ = v_isSharedCheck_3403_;
goto v_resetjp_3396_;
}
else
{
lean_dec(v___x_3392_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3403_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3399_; lean_object* v___x_3401_; 
v___x_3399_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3393_);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 0, v___x_3399_);
v___x_3401_ = v___x_3397_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3399_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
else
{
lean_dec(v_a_3393_);
return v___x_3392_;
}
}
}
else
{
return v___x_3392_;
}
}
}
else
{
lean_dec_ref(v_fallback_3355_);
lean_dec_ref(v_inst_x27_3354_);
lean_dec_ref(v_inst_3353_);
lean_dec_ref(v_h_3352_);
lean_dec_ref(v_p_x27_3351_);
lean_dec_ref(v_p_3350_);
return v___x_3372_;
}
}
else
{
lean_object* v_val_3407_; lean_object* v___x_3408_; 
lean_dec_ref(v_fallback_3355_);
v_val_3407_ = lean_ctor_get(v_a_3371_, 0);
lean_inc(v_val_3407_);
lean_dec_ref_known(v_a_3371_, 1);
v___x_3408_ = l_Lean_Meta_Sym_shareCommonInc(v_val_3407_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3423_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3411_ = v___x_3408_;
v_isShared_3412_ = v_isSharedCheck_3423_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3408_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3423_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; uint8_t v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3421_; 
v___x_3413_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8);
v___x_3414_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10);
lean_inc_n(v_a_3409_, 2);
v___x_3415_ = l_Lean_mkAppB(v___x_3413_, v___x_3414_, v_a_3409_);
v___x_3416_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__2);
v___x_3417_ = l_Lean_mkApp7(v___x_3416_, v_p_3350_, v_p_x27_3351_, v_h_3352_, v_inst_3353_, v_inst_x27_3354_, v_a_3409_, v___x_3415_);
v___x_3418_ = 0;
v___x_3419_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3419_, 0, v_a_3409_);
lean_ctor_set(v___x_3419_, 1, v___x_3417_);
lean_ctor_set_uint8(v___x_3419_, sizeof(void*)*2, v___x_3418_);
lean_ctor_set_uint8(v___x_3419_, sizeof(void*)*2 + 1, v___x_3418_);
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 0, v___x_3419_);
v___x_3421_ = v___x_3411_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3419_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_dec_ref(v_inst_x27_3354_);
lean_dec_ref(v_inst_3353_);
lean_dec_ref(v_h_3352_);
lean_dec_ref(v_p_x27_3351_);
lean_dec_ref(v_p_3350_);
v_a_3424_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3408_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3408_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
}
else
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
lean_dec_ref(v_fallback_3355_);
lean_dec_ref(v_inst_x27_3354_);
lean_dec_ref(v_inst_3353_);
lean_dec_ref(v_h_3352_);
lean_dec_ref(v_p_x27_3351_);
lean_dec_ref(v_p_3350_);
v_a_3432_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3434_ = v___x_3370_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3370_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3432_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___boxed(lean_object* v_p_3440_, lean_object* v_p_x27_3441_, lean_object* v_h_3442_, lean_object* v_inst_3443_, lean_object* v_inst_x27_3444_, lean_object* v_fallback_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_){
_start:
{
lean_object* v_res_3456_; 
v_res_3456_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(v_p_3440_, v_p_x27_3441_, v_h_3442_, v_inst_3443_, v_inst_x27_3444_, v_fallback_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_);
lean_dec(v_a_3454_);
lean_dec_ref(v_a_3453_);
lean_dec(v_a_3452_);
lean_dec_ref(v_a_3451_);
lean_dec(v_a_3450_);
lean_dec_ref(v_a_3449_);
lean_dec(v_a_3448_);
lean_dec_ref(v_a_3447_);
lean_dec(v_a_3446_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2(lean_object* v___x_3458_, lean_object* v_e_x27_3459_, lean_object* v_snd_3460_, lean_object* v___x_3461_, lean_object* v___x_3462_, lean_object* v___x_3463_, lean_object* v_arg_3464_, lean_object* v_proof_3465_, lean_object* v_arg_3466_, uint8_t v___x_3467_, uint8_t v_contextDependent_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
lean_object* v___x_3479_; 
v___x_3479_ = l_Lean_Meta_Sym_shareCommon(v___x_3458_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v___x_3481_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3480_);
lean_dec_ref_known(v___x_3479_, 1);
lean_inc_ref(v_snd_3460_);
lean_inc_ref(v_e_x27_3459_);
v___x_3481_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg(v_a_3480_, v_e_x27_3459_, v_snd_3460_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3494_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3484_ = v___x_3481_;
v_isShared_3485_ = v_isSharedCheck_3494_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3481_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3494_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3492_; 
v___x_3486_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2___closed__0));
v___x_3487_ = l_Lean_Name_mkStr3(v___x_3461_, v___x_3462_, v___x_3486_);
v___x_3488_ = l_Lean_mkConst(v___x_3487_, v___x_3463_);
v___x_3489_ = l_Lean_mkApp5(v___x_3488_, v_arg_3464_, v_e_x27_3459_, v_proof_3465_, v_arg_3466_, v_snd_3460_);
v___x_3490_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3490_, 0, v_a_3482_);
lean_ctor_set(v___x_3490_, 1, v___x_3489_);
lean_ctor_set_uint8(v___x_3490_, sizeof(void*)*2, v___x_3467_);
lean_ctor_set_uint8(v___x_3490_, sizeof(void*)*2 + 1, v_contextDependent_3468_);
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 0, v___x_3490_);
v___x_3492_ = v___x_3484_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
else
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
lean_dec_ref(v_arg_3466_);
lean_dec_ref(v_proof_3465_);
lean_dec_ref(v_arg_3464_);
lean_dec(v___x_3463_);
lean_dec_ref(v___x_3462_);
lean_dec_ref(v___x_3461_);
lean_dec_ref(v_snd_3460_);
lean_dec_ref(v_e_x27_3459_);
v_a_3495_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3497_ = v___x_3481_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3481_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3495_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
lean_dec_ref(v_arg_3466_);
lean_dec_ref(v_proof_3465_);
lean_dec_ref(v_arg_3464_);
lean_dec(v___x_3463_);
lean_dec_ref(v___x_3462_);
lean_dec_ref(v___x_3461_);
lean_dec_ref(v_snd_3460_);
lean_dec_ref(v_e_x27_3459_);
v_a_3503_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3479_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3479_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3503_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2___boxed(lean_object** _args){
lean_object* v___x_3511_ = _args[0];
lean_object* v_e_x27_3512_ = _args[1];
lean_object* v_snd_3513_ = _args[2];
lean_object* v___x_3514_ = _args[3];
lean_object* v___x_3515_ = _args[4];
lean_object* v___x_3516_ = _args[5];
lean_object* v_arg_3517_ = _args[6];
lean_object* v_proof_3518_ = _args[7];
lean_object* v_arg_3519_ = _args[8];
lean_object* v___x_3520_ = _args[9];
lean_object* v_contextDependent_3521_ = _args[10];
lean_object* v___y_3522_ = _args[11];
lean_object* v___y_3523_ = _args[12];
lean_object* v___y_3524_ = _args[13];
lean_object* v___y_3525_ = _args[14];
lean_object* v___y_3526_ = _args[15];
lean_object* v___y_3527_ = _args[16];
lean_object* v___y_3528_ = _args[17];
lean_object* v___y_3529_ = _args[18];
lean_object* v___y_3530_ = _args[19];
lean_object* v___y_3531_ = _args[20];
_start:
{
uint8_t v___x_20258__boxed_3532_; uint8_t v_contextDependent_20259__boxed_3533_; lean_object* v_res_3534_; 
v___x_20258__boxed_3532_ = lean_unbox(v___x_3520_);
v_contextDependent_20259__boxed_3533_ = lean_unbox(v_contextDependent_3521_);
v_res_3534_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2(v___x_3511_, v_e_x27_3512_, v_snd_3513_, v___x_3514_, v___x_3515_, v___x_3516_, v_arg_3517_, v_proof_3518_, v_arg_3519_, v___x_20258__boxed_3532_, v_contextDependent_20259__boxed_3533_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
lean_dec(v___y_3526_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec_ref(v___y_3523_);
lean_dec(v___y_3522_);
return v_res_3534_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3538_ = lean_box(0);
v___x_3539_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1));
v___x_3540_ = l_Lean_mkConst(v___x_3539_, v___x_3538_);
return v___x_3540_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3544_ = lean_box(0);
v___x_3545_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4));
v___x_3546_ = l_Lean_mkConst(v___x_3545_, v___x_3544_);
return v___x_3546_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3552_ = lean_box(0);
v___x_3553_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7));
v___x_3554_ = l_Lean_mkConst(v___x_3553_, v___x_3552_);
return v___x_3554_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3560_ = lean_box(0);
v___x_3561_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10));
v___x_3562_ = l_Lean_mkConst(v___x_3561_, v___x_3560_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0(uint8_t v___x_3563_, lean_object* v_e_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v___x_3578_; uint8_t v___x_3579_; 
v___x_3578_ = l_Lean_Expr_cleanupAnnotations(v_e_3564_);
v___x_3579_ = l_Lean_Expr_isApp(v___x_3578_);
if (v___x_3579_ == 0)
{
lean_dec_ref(v___x_3578_);
goto v___jp_3575_;
}
else
{
lean_object* v_arg_3580_; lean_object* v___x_3581_; uint8_t v___x_3582_; 
v_arg_3580_ = lean_ctor_get(v___x_3578_, 1);
lean_inc_ref(v_arg_3580_);
v___x_3581_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3578_);
v___x_3582_ = l_Lean_Expr_isApp(v___x_3581_);
if (v___x_3582_ == 0)
{
lean_dec_ref(v___x_3581_);
lean_dec_ref(v_arg_3580_);
goto v___jp_3575_;
}
else
{
lean_object* v_arg_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; uint8_t v___x_3588_; 
v_arg_3583_ = lean_ctor_get(v___x_3581_, 1);
lean_inc_ref(v_arg_3583_);
v___x_3584_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3581_);
v___x_3585_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0___closed__0));
v___x_3586_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__0));
v___x_3587_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__1));
v___x_3588_ = l_Lean_Expr_isConstOf(v___x_3584_, v___x_3587_);
lean_dec_ref(v___x_3584_);
if (v___x_3588_ == 0)
{
lean_dec_ref(v_arg_3583_);
lean_dec_ref(v_arg_3580_);
goto v___jp_3575_;
}
else
{
lean_object* v___x_3589_; 
lean_inc(v___y_3573_);
lean_inc_ref(v___y_3572_);
lean_inc(v___y_3571_);
lean_inc_ref(v___y_3570_);
lean_inc(v___y_3569_);
lean_inc_ref(v___y_3568_);
lean_inc(v___y_3567_);
lean_inc_ref(v___y_3566_);
lean_inc(v___y_3565_);
lean_inc_ref(v_arg_3583_);
v___x_3589_ = lean_sym_simp(v_arg_3583_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
lean_inc(v_a_3590_);
lean_dec_ref_known(v___x_3589_, 1);
if (lean_obj_tag(v_a_3590_) == 0)
{
uint8_t v_contextDependent_3591_; lean_object* v___x_3592_; 
v_contextDependent_3591_ = lean_ctor_get_uint8(v_a_3590_, 1);
lean_dec_ref_known(v_a_3590_, 0);
v___x_3592_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_3583_, v___y_3568_);
if (lean_obj_tag(v___x_3592_) == 0)
{
lean_object* v_a_3593_; uint8_t v___x_3594_; 
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
lean_inc(v_a_3593_);
lean_dec_ref_known(v___x_3592_, 1);
v___x_3594_ = lean_unbox(v_a_3593_);
if (v___x_3594_ == 0)
{
lean_object* v___x_3595_; 
v___x_3595_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_3583_, v___y_3568_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_a_3596_; uint8_t v___x_3597_; 
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_a_3596_);
lean_dec_ref_known(v___x_3595_, 1);
v___x_3597_ = lean_unbox(v_a_3596_);
lean_dec(v_a_3596_);
if (v___x_3597_ == 0)
{
lean_object* v___x_3598_; lean_object* v___f_3599_; lean_object* v___x_3600_; 
lean_dec(v_a_3593_);
v___x_3598_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_3588_, v_contextDependent_3591_);
v___f_3599_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_3599_, 0, v___x_3598_);
v___x_3600_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(v_arg_3583_, v_arg_3580_, v___f_3599_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
return v___x_3600_;
}
else
{
lean_object* v___x_3601_; 
lean_dec_ref(v_arg_3583_);
v___x_3601_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_3568_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3613_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3604_ = v___x_3601_;
v_isShared_3605_ = v_isSharedCheck_3613_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3601_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3613_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; uint8_t v___x_3609_; lean_object* v___x_3611_; 
v___x_3606_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2);
v___x_3607_ = l_Lean_Expr_app___override(v___x_3606_, v_arg_3580_);
v___x_3608_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3608_, 0, v_a_3602_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v___x_3609_ = lean_unbox(v_a_3593_);
lean_dec(v_a_3593_);
lean_ctor_set_uint8(v___x_3608_, sizeof(void*)*2, v___x_3609_);
lean_ctor_set_uint8(v___x_3608_, sizeof(void*)*2 + 1, v_contextDependent_3591_);
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 0, v___x_3608_);
v___x_3611_ = v___x_3604_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3608_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
lean_dec(v_a_3593_);
lean_dec_ref(v_arg_3580_);
v_a_3614_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3616_ = v___x_3601_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3601_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3614_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
}
else
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3629_; 
lean_dec(v_a_3593_);
lean_dec_ref(v_arg_3583_);
lean_dec_ref(v_arg_3580_);
v_a_3622_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3624_ = v___x_3595_;
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3595_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3627_; 
if (v_isShared_3625_ == 0)
{
v___x_3627_ = v___x_3624_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
}
else
{
lean_object* v___x_3630_; 
lean_dec(v_a_3593_);
lean_dec_ref(v_arg_3583_);
v___x_3630_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_3568_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3641_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3633_ = v___x_3630_;
v_isShared_3634_ = v_isSharedCheck_3641_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3630_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3641_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3639_; 
v___x_3635_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5);
v___x_3636_ = l_Lean_Expr_app___override(v___x_3635_, v_arg_3580_);
v___x_3637_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3637_, 0, v_a_3631_);
lean_ctor_set(v___x_3637_, 1, v___x_3636_);
lean_ctor_set_uint8(v___x_3637_, sizeof(void*)*2, v___x_3563_);
lean_ctor_set_uint8(v___x_3637_, sizeof(void*)*2 + 1, v_contextDependent_3591_);
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 0, v___x_3637_);
v___x_3639_ = v___x_3633_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3637_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
else
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
lean_dec_ref(v_arg_3580_);
v_a_3642_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3630_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3630_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
}
}
else
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3657_; 
lean_dec_ref(v_arg_3583_);
lean_dec_ref(v_arg_3580_);
v_a_3650_ = lean_ctor_get(v___x_3592_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3652_ = v___x_3592_;
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3592_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
if (v_isShared_3653_ == 0)
{
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
}
else
{
lean_object* v_e_x27_3658_; lean_object* v_proof_3659_; uint8_t v_contextDependent_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3756_; 
v_e_x27_3658_ = lean_ctor_get(v_a_3590_, 0);
v_proof_3659_ = lean_ctor_get(v_a_3590_, 1);
v_contextDependent_3660_ = lean_ctor_get_uint8(v_a_3590_, sizeof(void*)*2 + 1);
v_isSharedCheck_3756_ = !lean_is_exclusive(v_a_3590_);
if (v_isSharedCheck_3756_ == 0)
{
v___x_3662_ = v_a_3590_;
v_isShared_3663_ = v_isSharedCheck_3756_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_proof_3659_);
lean_inc(v_e_x27_3658_);
lean_dec(v_a_3590_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3756_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3664_; 
v___x_3664_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_3658_, v___y_3568_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; uint8_t v___x_3666_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_a_3665_);
lean_dec_ref_known(v___x_3664_, 1);
v___x_3666_ = lean_unbox(v_a_3665_);
if (v___x_3666_ == 0)
{
lean_object* v___x_3667_; 
v___x_3667_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_3658_, v___y_3568_);
lean_dec_ref(v_e_x27_3658_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; uint8_t v___x_3669_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc(v_a_3668_);
lean_dec_ref_known(v___x_3667_, 1);
v___x_3669_ = lean_unbox(v_a_3668_);
lean_dec(v_a_3668_);
if (v___x_3669_ == 0)
{
lean_object* v___x_3670_; 
lean_dec(v_a_3665_);
lean_del_object(v___x_3662_);
lean_dec_ref(v_proof_3659_);
lean_inc_ref(v_arg_3580_);
v___x_3670_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance(v_arg_3580_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v_fst_3672_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc(v_a_3671_);
lean_dec_ref_known(v___x_3670_, 1);
v_fst_3672_ = lean_ctor_get(v_a_3671_, 0);
lean_inc(v_fst_3672_);
if (lean_obj_tag(v_fst_3672_) == 0)
{
uint8_t v_contextDependent_3673_; lean_object* v___x_3674_; lean_object* v___f_3675_; lean_object* v___x_3676_; 
lean_dec(v_a_3671_);
v_contextDependent_3673_ = lean_ctor_get_uint8(v_fst_3672_, 1);
lean_dec_ref_known(v_fst_3672_, 0);
v___x_3674_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_3588_, v_contextDependent_3673_);
v___f_3675_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_3675_, 0, v___x_3674_);
v___x_3676_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(v_arg_3583_, v_arg_3580_, v___f_3675_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
return v___x_3676_;
}
else
{
lean_object* v_snd_3677_; lean_object* v_e_x27_3678_; lean_object* v_proof_3679_; uint8_t v_contextDependent_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___f_3685_; lean_object* v___x_3686_; 
v_snd_3677_ = lean_ctor_get(v_a_3671_, 1);
lean_inc_n(v_snd_3677_, 2);
lean_dec(v_a_3671_);
v_e_x27_3678_ = lean_ctor_get(v_fst_3672_, 0);
lean_inc_ref_n(v_e_x27_3678_, 2);
v_proof_3679_ = lean_ctor_get(v_fst_3672_, 1);
lean_inc_ref_n(v_proof_3679_, 2);
v_contextDependent_3680_ = lean_ctor_get_uint8(v_fst_3672_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_3672_, 2);
v___x_3681_ = lean_box(0);
v___x_3682_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2);
v___x_3683_ = lean_box(v___x_3588_);
v___x_3684_ = lean_box(v_contextDependent_3680_);
lean_inc_ref(v_arg_3580_);
lean_inc_ref(v_arg_3583_);
v___f_3685_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2___boxed), 21, 11);
lean_closure_set(v___f_3685_, 0, v___x_3682_);
lean_closure_set(v___f_3685_, 1, v_e_x27_3678_);
lean_closure_set(v___f_3685_, 2, v_snd_3677_);
lean_closure_set(v___f_3685_, 3, v___x_3585_);
lean_closure_set(v___f_3685_, 4, v___x_3586_);
lean_closure_set(v___f_3685_, 5, v___x_3681_);
lean_closure_set(v___f_3685_, 6, v_arg_3583_);
lean_closure_set(v___f_3685_, 7, v_proof_3679_);
lean_closure_set(v___f_3685_, 8, v_arg_3580_);
lean_closure_set(v___f_3685_, 9, v___x_3683_);
lean_closure_set(v___f_3685_, 10, v___x_3684_);
v___x_3686_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(v_arg_3583_, v_e_x27_3678_, v_proof_3679_, v_arg_3580_, v_snd_3677_, v___f_3685_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
return v___x_3686_;
}
}
else
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3694_; 
lean_dec_ref(v_arg_3583_);
lean_dec_ref(v_arg_3580_);
v_a_3687_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3689_ = v___x_3670_;
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3670_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3692_; 
if (v_isShared_3690_ == 0)
{
v___x_3692_ = v___x_3689_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
else
{
lean_object* v___x_3695_; 
v___x_3695_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_3568_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3709_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3698_ = v___x_3695_;
v_isShared_3699_ = v_isSharedCheck_3709_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3695_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3709_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3703_; 
v___x_3700_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8);
v___x_3701_ = l_Lean_mkApp3(v___x_3700_, v_arg_3583_, v_arg_3580_, v_proof_3659_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 1, v___x_3701_);
lean_ctor_set(v___x_3662_, 0, v_a_3696_);
v___x_3703_ = v___x_3662_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_a_3696_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v___x_3701_);
v___x_3703_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
uint8_t v___x_3704_; lean_object* v___x_3706_; 
v___x_3704_ = lean_unbox(v_a_3665_);
lean_dec(v_a_3665_);
lean_ctor_set_uint8(v___x_3703_, sizeof(void*)*2, v___x_3704_);
lean_ctor_set_uint8(v___x_3703_, sizeof(void*)*2 + 1, v_contextDependent_3660_);
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 0, v___x_3703_);
v___x_3706_ = v___x_3698_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3703_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
else
{
lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3717_; 
lean_dec(v_a_3665_);
lean_del_object(v___x_3662_);
lean_dec_ref(v_proof_3659_);
lean_dec_ref(v_arg_3583_);
lean_dec_ref(v_arg_3580_);
v_a_3710_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3712_ = v___x_3695_;
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3695_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3715_; 
if (v_isShared_3713_ == 0)
{
v___x_3715_ = v___x_3712_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3710_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
}
}
else
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3725_; 
lean_dec(v_a_3665_);
lean_del_object(v___x_3662_);
lean_dec_ref(v_proof_3659_);
lean_dec_ref(v_arg_3583_);
lean_dec_ref(v_arg_3580_);
v_a_3718_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3720_ = v___x_3667_;
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3667_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3723_; 
if (v_isShared_3721_ == 0)
{
v___x_3723_ = v___x_3720_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3718_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
}
else
{
lean_object* v___x_3726_; 
lean_dec(v_a_3665_);
lean_dec_ref(v_e_x27_3658_);
v___x_3726_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_3568_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3739_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3729_ = v___x_3726_;
v_isShared_3730_ = v_isSharedCheck_3739_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3726_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3739_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3734_; 
v___x_3731_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11);
v___x_3732_ = l_Lean_mkApp3(v___x_3731_, v_arg_3583_, v_arg_3580_, v_proof_3659_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 1, v___x_3732_);
lean_ctor_set(v___x_3662_, 0, v_a_3727_);
v___x_3734_ = v___x_3662_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3727_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v___x_3732_);
lean_ctor_set_uint8(v_reuseFailAlloc_3738_, sizeof(void*)*2 + 1, v_contextDependent_3660_);
v___x_3734_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
lean_object* v___x_3736_; 
lean_ctor_set_uint8(v___x_3734_, sizeof(void*)*2, v___x_3563_);
if (v_isShared_3730_ == 0)
{
lean_ctor_set(v___x_3729_, 0, v___x_3734_);
v___x_3736_ = v___x_3729_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3734_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
else
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3747_; 
lean_del_object(v___x_3662_);
lean_dec_ref(v_proof_3659_);
lean_dec_ref(v_arg_3583_);
lean_dec_ref(v_arg_3580_);
v_a_3740_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3742_ = v___x_3726_;
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3726_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3745_; 
if (v_isShared_3743_ == 0)
{
v___x_3745_ = v___x_3742_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3740_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
}
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
lean_del_object(v___x_3662_);
lean_dec_ref(v_proof_3659_);
lean_dec_ref(v_e_x27_3658_);
lean_dec_ref(v_arg_3583_);
lean_dec_ref(v_arg_3580_);
v_a_3748_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3664_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3664_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_3583_);
lean_dec_ref(v_arg_3580_);
return v___x_3589_;
}
}
}
}
v___jp_3575_:
{
lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3576_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3576_, 0, v___x_3563_);
lean_ctor_set_uint8(v___x_3576_, 1, v___x_3563_);
v___x_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3576_);
return v___x_3577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___boxed(lean_object* v___x_3757_, lean_object* v_e_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
uint8_t v___x_20445__boxed_3769_; lean_object* v_res_3770_; 
v___x_20445__boxed_3769_ = lean_unbox(v___x_3757_);
v_res_3770_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0(v___x_20445__boxed_3769_, v_e_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
return v_res_3770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv(lean_object* v_e_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_){
_start:
{
lean_object* v_numArgs_3782_; lean_object* v___x_3783_; uint8_t v___x_3784_; 
v_numArgs_3782_ = l_Lean_Expr_getAppNumArgs(v_e_3771_);
v___x_3783_ = lean_unsigned_to_nat(2u);
v___x_3784_ = lean_nat_dec_lt(v_numArgs_3782_, v___x_3783_);
if (v___x_3784_ == 0)
{
lean_object* v___x_3785_; lean_object* v___f_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3785_ = lean_box(v___x_3784_);
v___f_3786_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___boxed), 12, 1);
lean_closure_set(v___f_3786_, 0, v___x_3785_);
v___x_3787_ = lean_nat_sub(v_numArgs_3782_, v___x_3783_);
lean_dec(v_numArgs_3782_);
v___x_3788_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_3771_, v___x_3787_, v___f_3786_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
lean_dec(v___x_3787_);
return v___x_3788_;
}
else
{
uint8_t v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
lean_dec(v_numArgs_3782_);
lean_dec_ref(v_e_3771_);
v___x_3789_ = 0;
v___x_3790_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3790_, 0, v___x_3784_);
lean_ctor_set_uint8(v___x_3790_, 1, v___x_3789_);
v___x_3791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3790_);
return v___x_3791_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed(lean_object* v_e_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv(v_e_3792_, v_a_3793_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_);
lean_dec(v_a_3801_);
lean_dec_ref(v_a_3800_);
lean_dec(v_a_3799_);
lean_dec_ref(v_a_3798_);
lean_dec(v_a_3797_);
lean_dec_ref(v_a_3796_);
lean_dec(v_a_3795_);
lean_dec_ref(v_a_3794_);
lean_dec(v_a_3793_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_));
v___x_3820_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_));
v___x_3821_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed), 11, 0);
v___x_3822_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_3819_, v___x_3820_, v___x_3821_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14____boxed(lean_object* v_a_3823_){
_start:
{
lean_object* v_res_3824_; 
v_res_3824_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_();
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_3826_; uint8_t v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v___x_3826_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_));
v___x_3827_ = 0;
v___x_3828_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed), 11, 0);
v___x_3829_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_3826_, v___x_3827_, v___x_3828_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_16____boxed(lean_object* v_a_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_16_();
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond(lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_){
_start:
{
lean_object* v___x_3843_; 
v___x_3843_ = l_Lean_Meta_Sym_Simp_simpCond(v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_);
return v___x_3843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___boxed(lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond(v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_);
lean_dec(v_a_3853_);
lean_dec_ref(v_a_3852_);
lean_dec(v_a_3851_);
lean_dec_ref(v_a_3850_);
lean_dec(v_a_3849_);
lean_dec_ref(v_a_3848_);
lean_dec(v_a_3847_);
lean_dec_ref(v_a_3846_);
lean_dec(v_a_3845_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_(){
_start:
{
lean_object* v___f_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___f_3882_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_));
v___x_3883_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_));
v___x_3884_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_));
v___x_3885_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_3883_, v___x_3884_, v___f_3882_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16____boxed(lean_object* v_a_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_();
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_18_(){
_start:
{
lean_object* v___f_3889_; lean_object* v___x_3890_; uint8_t v___x_3891_; lean_object* v___x_3892_; 
v___f_3889_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_));
v___x_3890_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_));
v___x_3891_ = 0;
v___x_3892_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_3890_, v___x_3891_, v___f_3889_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_18____boxed(lean_object* v_a_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_18_();
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(lean_object* v_msgData_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v___x_3901_; lean_object* v_env_3902_; lean_object* v___x_3903_; lean_object* v_mctx_3904_; lean_object* v_lctx_3905_; lean_object* v_options_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3901_ = lean_st_ref_get(v___y_3899_);
v_env_3902_ = lean_ctor_get(v___x_3901_, 0);
lean_inc_ref(v_env_3902_);
lean_dec(v___x_3901_);
v___x_3903_ = lean_st_ref_get(v___y_3897_);
v_mctx_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc_ref(v_mctx_3904_);
lean_dec(v___x_3903_);
v_lctx_3905_ = lean_ctor_get(v___y_3896_, 2);
v_options_3906_ = lean_ctor_get(v___y_3898_, 2);
lean_inc_ref(v_options_3906_);
lean_inc_ref(v_lctx_3905_);
v___x_3907_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3907_, 0, v_env_3902_);
lean_ctor_set(v___x_3907_, 1, v_mctx_3904_);
lean_ctor_set(v___x_3907_, 2, v_lctx_3905_);
lean_ctor_set(v___x_3907_, 3, v_options_3906_);
v___x_3908_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
lean_ctor_set(v___x_3908_, 1, v_msgData_3895_);
v___x_3909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3908_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0___boxed(lean_object* v_msgData_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
lean_object* v_res_3916_; 
v_res_3916_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(v_msgData_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
lean_dec(v___y_3912_);
lean_dec_ref(v___y_3911_);
return v_res_3916_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3917_; double v___x_3918_; 
v___x_3917_ = lean_unsigned_to_nat(0u);
v___x_3918_ = lean_float_of_nat(v___x_3917_);
return v___x_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(lean_object* v_cls_3922_, lean_object* v_msg_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
lean_object* v_ref_3929_; lean_object* v___x_3930_; lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3975_; 
v_ref_3929_ = lean_ctor_get(v___y_3926_, 5);
v___x_3930_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(v_msg_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_);
v_a_3931_ = lean_ctor_get(v___x_3930_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3933_ = v___x_3930_;
v_isShared_3934_ = v_isSharedCheck_3975_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3930_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3975_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3935_; lean_object* v_traceState_3936_; lean_object* v_env_3937_; lean_object* v_nextMacroScope_3938_; lean_object* v_ngen_3939_; lean_object* v_auxDeclNGen_3940_; lean_object* v_cache_3941_; lean_object* v_messages_3942_; lean_object* v_infoState_3943_; lean_object* v_snapshotTasks_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3974_; 
v___x_3935_ = lean_st_ref_take(v___y_3927_);
v_traceState_3936_ = lean_ctor_get(v___x_3935_, 4);
v_env_3937_ = lean_ctor_get(v___x_3935_, 0);
v_nextMacroScope_3938_ = lean_ctor_get(v___x_3935_, 1);
v_ngen_3939_ = lean_ctor_get(v___x_3935_, 2);
v_auxDeclNGen_3940_ = lean_ctor_get(v___x_3935_, 3);
v_cache_3941_ = lean_ctor_get(v___x_3935_, 5);
v_messages_3942_ = lean_ctor_get(v___x_3935_, 6);
v_infoState_3943_ = lean_ctor_get(v___x_3935_, 7);
v_snapshotTasks_3944_ = lean_ctor_get(v___x_3935_, 8);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3946_ = v___x_3935_;
v_isShared_3947_ = v_isSharedCheck_3974_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_snapshotTasks_3944_);
lean_inc(v_infoState_3943_);
lean_inc(v_messages_3942_);
lean_inc(v_cache_3941_);
lean_inc(v_traceState_3936_);
lean_inc(v_auxDeclNGen_3940_);
lean_inc(v_ngen_3939_);
lean_inc(v_nextMacroScope_3938_);
lean_inc(v_env_3937_);
lean_dec(v___x_3935_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3974_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
uint64_t v_tid_3948_; lean_object* v_traces_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3973_; 
v_tid_3948_ = lean_ctor_get_uint64(v_traceState_3936_, sizeof(void*)*1);
v_traces_3949_ = lean_ctor_get(v_traceState_3936_, 0);
v_isSharedCheck_3973_ = !lean_is_exclusive(v_traceState_3936_);
if (v_isSharedCheck_3973_ == 0)
{
v___x_3951_ = v_traceState_3936_;
v_isShared_3952_ = v_isSharedCheck_3973_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_traces_3949_);
lean_dec(v_traceState_3936_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3973_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3953_; double v___x_3954_; uint8_t v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3963_; 
v___x_3953_ = lean_box(0);
v___x_3954_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0);
v___x_3955_ = 0;
v___x_3956_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__1));
v___x_3957_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3957_, 0, v_cls_3922_);
lean_ctor_set(v___x_3957_, 1, v___x_3953_);
lean_ctor_set(v___x_3957_, 2, v___x_3956_);
lean_ctor_set_float(v___x_3957_, sizeof(void*)*3, v___x_3954_);
lean_ctor_set_float(v___x_3957_, sizeof(void*)*3 + 8, v___x_3954_);
lean_ctor_set_uint8(v___x_3957_, sizeof(void*)*3 + 16, v___x_3955_);
v___x_3958_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__2));
v___x_3959_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3957_);
lean_ctor_set(v___x_3959_, 1, v_a_3931_);
lean_ctor_set(v___x_3959_, 2, v___x_3958_);
lean_inc(v_ref_3929_);
v___x_3960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3960_, 0, v_ref_3929_);
lean_ctor_set(v___x_3960_, 1, v___x_3959_);
v___x_3961_ = l_Lean_PersistentArray_push___redArg(v_traces_3949_, v___x_3960_);
if (v_isShared_3952_ == 0)
{
lean_ctor_set(v___x_3951_, 0, v___x_3961_);
v___x_3963_ = v___x_3951_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v___x_3961_);
lean_ctor_set_uint64(v_reuseFailAlloc_3972_, sizeof(void*)*1, v_tid_3948_);
v___x_3963_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
lean_object* v___x_3965_; 
if (v_isShared_3947_ == 0)
{
lean_ctor_set(v___x_3946_, 4, v___x_3963_);
v___x_3965_ = v___x_3946_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_env_3937_);
lean_ctor_set(v_reuseFailAlloc_3971_, 1, v_nextMacroScope_3938_);
lean_ctor_set(v_reuseFailAlloc_3971_, 2, v_ngen_3939_);
lean_ctor_set(v_reuseFailAlloc_3971_, 3, v_auxDeclNGen_3940_);
lean_ctor_set(v_reuseFailAlloc_3971_, 4, v___x_3963_);
lean_ctor_set(v_reuseFailAlloc_3971_, 5, v_cache_3941_);
lean_ctor_set(v_reuseFailAlloc_3971_, 6, v_messages_3942_);
lean_ctor_set(v_reuseFailAlloc_3971_, 7, v_infoState_3943_);
lean_ctor_set(v_reuseFailAlloc_3971_, 8, v_snapshotTasks_3944_);
v___x_3965_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3969_; 
v___x_3966_ = lean_st_ref_put(v___y_3927_, v___x_3965_);
v___x_3967_ = lean_box(0);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 0, v___x_3967_);
v___x_3969_ = v___x_3933_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3967_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___boxed(lean_object* v_cls_3976_, lean_object* v_msg_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v_cls_3976_, v_msg_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
return v_res_3983_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5(void){
_start:
{
lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3994_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2));
v___x_3995_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4));
v___x_3996_ = l_Lean_Name_append(v___x_3995_, v___x_3994_);
return v___x_3996_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7(void){
_start:
{
lean_object* v___x_3998_; lean_object* v___x_3999_; 
v___x_3998_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__6));
v___x_3999_ = l_Lean_stringToMessageData(v___x_3998_);
return v___x_3999_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9(void){
_start:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4001_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__8));
v___x_4002_ = l_Lean_stringToMessageData(v___x_4001_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(lean_object* v_e_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_){
_start:
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
lean_inc_ref(v_e_4003_);
v___x_4014_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___boxed), 6, 1);
lean_closure_set(v___x_4014_, 0, v_e_4003_);
v___x_4015_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_4014_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4073_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4018_ = v___x_4015_;
v_isShared_4019_ = v_isSharedCheck_4073_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_4015_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4073_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
if (lean_obj_tag(v_a_4016_) == 1)
{
lean_object* v_val_4020_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v_options_4047_; uint8_t v_hasTrace_4048_; 
lean_del_object(v___x_4018_);
v_val_4020_ = lean_ctor_get(v_a_4016_, 0);
lean_inc(v_val_4020_);
lean_dec_ref_known(v_a_4016_, 1);
v_options_4047_ = lean_ctor_get(v_a_4011_, 2);
v_hasTrace_4048_ = lean_ctor_get_uint8(v_options_4047_, sizeof(void*)*1);
if (v_hasTrace_4048_ == 0)
{
lean_dec_ref(v_e_4003_);
v___y_4022_ = v_a_4007_;
v___y_4023_ = v_a_4008_;
v___y_4024_ = v_a_4009_;
v___y_4025_ = v_a_4010_;
v___y_4026_ = v_a_4011_;
v___y_4027_ = v_a_4012_;
goto v___jp_4021_;
}
else
{
lean_object* v_inheritedTraceOptions_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; uint8_t v___x_4052_; 
v_inheritedTraceOptions_4049_ = lean_ctor_get(v_a_4011_, 13);
v___x_4050_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2));
v___x_4051_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5);
v___x_4052_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4049_, v_options_4047_, v___x_4051_);
if (v___x_4052_ == 0)
{
lean_dec_ref(v_e_4003_);
v___y_4022_ = v_a_4007_;
v___y_4023_ = v_a_4008_;
v___y_4024_ = v_a_4009_;
v___y_4025_ = v_a_4010_;
v___y_4026_ = v_a_4011_;
v___y_4027_ = v_a_4012_;
goto v___jp_4021_;
}
else
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4053_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7);
v___x_4054_ = l_Lean_indentExpr(v_e_4003_);
v___x_4055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4053_);
lean_ctor_set(v___x_4055_, 1, v___x_4054_);
v___x_4056_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9);
v___x_4057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4055_);
lean_ctor_set(v___x_4057_, 1, v___x_4056_);
lean_inc(v_val_4020_);
v___x_4058_ = l_Lean_indentExpr(v_val_4020_);
v___x_4059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4057_);
lean_ctor_set(v___x_4059_, 1, v___x_4058_);
v___x_4060_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v___x_4050_, v___x_4059_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_dec_ref_known(v___x_4060_, 1);
v___y_4022_ = v_a_4007_;
v___y_4023_ = v_a_4008_;
v___y_4024_ = v_a_4009_;
v___y_4025_ = v_a_4010_;
v___y_4026_ = v_a_4011_;
v___y_4027_ = v_a_4012_;
goto v___jp_4021_;
}
else
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
lean_dec(v_val_4020_);
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_4060_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4060_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
}
v___jp_4021_:
{
lean_object* v___x_4028_; 
lean_inc(v_val_4020_);
v___x_4028_ = l_Lean_Meta_Sym_mkEqRefl(v_val_4020_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4038_; 
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4031_ = v___x_4028_;
v_isShared_4032_ = v_isSharedCheck_4038_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4028_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4038_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
uint8_t v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4036_; 
v___x_4033_ = 0;
v___x_4034_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_4034_, 0, v_val_4020_);
lean_ctor_set(v___x_4034_, 1, v_a_4029_);
lean_ctor_set_uint8(v___x_4034_, sizeof(void*)*2, v___x_4033_);
lean_ctor_set_uint8(v___x_4034_, sizeof(void*)*2 + 1, v___x_4033_);
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 0, v___x_4034_);
v___x_4036_ = v___x_4031_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v___x_4034_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
else
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
lean_dec(v_val_4020_);
v_a_4039_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4041_ = v___x_4028_;
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v___x_4028_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4044_; 
if (v_isShared_4042_ == 0)
{
v___x_4044_ = v___x_4041_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_a_4039_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
}
}
else
{
lean_object* v___x_4069_; lean_object* v___x_4071_; 
lean_dec(v_a_4016_);
lean_dec_ref(v_e_4003_);
v___x_4069_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___closed__0));
if (v_isShared_4019_ == 0)
{
lean_ctor_set(v___x_4018_, 0, v___x_4069_);
v___x_4071_ = v___x_4018_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v___x_4069_);
v___x_4071_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
return v___x_4071_;
}
}
}
}
else
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4081_; 
lean_dec_ref(v_e_4003_);
v_a_4074_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4076_ = v___x_4015_;
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4015_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4079_; 
if (v_isShared_4077_ == 0)
{
v___x_4079_ = v___x_4076_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4074_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___boxed(lean_object* v_e_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_);
lean_dec(v_a_4091_);
lean_dec_ref(v_a_4090_);
lean_dec(v_a_4089_);
lean_dec_ref(v_a_4088_);
lean_dec(v_a_4087_);
lean_dec_ref(v_a_4086_);
lean_dec(v_a_4085_);
lean_dec_ref(v_a_4084_);
lean_dec(v_a_4083_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0(lean_object* v_cls_4094_, lean_object* v_msg_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
lean_object* v___x_4106_; 
v___x_4106_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v_cls_4094_, v_msg_4095_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
return v___x_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___boxed(lean_object* v_cls_4107_, lean_object* v_msg_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0(v_cls_4107_, v_msg_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec(v___y_4115_);
lean_dec_ref(v___y_4114_);
lean_dec(v___y_4113_);
lean_dec_ref(v___y_4112_);
lean_dec(v___y_4111_);
lean_dec_ref(v___y_4110_);
lean_dec(v___y_4109_);
return v_res_4119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec(lean_object* v_x_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_){
_start:
{
uint8_t v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; 
v___x_4143_ = 0;
v___x_4144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__0));
lean_inc_ref(v_x_4132_);
v___x_4145_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_x_4132_, v___x_4144_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v_a_4146_; 
v_a_4146_ = lean_ctor_get(v___x_4145_, 0);
lean_inc(v_a_4146_);
if (lean_obj_tag(v_a_4146_) == 0)
{
uint8_t v_done_4147_; 
v_done_4147_ = lean_ctor_get_uint8(v_a_4146_, 0);
if (v_done_4147_ == 0)
{
lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4160_; 
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4160_ == 0)
{
lean_object* v_unused_4161_; 
v_unused_4161_ = lean_ctor_get(v___x_4145_, 0);
lean_dec(v_unused_4161_);
v___x_4149_ = v___x_4145_;
v_isShared_4150_ = v_isSharedCheck_4160_;
goto v_resetjp_4148_;
}
else
{
lean_dec(v___x_4145_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4160_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
uint8_t v_contextDependent_4151_; lean_object* v___x_4152_; 
v_contextDependent_4151_ = lean_ctor_get_uint8(v_a_4146_, 1);
lean_dec_ref_known(v_a_4146_, 0);
v___x_4152_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_x_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v_a_4153_; uint8_t v___y_4155_; 
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_a_4153_);
if (v_contextDependent_4151_ == 0)
{
lean_dec(v_a_4153_);
lean_del_object(v___x_4149_);
return v___x_4152_;
}
else
{
lean_dec_ref_known(v___x_4152_, 1);
v___y_4155_ = v___x_4143_;
goto v___jp_4154_;
}
v___jp_4154_:
{
lean_object* v___x_4156_; lean_object* v___x_4158_; 
v___x_4156_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_4153_);
if (v_isShared_4150_ == 0)
{
lean_ctor_set(v___x_4149_, 0, v___x_4156_);
v___x_4158_ = v___x_4149_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v___x_4156_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
else
{
lean_del_object(v___x_4149_);
return v___x_4152_;
}
}
}
else
{
lean_dec_ref_known(v_a_4146_, 0);
lean_dec_ref(v_x_4132_);
return v___x_4145_;
}
}
else
{
uint8_t v_done_4162_; 
v_done_4162_ = lean_ctor_get_uint8(v_a_4146_, sizeof(void*)*2);
if (v_done_4162_ == 0)
{
lean_object* v_e_x27_4163_; lean_object* v_proof_4164_; uint8_t v_contextDependent_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4211_; 
lean_dec_ref_known(v___x_4145_, 1);
v_e_x27_4163_ = lean_ctor_get(v_a_4146_, 0);
v_proof_4164_ = lean_ctor_get(v_a_4146_, 1);
v_contextDependent_4165_ = lean_ctor_get_uint8(v_a_4146_, sizeof(void*)*2 + 1);
v_isSharedCheck_4211_ = !lean_is_exclusive(v_a_4146_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4167_ = v_a_4146_;
v_isShared_4168_ = v_isSharedCheck_4211_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_proof_4164_);
lean_inc(v_e_x27_4163_);
lean_dec(v_a_4146_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4211_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4169_; 
lean_inc_ref(v_e_x27_4163_);
v___x_4169_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_x27_4163_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_);
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4210_; 
v_a_4170_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4210_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4210_ == 0)
{
v___x_4172_ = v___x_4169_;
v_isShared_4173_ = v_isSharedCheck_4210_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___x_4169_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4210_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
if (lean_obj_tag(v_a_4170_) == 0)
{
uint8_t v___y_4175_; 
lean_dec_ref_known(v_a_4170_, 0);
lean_dec_ref(v_x_4132_);
if (v_contextDependent_4165_ == 0)
{
v___y_4175_ = v___x_4143_;
goto v___jp_4174_;
}
else
{
v___y_4175_ = v_contextDependent_4165_;
goto v___jp_4174_;
}
v___jp_4174_:
{
lean_object* v___x_4177_; 
if (v_isShared_4168_ == 0)
{
v___x_4177_ = v___x_4167_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_e_x27_4163_);
lean_ctor_set(v_reuseFailAlloc_4181_, 1, v_proof_4164_);
v___x_4177_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
lean_object* v___x_4179_; 
lean_ctor_set_uint8(v___x_4177_, sizeof(void*)*2, v___x_4143_);
lean_ctor_set_uint8(v___x_4177_, sizeof(void*)*2 + 1, v___y_4175_);
if (v_isShared_4173_ == 0)
{
lean_ctor_set(v___x_4172_, 0, v___x_4177_);
v___x_4179_ = v___x_4172_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v___x_4177_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
}
else
{
lean_object* v_e_x27_4182_; lean_object* v_proof_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4209_; 
lean_del_object(v___x_4172_);
lean_del_object(v___x_4167_);
v_e_x27_4182_ = lean_ctor_get(v_a_4170_, 0);
v_proof_4183_ = lean_ctor_get(v_a_4170_, 1);
v_isSharedCheck_4209_ = !lean_is_exclusive(v_a_4170_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4185_ = v_a_4170_;
v_isShared_4186_ = v_isSharedCheck_4209_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_proof_4183_);
lean_inc(v_e_x27_4182_);
lean_dec(v_a_4170_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4209_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4187_; 
lean_inc_ref(v_e_x27_4182_);
v___x_4187_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_x_4132_, v_e_x27_4163_, v_proof_4164_, v_e_x27_4182_, v_proof_4183_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_, v_a_4141_);
if (lean_obj_tag(v___x_4187_) == 0)
{
lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4200_; 
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4190_ = v___x_4187_;
v_isShared_4191_ = v_isSharedCheck_4200_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_dec(v___x_4187_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4200_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
uint8_t v___y_4193_; 
if (v_contextDependent_4165_ == 0)
{
v___y_4193_ = v___x_4143_;
goto v___jp_4192_;
}
else
{
v___y_4193_ = v_contextDependent_4165_;
goto v___jp_4192_;
}
v___jp_4192_:
{
lean_object* v___x_4195_; 
if (v_isShared_4186_ == 0)
{
lean_ctor_set(v___x_4185_, 1, v_a_4188_);
v___x_4195_ = v___x_4185_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_e_x27_4182_);
lean_ctor_set(v_reuseFailAlloc_4199_, 1, v_a_4188_);
v___x_4195_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
lean_object* v___x_4197_; 
lean_ctor_set_uint8(v___x_4195_, sizeof(void*)*2, v___x_4143_);
lean_ctor_set_uint8(v___x_4195_, sizeof(void*)*2 + 1, v___y_4193_);
if (v_isShared_4191_ == 0)
{
lean_ctor_set(v___x_4190_, 0, v___x_4195_);
v___x_4197_ = v___x_4190_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v___x_4195_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
}
}
else
{
lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4208_; 
lean_del_object(v___x_4185_);
lean_dec_ref(v_e_x27_4182_);
v_a_4201_ = lean_ctor_get(v___x_4187_, 0);
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4187_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4203_ = v___x_4187_;
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_a_4201_);
lean_dec(v___x_4187_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4206_; 
if (v_isShared_4204_ == 0)
{
v___x_4206_ = v___x_4203_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_a_4201_);
v___x_4206_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
return v___x_4206_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_4167_);
lean_dec_ref(v_proof_4164_);
lean_dec_ref(v_e_x27_4163_);
lean_dec_ref(v_x_4132_);
return v___x_4169_;
}
}
}
else
{
lean_dec_ref_known(v_a_4146_, 2);
lean_dec_ref(v_x_4132_);
return v___x_4145_;
}
}
}
else
{
lean_dec_ref(v_x_4132_);
return v___x_4145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed(lean_object* v_x_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec(v_x_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_);
lean_dec(v_a_4221_);
lean_dec_ref(v_a_4220_);
lean_dec(v_a_4219_);
lean_dec_ref(v_a_4218_);
lean_dec(v_a_4217_);
lean_dec_ref(v_a_4216_);
lean_dec(v_a_4215_);
lean_dec_ref(v_a_4214_);
lean_dec(v_a_4213_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_));
v___x_4246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_));
v___x_4247_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed), 11, 0);
v___x_4248_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_4245_, v___x_4246_, v___x_4247_);
return v___x_4248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17____boxed(lean_object* v_a_4249_){
_start:
{
lean_object* v_res_4250_; 
v_res_4250_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_();
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_4252_; uint8_t v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
v___x_4252_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_));
v___x_4253_ = 0;
v___x_4254_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed), 11, 0);
v___x_4255_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_4252_, v___x_4253_, v___x_4254_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_19____boxed(lean_object* v_a_4256_){
_start:
{
lean_object* v_res_4257_; 
v_res_4257_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_19_();
return v_res_4257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(lean_object* v_appFn_4259_, lean_object* v_e_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_){
_start:
{
lean_object* v___x_4271_; 
v___x_4271_ = l_Lean_Meta_Tactic_Cbv_getMatchTheorems(v_appFn_4259_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_);
if (lean_obj_tag(v___x_4271_) == 0)
{
lean_object* v_a_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v_a_4272_ = lean_ctor_get(v___x_4271_, 0);
lean_inc(v_a_4272_);
lean_dec_ref_known(v___x_4271_, 1);
v___x_4273_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0));
v___x_4274_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_4272_, v___x_4273_, v_e_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_, v_a_4267_, v_a_4268_, v_a_4269_);
lean_dec(v_a_4272_);
return v___x_4274_;
}
else
{
lean_object* v_a_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4282_; 
lean_dec_ref(v_e_4260_);
v_a_4275_ = lean_ctor_get(v___x_4271_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4271_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4277_ = v___x_4271_;
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_a_4275_);
lean_dec(v___x_4271_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4280_; 
if (v_isShared_4278_ == 0)
{
v___x_4280_ = v___x_4277_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4275_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___boxed(lean_object* v_appFn_4283_, lean_object* v_e_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_){
_start:
{
lean_object* v_res_4295_; 
v_res_4295_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_appFn_4283_, v_e_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_);
lean_dec(v_a_4293_);
lean_dec_ref(v_a_4292_);
lean_dec(v_a_4291_);
lean_dec_ref(v_a_4290_);
lean_dec(v_a_4289_);
lean_dec_ref(v_a_4288_);
lean_dec(v_a_4287_);
lean_dec_ref(v_a_4286_);
lean_dec(v_a_4285_);
return v_res_4295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(lean_object* v_declName_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v___x_4299_; lean_object* v_env_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4299_ = lean_st_ref_get(v___y_4297_);
v_env_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc_ref(v_env_4300_);
lean_dec(v___x_4299_);
v___x_4301_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_4300_, v_declName_4296_);
v___x_4302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4301_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg___boxed(lean_object* v_declName_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(v_declName_4303_, v___y_4304_);
lean_dec(v___y_4304_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(lean_object* v_declName_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v___x_4318_; 
v___x_4318_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(v_declName_4307_, v___y_4316_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___boxed(lean_object* v_declName_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(v_declName_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
lean_dec(v___y_4322_);
lean_dec_ref(v___y_4321_);
lean_dec(v___y_4320_);
return v_res_4330_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2(void){
_start:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4337_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1));
v___x_4338_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4));
v___x_4339_ = l_Lean_Name_append(v___x_4338_, v___x_4337_);
return v___x_4339_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4(void){
_start:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; 
v___x_4341_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__3));
v___x_4342_ = l_Lean_stringToMessageData(v___x_4341_);
return v___x_4342_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6(void){
_start:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___x_4344_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__5));
v___x_4345_ = l_Lean_stringToMessageData(v___x_4344_);
return v___x_4345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher(lean_object* v_e_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_){
_start:
{
uint8_t v___x_4357_; 
v___x_4357_ = l_Lean_Expr_isApp(v_e_4346_);
if (v___x_4357_ == 0)
{
lean_object* v___x_4358_; lean_object* v___x_4359_; 
lean_dec_ref(v_e_4346_);
v___x_4358_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_4358_, 0, v___x_4357_);
lean_ctor_set_uint8(v___x_4358_, 1, v___x_4357_);
v___x_4359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4359_, 0, v___x_4358_);
return v___x_4359_;
}
else
{
lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4360_ = l_Lean_Expr_getAppFn(v_e_4346_);
v___x_4361_ = l_Lean_Expr_constName_x3f(v___x_4360_);
lean_dec_ref(v___x_4360_);
if (lean_obj_tag(v___x_4361_) == 1)
{
lean_object* v_val_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4509_; 
v_val_4362_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4364_ = v___x_4361_;
v_isShared_4365_ = v_isSharedCheck_4509_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_val_4362_);
lean_dec(v___x_4361_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4509_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v_a_4367_; lean_object* v_e_x27_4368_; lean_object* v___y_4410_; lean_object* v_a_4411_; lean_object* v___y_4414_; lean_object* v___y_4417_; lean_object* v___y_4418_; uint8_t v___y_4419_; lean_object* v___y_4423_; lean_object* v_a_4424_; lean_object* v___y_4432_; lean_object* v___x_4434_; lean_object* v_a_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4508_; 
lean_inc(v_val_4362_);
v___x_4434_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(v_val_4362_, v_a_4355_);
v_a_4435_ = lean_ctor_get(v___x_4434_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4434_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4437_ = v___x_4434_;
v_isShared_4438_ = v_isSharedCheck_4508_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_a_4435_);
lean_dec(v___x_4434_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4508_;
goto v_resetjp_4436_;
}
v___jp_4366_:
{
lean_object* v_options_4369_; uint8_t v_hasTrace_4370_; 
v_options_4369_ = lean_ctor_get(v_a_4354_, 2);
v_hasTrace_4370_ = lean_ctor_get_uint8(v_options_4369_, sizeof(void*)*1);
if (v_hasTrace_4370_ == 0)
{
lean_object* v___x_4372_; 
lean_dec_ref(v_e_x27_4368_);
lean_dec(v_val_4362_);
lean_dec_ref(v_e_4346_);
if (v_isShared_4365_ == 0)
{
lean_ctor_set_tag(v___x_4364_, 0);
lean_ctor_set(v___x_4364_, 0, v_a_4367_);
v___x_4372_ = v___x_4364_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v_a_4367_);
v___x_4372_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
return v___x_4372_;
}
}
else
{
lean_object* v_inheritedTraceOptions_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; uint8_t v___x_4377_; 
v_inheritedTraceOptions_4374_ = lean_ctor_get(v_a_4354_, 13);
v___x_4375_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1));
v___x_4376_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2, &l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2);
v___x_4377_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4374_, v_options_4369_, v___x_4376_);
if (v___x_4377_ == 0)
{
lean_object* v___x_4379_; 
lean_dec_ref(v_e_x27_4368_);
lean_dec(v_val_4362_);
lean_dec_ref(v_e_4346_);
if (v_isShared_4365_ == 0)
{
lean_ctor_set_tag(v___x_4364_, 0);
lean_ctor_set(v___x_4364_, 0, v_a_4367_);
v___x_4379_ = v___x_4364_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_a_4367_);
v___x_4379_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
return v___x_4379_;
}
}
else
{
lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
lean_del_object(v___x_4364_);
v___x_4381_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4, &l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4);
v___x_4382_ = l_Lean_MessageData_ofName(v_val_4362_);
v___x_4383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4383_, 0, v___x_4381_);
lean_ctor_set(v___x_4383_, 1, v___x_4382_);
v___x_4384_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6, &l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6);
v___x_4385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4383_);
lean_ctor_set(v___x_4385_, 1, v___x_4384_);
v___x_4386_ = l_Lean_indentExpr(v_e_4346_);
v___x_4387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4387_, 0, v___x_4385_);
lean_ctor_set(v___x_4387_, 1, v___x_4386_);
v___x_4388_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9);
v___x_4389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4387_);
lean_ctor_set(v___x_4389_, 1, v___x_4388_);
v___x_4390_ = l_Lean_indentExpr(v_e_x27_4368_);
v___x_4391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4389_);
lean_ctor_set(v___x_4391_, 1, v___x_4390_);
v___x_4392_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v___x_4375_, v___x_4391_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_);
if (lean_obj_tag(v___x_4392_) == 0)
{
lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4399_; 
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4399_ == 0)
{
lean_object* v_unused_4400_; 
v_unused_4400_ = lean_ctor_get(v___x_4392_, 0);
lean_dec(v_unused_4400_);
v___x_4394_ = v___x_4392_;
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
else
{
lean_dec(v___x_4392_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4397_; 
if (v_isShared_4395_ == 0)
{
lean_ctor_set(v___x_4394_, 0, v_a_4367_);
v___x_4397_ = v___x_4394_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_a_4367_);
v___x_4397_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
return v___x_4397_;
}
}
}
else
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4408_; 
lean_dec_ref(v_a_4367_);
v_a_4401_ = lean_ctor_get(v___x_4392_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4403_ = v___x_4392_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4392_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4406_; 
if (v_isShared_4404_ == 0)
{
v___x_4406_ = v___x_4403_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_a_4401_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
}
}
}
}
}
}
v___jp_4409_:
{
if (lean_obj_tag(v_a_4411_) == 1)
{
lean_object* v_e_x27_4412_; 
lean_dec_ref(v___y_4410_);
v_e_x27_4412_ = lean_ctor_get(v_a_4411_, 0);
lean_inc_ref(v_e_x27_4412_);
v_a_4367_ = v_a_4411_;
v_e_x27_4368_ = v_e_x27_4412_;
goto v___jp_4366_;
}
else
{
lean_dec_ref(v_a_4411_);
lean_del_object(v___x_4364_);
lean_dec(v_val_4362_);
lean_dec_ref(v_e_4346_);
return v___y_4410_;
}
}
v___jp_4413_:
{
if (lean_obj_tag(v___y_4414_) == 0)
{
lean_object* v_a_4415_; 
v_a_4415_ = lean_ctor_get(v___y_4414_, 0);
lean_inc(v_a_4415_);
v___y_4410_ = v___y_4414_;
v_a_4411_ = v_a_4415_;
goto v___jp_4409_;
}
else
{
lean_del_object(v___x_4364_);
lean_dec(v_val_4362_);
lean_dec_ref(v_e_4346_);
return v___y_4414_;
}
}
v___jp_4416_:
{
lean_object* v___x_4420_; lean_object* v___x_4421_; 
lean_dec_ref(v___y_4418_);
v___x_4420_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_4417_);
lean_inc_ref(v___x_4420_);
v___x_4421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4420_);
v___y_4410_ = v___x_4421_;
v_a_4411_ = v___x_4420_;
goto v___jp_4409_;
}
v___jp_4422_:
{
if (lean_obj_tag(v_a_4424_) == 0)
{
uint8_t v_done_4425_; 
v_done_4425_ = lean_ctor_get_uint8(v_a_4424_, 0);
if (v_done_4425_ == 0)
{
uint8_t v_contextDependent_4426_; lean_object* v___x_4427_; 
lean_dec_ref(v___y_4423_);
v_contextDependent_4426_ = lean_ctor_get_uint8(v_a_4424_, 1);
lean_dec_ref_known(v_a_4424_, 0);
lean_inc_ref(v_e_4346_);
v___x_4427_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_);
if (lean_obj_tag(v___x_4427_) == 0)
{
if (v_contextDependent_4426_ == 0)
{
v___y_4414_ = v___x_4427_;
goto v___jp_4413_;
}
else
{
lean_object* v_a_4428_; uint8_t v___x_4429_; 
v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4428_);
v___x_4429_ = 0;
v___y_4417_ = v_a_4428_;
v___y_4418_ = v___x_4427_;
v___y_4419_ = v___x_4429_;
goto v___jp_4416_;
}
}
else
{
v___y_4414_ = v___x_4427_;
goto v___jp_4413_;
}
}
else
{
lean_dec_ref_known(v_a_4424_, 0);
lean_del_object(v___x_4364_);
lean_dec(v_val_4362_);
lean_dec_ref(v_e_4346_);
return v___y_4423_;
}
}
else
{
lean_object* v_e_x27_4430_; 
lean_dec_ref(v___y_4423_);
v_e_x27_4430_ = lean_ctor_get(v_a_4424_, 0);
lean_inc_ref(v_e_x27_4430_);
v_a_4367_ = v_a_4424_;
v_e_x27_4368_ = v_e_x27_4430_;
goto v___jp_4366_;
}
}
v___jp_4431_:
{
if (lean_obj_tag(v___y_4432_) == 0)
{
lean_object* v_a_4433_; 
v_a_4433_ = lean_ctor_get(v___y_4432_, 0);
lean_inc(v_a_4433_);
v___y_4423_ = v___y_4432_;
v_a_4424_ = v_a_4433_;
goto v___jp_4422_;
}
else
{
lean_del_object(v___x_4364_);
lean_dec(v_val_4362_);
lean_dec_ref(v_e_4346_);
return v___y_4432_;
}
}
v_resetjp_4436_:
{
if (lean_obj_tag(v_a_4435_) == 1)
{
lean_object* v_val_4439_; lean_object* v_numParams_4440_; lean_object* v_numDiscrs_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
lean_del_object(v___x_4437_);
v_val_4439_ = lean_ctor_get(v_a_4435_, 0);
lean_inc(v_val_4439_);
lean_dec_ref_known(v_a_4435_, 1);
v_numParams_4440_ = lean_ctor_get(v_val_4439_, 0);
lean_inc(v_numParams_4440_);
v_numDiscrs_4441_ = lean_ctor_get(v_val_4439_, 1);
lean_inc(v_numDiscrs_4441_);
lean_dec(v_val_4439_);
v___x_4442_ = lean_unsigned_to_nat(1u);
v___x_4443_ = lean_nat_add(v_numParams_4440_, v___x_4442_);
lean_dec(v_numParams_4440_);
v___x_4444_ = lean_nat_add(v___x_4443_, v_numDiscrs_4441_);
lean_dec(v_numDiscrs_4441_);
lean_inc_ref(v_e_4346_);
v___x_4445_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_e_4346_, v___x_4443_, v___x_4444_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_);
lean_dec(v___x_4444_);
lean_dec(v___x_4443_);
if (lean_obj_tag(v___x_4445_) == 0)
{
lean_object* v_a_4446_; 
v_a_4446_ = lean_ctor_get(v___x_4445_, 0);
lean_inc(v_a_4446_);
if (lean_obj_tag(v_a_4446_) == 0)
{
uint8_t v_done_4447_; 
v_done_4447_ = lean_ctor_get_uint8(v_a_4446_, 0);
if (v_done_4447_ == 0)
{
uint8_t v_contextDependent_4448_; lean_object* v___x_4449_; 
lean_dec_ref_known(v___x_4445_, 1);
v_contextDependent_4448_ = lean_ctor_get_uint8(v_a_4446_, 1);
lean_dec_ref_known(v_a_4446_, 0);
lean_inc_ref(v_e_4346_);
lean_inc(v_val_4362_);
v___x_4449_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_val_4362_, v_e_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_);
if (lean_obj_tag(v___x_4449_) == 0)
{
lean_object* v_a_4450_; uint8_t v___y_4452_; 
v_a_4450_ = lean_ctor_get(v___x_4449_, 0);
lean_inc(v_a_4450_);
if (v_contextDependent_4448_ == 0)
{
lean_dec(v_a_4450_);
v___y_4432_ = v___x_4449_;
goto v___jp_4431_;
}
else
{
if (lean_obj_tag(v_a_4450_) == 0)
{
uint8_t v_contextDependent_4462_; 
v_contextDependent_4462_ = lean_ctor_get_uint8(v_a_4450_, 1);
v___y_4452_ = v_contextDependent_4462_;
goto v___jp_4451_;
}
else
{
uint8_t v_contextDependent_4463_; 
v_contextDependent_4463_ = lean_ctor_get_uint8(v_a_4450_, sizeof(void*)*2 + 1);
v___y_4452_ = v_contextDependent_4463_;
goto v___jp_4451_;
}
}
v___jp_4451_:
{
if (v___y_4452_ == 0)
{
lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4460_; 
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4449_);
if (v_isSharedCheck_4460_ == 0)
{
lean_object* v_unused_4461_; 
v_unused_4461_ = lean_ctor_get(v___x_4449_, 0);
lean_dec(v_unused_4461_);
v___x_4454_ = v___x_4449_;
v_isShared_4455_ = v_isSharedCheck_4460_;
goto v_resetjp_4453_;
}
else
{
lean_dec(v___x_4449_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4460_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4456_; lean_object* v___x_4458_; 
v___x_4456_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_4450_);
lean_inc_ref(v___x_4456_);
if (v_isShared_4455_ == 0)
{
lean_ctor_set(v___x_4454_, 0, v___x_4456_);
v___x_4458_ = v___x_4454_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v___x_4456_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
v___y_4423_ = v___x_4458_;
v_a_4424_ = v___x_4456_;
goto v___jp_4422_;
}
}
}
else
{
lean_dec(v_a_4450_);
v___y_4432_ = v___x_4449_;
goto v___jp_4431_;
}
}
}
else
{
v___y_4432_ = v___x_4449_;
goto v___jp_4431_;
}
}
else
{
lean_dec_ref_known(v_a_4446_, 0);
v___y_4432_ = v___x_4445_;
goto v___jp_4431_;
}
}
else
{
uint8_t v_done_4464_; 
v_done_4464_ = lean_ctor_get_uint8(v_a_4446_, sizeof(void*)*2);
if (v_done_4464_ == 0)
{
lean_object* v_e_x27_4465_; lean_object* v_proof_4466_; uint8_t v_contextDependent_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4503_; 
lean_dec_ref_known(v___x_4445_, 1);
v_e_x27_4465_ = lean_ctor_get(v_a_4446_, 0);
v_proof_4466_ = lean_ctor_get(v_a_4446_, 1);
v_contextDependent_4467_ = lean_ctor_get_uint8(v_a_4446_, sizeof(void*)*2 + 1);
v_isSharedCheck_4503_ = !lean_is_exclusive(v_a_4446_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4469_ = v_a_4446_;
v_isShared_4470_ = v_isSharedCheck_4503_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_proof_4466_);
lean_inc(v_e_x27_4465_);
lean_dec(v_a_4446_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4503_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v___x_4471_; 
lean_inc_ref(v_e_x27_4465_);
lean_inc(v_val_4362_);
v___x_4471_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_val_4362_, v_e_x27_4465_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_object* v_a_4472_; 
v_a_4472_ = lean_ctor_get(v___x_4471_, 0);
lean_inc(v_a_4472_);
lean_dec_ref_known(v___x_4471_, 1);
if (lean_obj_tag(v_a_4472_) == 0)
{
uint8_t v_done_4473_; uint8_t v_contextDependent_4474_; uint8_t v___y_4476_; 
v_done_4473_ = lean_ctor_get_uint8(v_a_4472_, 0);
v_contextDependent_4474_ = lean_ctor_get_uint8(v_a_4472_, 1);
lean_dec_ref_known(v_a_4472_, 0);
if (v_contextDependent_4467_ == 0)
{
v___y_4476_ = v_contextDependent_4474_;
goto v___jp_4475_;
}
else
{
v___y_4476_ = v_contextDependent_4467_;
goto v___jp_4475_;
}
v___jp_4475_:
{
lean_object* v___x_4478_; 
lean_inc_ref(v_e_x27_4465_);
if (v_isShared_4470_ == 0)
{
v___x_4478_ = v___x_4469_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_e_x27_4465_);
lean_ctor_set(v_reuseFailAlloc_4479_, 1, v_proof_4466_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
lean_ctor_set_uint8(v___x_4478_, sizeof(void*)*2, v_done_4473_);
lean_ctor_set_uint8(v___x_4478_, sizeof(void*)*2 + 1, v___y_4476_);
v_a_4367_ = v___x_4478_;
v_e_x27_4368_ = v_e_x27_4465_;
goto v___jp_4366_;
}
}
}
else
{
lean_object* v_e_x27_4480_; lean_object* v_proof_4481_; uint8_t v_done_4482_; uint8_t v_contextDependent_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4502_; 
lean_del_object(v___x_4469_);
v_e_x27_4480_ = lean_ctor_get(v_a_4472_, 0);
v_proof_4481_ = lean_ctor_get(v_a_4472_, 1);
v_done_4482_ = lean_ctor_get_uint8(v_a_4472_, sizeof(void*)*2);
v_contextDependent_4483_ = lean_ctor_get_uint8(v_a_4472_, sizeof(void*)*2 + 1);
v_isSharedCheck_4502_ = !lean_is_exclusive(v_a_4472_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4485_ = v_a_4472_;
v_isShared_4486_ = v_isSharedCheck_4502_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_proof_4481_);
lean_inc(v_e_x27_4480_);
lean_dec(v_a_4472_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4502_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4487_; 
lean_inc_ref(v_e_x27_4480_);
lean_inc_ref(v_e_4346_);
v___x_4487_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_4346_, v_e_x27_4465_, v_proof_4466_, v_e_x27_4480_, v_proof_4481_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_);
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_object* v_a_4488_; uint8_t v___y_4490_; 
v_a_4488_ = lean_ctor_get(v___x_4487_, 0);
lean_inc(v_a_4488_);
lean_dec_ref_known(v___x_4487_, 1);
if (v_contextDependent_4467_ == 0)
{
v___y_4490_ = v_contextDependent_4483_;
goto v___jp_4489_;
}
else
{
v___y_4490_ = v_contextDependent_4467_;
goto v___jp_4489_;
}
v___jp_4489_:
{
lean_object* v___x_4492_; 
lean_inc_ref(v_e_x27_4480_);
if (v_isShared_4486_ == 0)
{
lean_ctor_set(v___x_4485_, 1, v_a_4488_);
v___x_4492_ = v___x_4485_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v_e_x27_4480_);
lean_ctor_set(v_reuseFailAlloc_4493_, 1, v_a_4488_);
lean_ctor_set_uint8(v_reuseFailAlloc_4493_, sizeof(void*)*2, v_done_4482_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
lean_ctor_set_uint8(v___x_4492_, sizeof(void*)*2 + 1, v___y_4490_);
v_a_4367_ = v___x_4492_;
v_e_x27_4368_ = v_e_x27_4480_;
goto v___jp_4366_;
}
}
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
lean_del_object(v___x_4485_);
lean_dec_ref(v_e_x27_4480_);
lean_del_object(v___x_4364_);
lean_dec(v_val_4362_);
lean_dec_ref(v_e_4346_);
v_a_4494_ = lean_ctor_get(v___x_4487_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4487_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4496_ = v___x_4487_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4487_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
if (v_isShared_4497_ == 0)
{
v___x_4499_ = v___x_4496_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4494_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_4469_);
lean_dec_ref(v_proof_4466_);
lean_dec_ref(v_e_x27_4465_);
v___y_4432_ = v___x_4471_;
goto v___jp_4431_;
}
}
}
else
{
lean_dec_ref_known(v_a_4446_, 2);
v___y_4432_ = v___x_4445_;
goto v___jp_4431_;
}
}
}
else
{
v___y_4432_ = v___x_4445_;
goto v___jp_4431_;
}
}
else
{
lean_object* v___x_4504_; lean_object* v___x_4506_; 
lean_dec(v_a_4435_);
lean_del_object(v___x_4364_);
lean_dec(v_val_4362_);
lean_dec_ref(v_e_4346_);
v___x_4504_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___closed__0));
if (v_isShared_4438_ == 0)
{
lean_ctor_set(v___x_4437_, 0, v___x_4504_);
v___x_4506_ = v___x_4437_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v___x_4504_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
}
}
else
{
lean_object* v___x_4510_; lean_object* v___x_4511_; 
lean_dec(v___x_4361_);
lean_dec_ref(v_e_4346_);
v___x_4510_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___closed__0));
v___x_4511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4511_, 0, v___x_4510_);
return v___x_4511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___boxed(lean_object* v_e_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_){
_start:
{
lean_object* v_res_4523_; 
v_res_4523_ = l_Lean_Meta_Tactic_Cbv_tryMatcher(v_e_4512_, v_a_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_);
lean_dec(v_a_4521_);
lean_dec_ref(v_a_4520_);
lean_dec(v_a_4519_);
lean_dec_ref(v_a_4518_);
lean_dec(v_a_4517_);
lean_dec_ref(v_a_4516_);
lean_dec(v_a_4515_);
lean_dec_ref(v_a_4514_);
lean_dec(v_a_4513_);
return v_res_4523_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Init_Sym_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_Opaque(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_NoncomputableAttr(uint8_t builtin);
lean_object* runtime_initialize_Init_CbvSimproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SynthInstance(builtin);
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
res = runtime_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_Opaque(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_NoncomputableAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_18_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_ControlFlow(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Init_Sym_Lemmas(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_Opaque(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(uint8_t builtin);
lean_object* initialize_Lean_Compiler_NoncomputableAttr(uint8_t builtin);
lean_object* initialize_Init_CbvSimproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Cbv_ControlFlow(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
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
res = initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_Opaque(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_NoncomputableAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Cbv_ControlFlow(builtin);
}
#ifdef __cplusplus
}
#endif

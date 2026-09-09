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
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_project_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_817_; lean_object* v___x_834_; uint8_t v_transparency_835_; uint8_t v___x_836_; 
v___x_834_ = l_Lean_Meta_Context_config(v___y_811_);
v_transparency_835_ = lean_ctor_get_uint8(v___x_834_, 9);
lean_dec_ref(v___x_834_);
v___x_836_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_835_, v___x_808_);
if (v___x_836_ == 0)
{
lean_object* v_keyedConfig_837_; uint8_t v_trackZetaDelta_838_; lean_object* v_zetaDeltaSet_839_; lean_object* v_lctx_840_; lean_object* v_localInstances_841_; lean_object* v_defEqCtx_x3f_842_; lean_object* v_synthPendingDepth_843_; lean_object* v_customCanUnfoldPredicate_x3f_844_; uint8_t v_univApprox_845_; uint8_t v_inTypeClassResolution_846_; uint8_t v_cacheInferType_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_856_; 
v_keyedConfig_837_ = lean_ctor_get(v___y_811_, 0);
v_trackZetaDelta_838_ = lean_ctor_get_uint8(v___y_811_, sizeof(void*)*7);
v_zetaDeltaSet_839_ = lean_ctor_get(v___y_811_, 1);
v_lctx_840_ = lean_ctor_get(v___y_811_, 2);
v_localInstances_841_ = lean_ctor_get(v___y_811_, 3);
v_defEqCtx_x3f_842_ = lean_ctor_get(v___y_811_, 4);
v_synthPendingDepth_843_ = lean_ctor_get(v___y_811_, 5);
v_customCanUnfoldPredicate_x3f_844_ = lean_ctor_get(v___y_811_, 6);
v_univApprox_845_ = lean_ctor_get_uint8(v___y_811_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_846_ = lean_ctor_get_uint8(v___y_811_, sizeof(void*)*7 + 2);
v_cacheInferType_847_ = lean_ctor_get_uint8(v___y_811_, sizeof(void*)*7 + 3);
v_isSharedCheck_856_ = !lean_is_exclusive(v___y_811_);
if (v_isSharedCheck_856_ == 0)
{
v___x_849_ = v___y_811_;
v_isShared_850_ = v_isSharedCheck_856_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_844_);
lean_inc(v_synthPendingDepth_843_);
lean_inc(v_defEqCtx_x3f_842_);
lean_inc(v_localInstances_841_);
lean_inc(v_lctx_840_);
lean_inc(v_zetaDeltaSet_839_);
lean_inc(v_keyedConfig_837_);
lean_dec(v___y_811_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_856_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_851_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_808_, v_keyedConfig_837_);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_851_);
v___x_853_ = v___x_849_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_851_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_zetaDeltaSet_839_);
lean_ctor_set(v_reuseFailAlloc_855_, 2, v_lctx_840_);
lean_ctor_set(v_reuseFailAlloc_855_, 3, v_localInstances_841_);
lean_ctor_set(v_reuseFailAlloc_855_, 4, v_defEqCtx_x3f_842_);
lean_ctor_set(v_reuseFailAlloc_855_, 5, v_synthPendingDepth_843_);
lean_ctor_set(v_reuseFailAlloc_855_, 6, v_customCanUnfoldPredicate_x3f_844_);
lean_ctor_set_uint8(v_reuseFailAlloc_855_, sizeof(void*)*7, v_trackZetaDelta_838_);
lean_ctor_set_uint8(v_reuseFailAlloc_855_, sizeof(void*)*7 + 1, v_univApprox_845_);
lean_ctor_set_uint8(v_reuseFailAlloc_855_, sizeof(void*)*7 + 2, v_inTypeClassResolution_846_);
lean_ctor_set_uint8(v_reuseFailAlloc_855_, sizeof(void*)*7 + 3, v_cacheInferType_847_);
v___x_853_ = v_reuseFailAlloc_855_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Meta_project_x3f(v_inst_809_, v___x_810_, v___x_853_, v___y_812_, v___y_813_, v___y_814_);
lean_dec_ref(v___x_853_);
v___y_817_ = v___x_854_;
goto v___jp_816_;
}
}
}
else
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Meta_project_x3f(v_inst_809_, v___x_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
lean_dec_ref(v___y_811_);
v___y_817_ = v___x_857_;
goto v___jp_816_;
}
v___jp_816_:
{
if (lean_obj_tag(v___y_817_) == 0)
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
v_a_818_ = lean_ctor_get(v___y_817_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___y_817_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___y_817_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___y_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
v_a_826_ = lean_ctor_get(v___y_817_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___y_817_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___y_817_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___y_817_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0___boxed(lean_object* v___x_858_, lean_object* v_inst_859_, lean_object* v___x_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
uint8_t v___x_15491__boxed_866_; lean_object* v_res_867_; 
v___x_15491__boxed_866_ = lean_unbox(v___x_858_);
v_res_867_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0(v___x_15491__boxed_866_, v_inst_859_, v___x_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec(v___x_860_);
return v_res_867_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_872_ = lean_box(0);
v___x_873_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__1));
v___x_874_ = l_Lean_mkConst(v___x_873_, v___x_872_);
return v___x_874_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__6(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_unsigned_to_nat(1u);
v___x_881_ = l_Lean_Level_ofNat(v___x_880_);
return v___x_881_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__7(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_882_ = lean_box(0);
v___x_883_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__6, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__6_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__6);
v___x_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v___x_882_);
return v___x_884_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_885_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__7, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__7);
v___x_886_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__5));
v___x_887_ = l_Lean_Expr_const___override(v___x_886_, v___x_885_);
return v___x_887_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_890_ = lean_box(0);
v___x_891_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__9));
v___x_892_ = l_Lean_mkConst(v___x_891_, v___x_890_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(lean_object* v_f_903_, lean_object* v_00_u03b1_904_, lean_object* v_c_905_, lean_object* v_inst_906_, lean_object* v_a_907_, lean_object* v_b_908_, lean_object* v_fallback_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v___x_920_; uint8_t v___x_921_; lean_object* v___x_922_; lean_object* v___f_923_; lean_object* v___x_924_; 
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = 5;
v___x_922_ = lean_box(v___x_921_);
lean_inc_ref(v_inst_906_);
v___f_923_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0___boxed), 8, 3);
lean_closure_set(v___f_923_, 0, v___x_922_);
lean_closure_set(v___f_923_, 1, v_inst_906_);
lean_closure_set(v___f_923_, 2, v___x_920_);
v___x_924_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_923_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_a_925_);
lean_dec_ref_known(v___x_924_, 1);
if (lean_obj_tag(v_a_925_) == 0)
{
lean_object* v___x_926_; 
lean_inc(v_a_918_);
lean_inc_ref(v_a_917_);
lean_inc(v_a_916_);
lean_inc_ref(v_a_915_);
lean_inc(v_a_914_);
lean_inc_ref(v_a_913_);
lean_inc(v_a_912_);
lean_inc_ref(v_a_911_);
lean_inc(v_a_910_);
lean_inc_ref(v_inst_906_);
v___x_926_ = lean_sym_simp(v_inst_906_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
lean_dec_ref_known(v___x_926_, 1);
if (lean_obj_tag(v_a_927_) == 0)
{
uint8_t v_contextDependent_928_; lean_object* v___x_929_; 
v_contextDependent_928_ = lean_ctor_get_uint8(v_a_927_, 1);
lean_dec_ref_known(v_a_927_, 0);
lean_inc_ref(v_inst_906_);
v___x_929_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(v_f_903_, v_00_u03b1_904_, v_c_905_, v_inst_906_, v_a_907_, v_b_908_, v_inst_906_, v_fallback_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; uint8_t v___y_932_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
if (v_contextDependent_928_ == 0)
{
lean_dec(v_a_930_);
return v___x_929_;
}
else
{
if (lean_obj_tag(v_a_930_) == 0)
{
uint8_t v_contextDependent_942_; 
v_contextDependent_942_ = lean_ctor_get_uint8(v_a_930_, 1);
v___y_932_ = v_contextDependent_942_;
goto v___jp_931_;
}
else
{
uint8_t v_contextDependent_943_; 
v_contextDependent_943_ = lean_ctor_get_uint8(v_a_930_, sizeof(void*)*2 + 1);
v___y_932_ = v_contextDependent_943_;
goto v___jp_931_;
}
}
v___jp_931_:
{
if (v___y_932_ == 0)
{
lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_940_; 
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_940_ == 0)
{
lean_object* v_unused_941_; 
v_unused_941_ = lean_ctor_get(v___x_929_, 0);
lean_dec(v_unused_941_);
v___x_934_ = v___x_929_;
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
else
{
lean_dec(v___x_929_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_930_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_936_);
v___x_938_ = v___x_934_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
else
{
lean_dec(v_a_930_);
return v___x_929_;
}
}
}
else
{
return v___x_929_;
}
}
else
{
lean_object* v_e_x27_944_; uint8_t v_contextDependent_945_; lean_object* v___x_946_; 
v_e_x27_944_ = lean_ctor_get(v_a_927_, 0);
lean_inc_ref(v_e_x27_944_);
v_contextDependent_945_ = lean_ctor_get_uint8(v_a_927_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_927_, 2);
v___x_946_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(v_f_903_, v_00_u03b1_904_, v_c_905_, v_inst_906_, v_a_907_, v_b_908_, v_e_x27_944_, v_fallback_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; uint8_t v___y_949_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
if (v_contextDependent_945_ == 0)
{
lean_dec(v_a_947_);
return v___x_946_;
}
else
{
if (lean_obj_tag(v_a_947_) == 0)
{
uint8_t v_contextDependent_959_; 
v_contextDependent_959_ = lean_ctor_get_uint8(v_a_947_, 1);
v___y_949_ = v_contextDependent_959_;
goto v___jp_948_;
}
else
{
uint8_t v_contextDependent_960_; 
v_contextDependent_960_ = lean_ctor_get_uint8(v_a_947_, sizeof(void*)*2 + 1);
v___y_949_ = v_contextDependent_960_;
goto v___jp_948_;
}
}
v___jp_948_:
{
if (v___y_949_ == 0)
{
lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_957_; 
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_957_ == 0)
{
lean_object* v_unused_958_; 
v_unused_958_ = lean_ctor_get(v___x_946_, 0);
lean_dec(v_unused_958_);
v___x_951_ = v___x_946_;
v_isShared_952_ = v_isSharedCheck_957_;
goto v_resetjp_950_;
}
else
{
lean_dec(v___x_946_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_957_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_953_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_947_);
if (v_isShared_952_ == 0)
{
lean_ctor_set(v___x_951_, 0, v___x_953_);
v___x_955_ = v___x_951_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
else
{
lean_dec(v_a_947_);
return v___x_946_;
}
}
}
else
{
return v___x_946_;
}
}
}
else
{
lean_dec_ref(v_fallback_909_);
lean_dec_ref(v_b_908_);
lean_dec_ref(v_a_907_);
lean_dec_ref(v_inst_906_);
lean_dec_ref(v_c_905_);
lean_dec_ref(v_00_u03b1_904_);
return v___x_926_;
}
}
else
{
lean_object* v_val_961_; lean_object* v___x_962_; 
v_val_961_ = lean_ctor_get(v_a_925_, 0);
lean_inc(v_val_961_);
lean_dec_ref_known(v_a_925_, 1);
v___x_962_ = l_Lean_Meta_Sym_shareCommonInc(v_val_961_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
lean_inc_n(v_a_963_, 3);
lean_dec_ref_known(v___x_962_, 1);
v___x_964_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2);
v___x_965_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8);
v___x_966_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10);
v___x_967_ = l_Lean_mkAppB(v___x_965_, v___x_966_, v_a_963_);
lean_inc(v_a_918_);
lean_inc_ref(v_a_917_);
lean_inc(v_a_916_);
lean_inc_ref(v_a_915_);
lean_inc(v_a_914_);
lean_inc_ref(v_a_913_);
lean_inc(v_a_912_);
lean_inc_ref(v_a_911_);
lean_inc(v_a_910_);
v___x_968_ = lean_sym_simp(v_a_963_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; uint8_t v___x_970_; lean_object* v_e_x27_972_; lean_object* v_proof_973_; uint8_t v_contextDependent_974_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
lean_dec_ref_known(v___x_968_, 1);
v___x_970_ = 0;
if (lean_obj_tag(v_a_969_) == 0)
{
uint8_t v_contextDependent_1011_; 
v_contextDependent_1011_ = lean_ctor_get_uint8(v_a_969_, 1);
lean_dec_ref_known(v_a_969_, 0);
v_e_x27_972_ = v_a_963_;
v_proof_973_ = v___x_967_;
v_contextDependent_974_ = v_contextDependent_1011_;
goto v___jp_971_;
}
else
{
lean_object* v_e_x27_1012_; lean_object* v_proof_1013_; uint8_t v_contextDependent_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_e_x27_1012_ = lean_ctor_get(v_a_969_, 0);
lean_inc_ref_n(v_e_x27_1012_, 2);
v_proof_1013_ = lean_ctor_get(v_a_969_, 1);
lean_inc_ref(v_proof_1013_);
v_contextDependent_1014_ = lean_ctor_get_uint8(v_a_969_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_969_, 2);
lean_inc_ref(v_inst_906_);
lean_inc_ref(v_c_905_);
v___x_1015_ = l_Lean_mkAppB(v___x_964_, v_c_905_, v_inst_906_);
v___x_1016_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___x_1015_, v_a_963_, v___x_967_, v_e_x27_1012_, v_proof_1013_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_object* v_a_1017_; 
v_a_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_a_1017_);
lean_dec_ref_known(v___x_1016_, 1);
v_e_x27_972_ = v_e_x27_1012_;
v_proof_973_ = v_a_1017_;
v_contextDependent_974_ = v_contextDependent_1014_;
goto v___jp_971_;
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec_ref(v_e_x27_1012_);
lean_dec_ref(v_fallback_909_);
lean_dec_ref(v_b_908_);
lean_dec_ref(v_a_907_);
lean_dec_ref(v_inst_906_);
lean_dec_ref(v_c_905_);
lean_dec_ref(v_00_u03b1_904_);
v_a_1018_ = lean_ctor_get(v___x_1016_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1016_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1016_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1016_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
v___jp_971_:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_x27_972_, v_a_916_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_1002_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_1002_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_1002_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_980_ = l_Lean_Expr_cleanupAnnotations(v_a_976_);
v___x_981_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_982_ = l_Lean_Expr_isConstOf(v___x_980_, v___x_981_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_983_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_984_ = l_Lean_Expr_isConstOf(v___x_980_, v___x_983_);
lean_dec_ref(v___x_980_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
lean_del_object(v___x_978_);
lean_dec_ref(v_proof_973_);
lean_dec_ref(v_b_908_);
lean_dec_ref(v_a_907_);
lean_dec_ref(v_inst_906_);
lean_dec_ref(v_c_905_);
lean_dec_ref(v_00_u03b1_904_);
lean_inc(v_a_918_);
lean_inc_ref(v_a_917_);
lean_inc(v_a_916_);
lean_inc_ref(v_a_915_);
lean_inc(v_a_914_);
lean_inc_ref(v_a_913_);
lean_inc(v_a_912_);
lean_inc_ref(v_a_911_);
lean_inc(v_a_910_);
v___x_985_ = lean_apply_10(v_fallback_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, lean_box(0));
return v___x_985_;
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
lean_dec_ref(v_fallback_909_);
v___x_986_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__12));
v___x_987_ = l_Lean_Expr_constLevels_x21(v_f_903_);
v___x_988_ = l_Lean_mkConst(v___x_986_, v___x_987_);
lean_inc_ref(v_a_907_);
v___x_989_ = l_Lean_mkApp6(v___x_988_, v_00_u03b1_904_, v_c_905_, v_inst_906_, v_a_907_, v_b_908_, v_proof_973_);
v___x_990_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_990_, 0, v_a_907_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
lean_ctor_set_uint8(v___x_990_, sizeof(void*)*2, v___x_970_);
lean_ctor_set_uint8(v___x_990_, sizeof(void*)*2 + 1, v_contextDependent_974_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_990_);
v___x_992_ = v___x_978_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
else
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
lean_dec_ref(v___x_980_);
lean_dec_ref(v_fallback_909_);
v___x_994_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__14));
v___x_995_ = l_Lean_Expr_constLevels_x21(v_f_903_);
v___x_996_ = l_Lean_mkConst(v___x_994_, v___x_995_);
lean_inc_ref(v_b_908_);
v___x_997_ = l_Lean_mkApp6(v___x_996_, v_00_u03b1_904_, v_c_905_, v_inst_906_, v_a_907_, v_b_908_, v_proof_973_);
v___x_998_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_998_, 0, v_b_908_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
lean_ctor_set_uint8(v___x_998_, sizeof(void*)*2, v___x_970_);
lean_ctor_set_uint8(v___x_998_, sizeof(void*)*2 + 1, v_contextDependent_974_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_998_);
v___x_1000_ = v___x_978_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
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
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref(v_proof_973_);
lean_dec_ref(v_fallback_909_);
lean_dec_ref(v_b_908_);
lean_dec_ref(v_a_907_);
lean_dec_ref(v_inst_906_);
lean_dec_ref(v_c_905_);
lean_dec_ref(v_00_u03b1_904_);
v_a_1003_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_975_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_975_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_967_);
lean_dec(v_a_963_);
lean_dec_ref(v_fallback_909_);
lean_dec_ref(v_b_908_);
lean_dec_ref(v_a_907_);
lean_dec_ref(v_inst_906_);
lean_dec_ref(v_c_905_);
lean_dec_ref(v_00_u03b1_904_);
return v___x_968_;
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec_ref(v_fallback_909_);
lean_dec_ref(v_b_908_);
lean_dec_ref(v_a_907_);
lean_dec_ref(v_inst_906_);
lean_dec_ref(v_c_905_);
lean_dec_ref(v_00_u03b1_904_);
v_a_1026_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_962_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_962_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec_ref(v_fallback_909_);
lean_dec_ref(v_b_908_);
lean_dec_ref(v_a_907_);
lean_dec_ref(v_inst_906_);
lean_dec_ref(v_c_905_);
lean_dec_ref(v_00_u03b1_904_);
v_a_1034_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_924_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_924_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___boxed(lean_object** _args){
lean_object* v_f_1042_ = _args[0];
lean_object* v_00_u03b1_1043_ = _args[1];
lean_object* v_c_1044_ = _args[2];
lean_object* v_inst_1045_ = _args[3];
lean_object* v_a_1046_ = _args[4];
lean_object* v_b_1047_ = _args[5];
lean_object* v_fallback_1048_ = _args[6];
lean_object* v_a_1049_ = _args[7];
lean_object* v_a_1050_ = _args[8];
lean_object* v_a_1051_ = _args[9];
lean_object* v_a_1052_ = _args[10];
lean_object* v_a_1053_ = _args[11];
lean_object* v_a_1054_ = _args[12];
lean_object* v_a_1055_ = _args[13];
lean_object* v_a_1056_ = _args[14];
lean_object* v_a_1057_ = _args[15];
lean_object* v_a_1058_ = _args[16];
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v_f_1042_, v_00_u03b1_1043_, v_c_1044_, v_inst_1045_, v_a_1046_, v_b_1047_, v_fallback_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_f_1042_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0(uint8_t v___x_1060_, lean_object* v_inst_x27_1061_, lean_object* v___x_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v___y_1069_; lean_object* v___x_1086_; uint8_t v_transparency_1087_; uint8_t v___x_1088_; 
v___x_1086_ = l_Lean_Meta_Context_config(v___y_1063_);
v_transparency_1087_ = lean_ctor_get_uint8(v___x_1086_, 9);
lean_dec_ref(v___x_1086_);
v___x_1088_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1087_, v___x_1060_);
if (v___x_1088_ == 0)
{
lean_object* v_keyedConfig_1089_; uint8_t v_trackZetaDelta_1090_; lean_object* v_zetaDeltaSet_1091_; lean_object* v_lctx_1092_; lean_object* v_localInstances_1093_; lean_object* v_defEqCtx_x3f_1094_; lean_object* v_synthPendingDepth_1095_; lean_object* v_customCanUnfoldPredicate_x3f_1096_; uint8_t v_univApprox_1097_; uint8_t v_inTypeClassResolution_1098_; uint8_t v_cacheInferType_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1108_; 
v_keyedConfig_1089_ = lean_ctor_get(v___y_1063_, 0);
v_trackZetaDelta_1090_ = lean_ctor_get_uint8(v___y_1063_, sizeof(void*)*7);
v_zetaDeltaSet_1091_ = lean_ctor_get(v___y_1063_, 1);
v_lctx_1092_ = lean_ctor_get(v___y_1063_, 2);
v_localInstances_1093_ = lean_ctor_get(v___y_1063_, 3);
v_defEqCtx_x3f_1094_ = lean_ctor_get(v___y_1063_, 4);
v_synthPendingDepth_1095_ = lean_ctor_get(v___y_1063_, 5);
v_customCanUnfoldPredicate_x3f_1096_ = lean_ctor_get(v___y_1063_, 6);
v_univApprox_1097_ = lean_ctor_get_uint8(v___y_1063_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1098_ = lean_ctor_get_uint8(v___y_1063_, sizeof(void*)*7 + 2);
v_cacheInferType_1099_ = lean_ctor_get_uint8(v___y_1063_, sizeof(void*)*7 + 3);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___y_1063_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1101_ = v___y_1063_;
v_isShared_1102_ = v_isSharedCheck_1108_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_1096_);
lean_inc(v_synthPendingDepth_1095_);
lean_inc(v_defEqCtx_x3f_1094_);
lean_inc(v_localInstances_1093_);
lean_inc(v_lctx_1092_);
lean_inc(v_zetaDeltaSet_1091_);
lean_inc(v_keyedConfig_1089_);
lean_dec(v___y_1063_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1108_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1103_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1060_, v_keyedConfig_1089_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 0, v___x_1103_);
v___x_1105_ = v___x_1101_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1103_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_zetaDeltaSet_1091_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v_lctx_1092_);
lean_ctor_set(v_reuseFailAlloc_1107_, 3, v_localInstances_1093_);
lean_ctor_set(v_reuseFailAlloc_1107_, 4, v_defEqCtx_x3f_1094_);
lean_ctor_set(v_reuseFailAlloc_1107_, 5, v_synthPendingDepth_1095_);
lean_ctor_set(v_reuseFailAlloc_1107_, 6, v_customCanUnfoldPredicate_x3f_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1107_, sizeof(void*)*7, v_trackZetaDelta_1090_);
lean_ctor_set_uint8(v_reuseFailAlloc_1107_, sizeof(void*)*7 + 1, v_univApprox_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1107_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1107_, sizeof(void*)*7 + 3, v_cacheInferType_1099_);
v___x_1105_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Lean_Meta_project_x3f(v_inst_x27_1061_, v___x_1062_, v___x_1105_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec_ref(v___x_1105_);
v___y_1069_ = v___x_1106_;
goto v___jp_1068_;
}
}
}
else
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_Meta_project_x3f(v_inst_x27_1061_, v___x_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec_ref(v___y_1063_);
v___y_1069_ = v___x_1109_;
goto v___jp_1068_;
}
v___jp_1068_:
{
if (lean_obj_tag(v___y_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
v_a_1070_ = lean_ctor_get(v___y_1069_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___y_1069_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___y_1069_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___y_1069_);
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
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
v_a_1078_ = lean_ctor_get(v___y_1069_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___y_1069_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___y_1069_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___y_1069_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0___boxed(lean_object* v___x_1110_, lean_object* v_inst_x27_1111_, lean_object* v___x_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
uint8_t v___x_15491__boxed_1118_; lean_object* v_res_1119_; 
v___x_15491__boxed_1118_ = lean_unbox(v___x_1110_);
v_res_1119_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0(v___x_15491__boxed_1118_, v_inst_x27_1111_, v___x_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
lean_dec(v___x_1112_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr(lean_object* v_f_1130_, lean_object* v_00_u03b1_1131_, lean_object* v_c_1132_, lean_object* v_inst_1133_, lean_object* v_a_1134_, lean_object* v_b_1135_, lean_object* v_c_x27_1136_, lean_object* v_h_1137_, lean_object* v_inst_x27_1138_, lean_object* v_fallback_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v___x_1150_; uint8_t v___x_1151_; lean_object* v___x_1152_; lean_object* v___f_1153_; lean_object* v___x_1154_; 
v___x_1150_ = lean_unsigned_to_nat(0u);
v___x_1151_ = 5;
v___x_1152_ = lean_box(v___x_1151_);
lean_inc_ref(v_inst_x27_1138_);
v___f_1153_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1153_, 0, v___x_1152_);
lean_closure_set(v___f_1153_, 1, v_inst_x27_1138_);
lean_closure_set(v___f_1153_, 2, v___x_1150_);
v___x_1154_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_1153_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1154_, 1);
if (lean_obj_tag(v_a_1155_) == 0)
{
lean_object* v___x_1156_; 
lean_inc(v_a_1148_);
lean_inc_ref(v_a_1147_);
lean_inc(v_a_1146_);
lean_inc_ref(v_a_1145_);
lean_inc(v_a_1144_);
lean_inc_ref(v_a_1143_);
lean_inc(v_a_1142_);
lean_inc_ref(v_a_1141_);
lean_inc(v_a_1140_);
lean_inc_ref(v_inst_x27_1138_);
v___x_1156_ = lean_sym_simp(v_inst_x27_1138_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1156_, 1);
if (lean_obj_tag(v_a_1157_) == 0)
{
uint8_t v_contextDependent_1158_; lean_object* v___x_1159_; 
v_contextDependent_1158_ = lean_ctor_get_uint8(v_a_1157_, 1);
lean_dec_ref_known(v_a_1157_, 0);
v___x_1159_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(v_f_1130_, v_00_u03b1_1131_, v_c_1132_, v_inst_1133_, v_a_1134_, v_b_1135_, v_c_x27_1136_, v_h_1137_, v_inst_x27_1138_, v_fallback_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; uint8_t v___y_1162_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1160_);
if (v_contextDependent_1158_ == 0)
{
lean_dec(v_a_1160_);
return v___x_1159_;
}
else
{
if (lean_obj_tag(v_a_1160_) == 0)
{
uint8_t v_contextDependent_1172_; 
v_contextDependent_1172_ = lean_ctor_get_uint8(v_a_1160_, 1);
v___y_1162_ = v_contextDependent_1172_;
goto v___jp_1161_;
}
else
{
uint8_t v_contextDependent_1173_; 
v_contextDependent_1173_ = lean_ctor_get_uint8(v_a_1160_, sizeof(void*)*2 + 1);
v___y_1162_ = v_contextDependent_1173_;
goto v___jp_1161_;
}
}
v___jp_1161_:
{
if (v___y_1162_ == 0)
{
lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1170_; 
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1170_ == 0)
{
lean_object* v_unused_1171_; 
v_unused_1171_ = lean_ctor_get(v___x_1159_, 0);
lean_dec(v_unused_1171_);
v___x_1164_ = v___x_1159_;
v_isShared_1165_ = v_isSharedCheck_1170_;
goto v_resetjp_1163_;
}
else
{
lean_dec(v___x_1159_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1170_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1166_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1160_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1166_);
v___x_1168_ = v___x_1164_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
else
{
lean_dec(v_a_1160_);
return v___x_1159_;
}
}
}
else
{
return v___x_1159_;
}
}
else
{
lean_object* v_e_x27_1174_; uint8_t v_contextDependent_1175_; lean_object* v___x_1176_; 
lean_dec_ref(v_inst_x27_1138_);
v_e_x27_1174_ = lean_ctor_get(v_a_1157_, 0);
lean_inc_ref(v_e_x27_1174_);
v_contextDependent_1175_ = lean_ctor_get_uint8(v_a_1157_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1157_, 2);
v___x_1176_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(v_f_1130_, v_00_u03b1_1131_, v_c_1132_, v_inst_1133_, v_a_1134_, v_b_1135_, v_c_x27_1136_, v_h_1137_, v_e_x27_1174_, v_fallback_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; uint8_t v___y_1179_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_a_1177_);
if (v_contextDependent_1175_ == 0)
{
lean_dec(v_a_1177_);
return v___x_1176_;
}
else
{
if (lean_obj_tag(v_a_1177_) == 0)
{
uint8_t v_contextDependent_1189_; 
v_contextDependent_1189_ = lean_ctor_get_uint8(v_a_1177_, 1);
v___y_1179_ = v_contextDependent_1189_;
goto v___jp_1178_;
}
else
{
uint8_t v_contextDependent_1190_; 
v_contextDependent_1190_ = lean_ctor_get_uint8(v_a_1177_, sizeof(void*)*2 + 1);
v___y_1179_ = v_contextDependent_1190_;
goto v___jp_1178_;
}
}
v___jp_1178_:
{
if (v___y_1179_ == 0)
{
lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1187_; 
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1187_ == 0)
{
lean_object* v_unused_1188_; 
v_unused_1188_ = lean_ctor_get(v___x_1176_, 0);
lean_dec(v_unused_1188_);
v___x_1181_ = v___x_1176_;
v_isShared_1182_ = v_isSharedCheck_1187_;
goto v_resetjp_1180_;
}
else
{
lean_dec(v___x_1176_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1187_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1177_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1183_);
v___x_1185_ = v___x_1181_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
else
{
lean_dec(v_a_1177_);
return v___x_1176_;
}
}
}
else
{
return v___x_1176_;
}
}
}
else
{
lean_dec_ref(v_fallback_1139_);
lean_dec_ref(v_inst_x27_1138_);
lean_dec_ref(v_h_1137_);
lean_dec_ref(v_c_x27_1136_);
lean_dec_ref(v_b_1135_);
lean_dec_ref(v_a_1134_);
lean_dec_ref(v_inst_1133_);
lean_dec_ref(v_c_1132_);
lean_dec_ref(v_00_u03b1_1131_);
return v___x_1156_;
}
}
else
{
lean_object* v_val_1191_; lean_object* v___x_1192_; 
v_val_1191_ = lean_ctor_get(v_a_1155_, 0);
lean_inc(v_val_1191_);
lean_dec_ref_known(v_a_1155_, 1);
v___x_1192_ = l_Lean_Meta_Sym_shareCommonInc(v_val_1191_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc_n(v_a_1193_, 3);
lean_dec_ref_known(v___x_1192_, 1);
v___x_1194_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2);
v___x_1195_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8);
v___x_1196_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10);
v___x_1197_ = l_Lean_mkAppB(v___x_1195_, v___x_1196_, v_a_1193_);
lean_inc(v_a_1148_);
lean_inc_ref(v_a_1147_);
lean_inc(v_a_1146_);
lean_inc_ref(v_a_1145_);
lean_inc(v_a_1144_);
lean_inc_ref(v_a_1143_);
lean_inc(v_a_1142_);
lean_inc_ref(v_a_1141_);
lean_inc(v_a_1140_);
v___x_1198_ = lean_sym_simp(v_a_1193_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; uint8_t v___x_1200_; lean_object* v_e_x27_1202_; lean_object* v_proof_1203_; uint8_t v_contextDependent_1204_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1198_, 1);
v___x_1200_ = 0;
if (lean_obj_tag(v_a_1199_) == 0)
{
uint8_t v_contextDependent_1241_; 
v_contextDependent_1241_ = lean_ctor_get_uint8(v_a_1199_, 1);
lean_dec_ref_known(v_a_1199_, 0);
v_e_x27_1202_ = v_a_1193_;
v_proof_1203_ = v___x_1197_;
v_contextDependent_1204_ = v_contextDependent_1241_;
goto v___jp_1201_;
}
else
{
lean_object* v_e_x27_1242_; lean_object* v_proof_1243_; uint8_t v_contextDependent_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v_e_x27_1242_ = lean_ctor_get(v_a_1199_, 0);
lean_inc_ref_n(v_e_x27_1242_, 2);
v_proof_1243_ = lean_ctor_get(v_a_1199_, 1);
lean_inc_ref(v_proof_1243_);
v_contextDependent_1244_ = lean_ctor_get_uint8(v_a_1199_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1199_, 2);
lean_inc_ref(v_inst_x27_1138_);
lean_inc_ref(v_c_x27_1136_);
v___x_1245_ = l_Lean_mkAppB(v___x_1194_, v_c_x27_1136_, v_inst_x27_1138_);
v___x_1246_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___x_1245_, v_a_1193_, v___x_1197_, v_e_x27_1242_, v_proof_1243_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1246_, 1);
v_e_x27_1202_ = v_e_x27_1242_;
v_proof_1203_ = v_a_1247_;
v_contextDependent_1204_ = v_contextDependent_1244_;
goto v___jp_1201_;
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec_ref(v_e_x27_1242_);
lean_dec_ref(v_fallback_1139_);
lean_dec_ref(v_inst_x27_1138_);
lean_dec_ref(v_h_1137_);
lean_dec_ref(v_c_x27_1136_);
lean_dec_ref(v_b_1135_);
lean_dec_ref(v_a_1134_);
lean_dec_ref(v_inst_1133_);
lean_dec_ref(v_c_1132_);
lean_dec_ref(v_00_u03b1_1131_);
v_a_1248_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1246_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1246_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
v___jp_1201_:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_x27_1202_, v_a_1146_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1232_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1232_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1232_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v___x_1210_ = l_Lean_Expr_cleanupAnnotations(v_a_1206_);
v___x_1211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_1212_ = l_Lean_Expr_isConstOf(v___x_1210_, v___x_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_1214_ = l_Lean_Expr_isConstOf(v___x_1210_, v___x_1213_);
lean_dec_ref(v___x_1210_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; 
lean_del_object(v___x_1208_);
lean_dec_ref(v_proof_1203_);
lean_dec_ref(v_inst_x27_1138_);
lean_dec_ref(v_h_1137_);
lean_dec_ref(v_c_x27_1136_);
lean_dec_ref(v_b_1135_);
lean_dec_ref(v_a_1134_);
lean_dec_ref(v_inst_1133_);
lean_dec_ref(v_c_1132_);
lean_dec_ref(v_00_u03b1_1131_);
lean_inc(v_a_1148_);
lean_inc_ref(v_a_1147_);
lean_inc(v_a_1146_);
lean_inc_ref(v_a_1145_);
lean_inc(v_a_1144_);
lean_inc_ref(v_a_1143_);
lean_inc(v_a_1142_);
lean_inc_ref(v_a_1141_);
lean_inc(v_a_1140_);
v___x_1215_ = lean_apply_10(v_fallback_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, lean_box(0));
return v___x_1215_;
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1222_; 
lean_dec_ref(v_fallback_1139_);
v___x_1216_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__1));
v___x_1217_ = l_Lean_Expr_constLevels_x21(v_f_1130_);
v___x_1218_ = l_Lean_mkConst(v___x_1216_, v___x_1217_);
lean_inc_ref(v_a_1134_);
v___x_1219_ = l_Lean_mkApp9(v___x_1218_, v_00_u03b1_1131_, v_c_1132_, v_inst_1133_, v_a_1134_, v_b_1135_, v_c_x27_1136_, v_h_1137_, v_inst_x27_1138_, v_proof_1203_);
v___x_1220_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1220_, 0, v_a_1134_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
lean_ctor_set_uint8(v___x_1220_, sizeof(void*)*2, v___x_1200_);
lean_ctor_set_uint8(v___x_1220_, sizeof(void*)*2 + 1, v_contextDependent_1204_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1220_);
v___x_1222_ = v___x_1208_;
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
else
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
lean_dec_ref(v___x_1210_);
lean_dec_ref(v_fallback_1139_);
v___x_1224_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__3));
v___x_1225_ = l_Lean_Expr_constLevels_x21(v_f_1130_);
v___x_1226_ = l_Lean_mkConst(v___x_1224_, v___x_1225_);
lean_inc_ref(v_b_1135_);
v___x_1227_ = l_Lean_mkApp9(v___x_1226_, v_00_u03b1_1131_, v_c_1132_, v_inst_1133_, v_a_1134_, v_b_1135_, v_c_x27_1136_, v_h_1137_, v_inst_x27_1138_, v_proof_1203_);
v___x_1228_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1228_, 0, v_b_1135_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
lean_ctor_set_uint8(v___x_1228_, sizeof(void*)*2, v___x_1200_);
lean_ctor_set_uint8(v___x_1228_, sizeof(void*)*2 + 1, v_contextDependent_1204_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v___x_1228_);
v___x_1230_ = v___x_1208_;
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
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec_ref(v_proof_1203_);
lean_dec_ref(v_fallback_1139_);
lean_dec_ref(v_inst_x27_1138_);
lean_dec_ref(v_h_1137_);
lean_dec_ref(v_c_x27_1136_);
lean_dec_ref(v_b_1135_);
lean_dec_ref(v_a_1134_);
lean_dec_ref(v_inst_1133_);
lean_dec_ref(v_c_1132_);
lean_dec_ref(v_00_u03b1_1131_);
v_a_1233_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1205_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1205_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1197_);
lean_dec(v_a_1193_);
lean_dec_ref(v_fallback_1139_);
lean_dec_ref(v_inst_x27_1138_);
lean_dec_ref(v_h_1137_);
lean_dec_ref(v_c_x27_1136_);
lean_dec_ref(v_b_1135_);
lean_dec_ref(v_a_1134_);
lean_dec_ref(v_inst_1133_);
lean_dec_ref(v_c_1132_);
lean_dec_ref(v_00_u03b1_1131_);
return v___x_1198_;
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec_ref(v_fallback_1139_);
lean_dec_ref(v_inst_x27_1138_);
lean_dec_ref(v_h_1137_);
lean_dec_ref(v_c_x27_1136_);
lean_dec_ref(v_b_1135_);
lean_dec_ref(v_a_1134_);
lean_dec_ref(v_inst_1133_);
lean_dec_ref(v_c_1132_);
lean_dec_ref(v_00_u03b1_1131_);
v_a_1256_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1192_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1192_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec_ref(v_fallback_1139_);
lean_dec_ref(v_inst_x27_1138_);
lean_dec_ref(v_h_1137_);
lean_dec_ref(v_c_x27_1136_);
lean_dec_ref(v_b_1135_);
lean_dec_ref(v_a_1134_);
lean_dec_ref(v_inst_1133_);
lean_dec_ref(v_c_1132_);
lean_dec_ref(v_00_u03b1_1131_);
v_a_1264_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1154_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1154_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_1272_ = _args[0];
lean_object* v_00_u03b1_1273_ = _args[1];
lean_object* v_c_1274_ = _args[2];
lean_object* v_inst_1275_ = _args[3];
lean_object* v_a_1276_ = _args[4];
lean_object* v_b_1277_ = _args[5];
lean_object* v_c_x27_1278_ = _args[6];
lean_object* v_h_1279_ = _args[7];
lean_object* v_inst_x27_1280_ = _args[8];
lean_object* v_fallback_1281_ = _args[9];
lean_object* v_a_1282_ = _args[10];
lean_object* v_a_1283_ = _args[11];
lean_object* v_a_1284_ = _args[12];
lean_object* v_a_1285_ = _args[13];
lean_object* v_a_1286_ = _args[14];
lean_object* v_a_1287_ = _args[15];
lean_object* v_a_1288_ = _args[16];
lean_object* v_a_1289_ = _args[17];
lean_object* v_a_1290_ = _args[18];
lean_object* v_a_1291_ = _args[19];
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr(v_f_1272_, v_00_u03b1_1273_, v_c_1274_, v_inst_1275_, v_a_1276_, v_b_1277_, v_c_x27_1278_, v_h_1279_, v_inst_x27_1280_, v_fallback_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec(v_a_1290_);
lean_dec_ref(v_a_1289_);
lean_dec(v_a_1288_);
lean_dec_ref(v_a_1287_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_f_1272_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0(lean_object* v___x_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1293_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed(lean_object* v___x_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0(v___x_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg(lean_object* v_f_1317_, lean_object* v_a_u2081_1318_, lean_object* v_a_u2082_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(v_f_1317_, v_a_u2081_1318_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_object* v_a_1328_; lean_object* v___x_1329_; 
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
lean_inc(v_a_1328_);
lean_dec_ref_known(v___x_1327_, 1);
v___x_1329_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(v_a_1328_, v_a_u2082_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
return v___x_1329_;
}
else
{
lean_dec_ref(v_a_u2082_1319_);
return v___x_1327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_1330_, lean_object* v_a_u2081_1331_, lean_object* v_a_u2082_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg(v_f_1330_, v_a_u2081_1331_, v_a_u2082_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(lean_object* v_f_1341_, lean_object* v_a_u2081_1342_, lean_object* v_a_u2082_1343_, lean_object* v_a_u2083_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg(v_f_1341_, v_a_u2081_1342_, v_a_u2082_1343_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_a_1356_; lean_object* v___x_1357_; 
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v___x_1355_, 1);
v___x_1357_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(v_a_1356_, v_a_u2083_1344_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
return v___x_1357_;
}
else
{
lean_dec_ref(v_a_u2083_1344_);
return v___x_1355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___boxed(lean_object* v_f_1358_, lean_object* v_a_u2081_1359_, lean_object* v_a_u2082_1360_, lean_object* v_a_u2083_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(v_f_1358_, v_a_u2081_1359_, v_a_u2082_1360_, v_a_u2083_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(lean_object* v_f_1373_, lean_object* v_a_u2081_1374_, lean_object* v_a_u2082_1375_, lean_object* v_a_u2083_1376_, lean_object* v_a_u2084_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(v_f_1373_, v_a_u2081_1374_, v_a_u2082_1375_, v_a_u2083_1376_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1390_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref_known(v___x_1388_, 1);
v___x_1390_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(v_a_1389_, v_a_u2084_1377_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
return v___x_1390_;
}
else
{
lean_dec_ref(v_a_u2084_1377_);
return v___x_1388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0___boxed(lean_object* v_f_1391_, lean_object* v_a_u2081_1392_, lean_object* v_a_u2082_1393_, lean_object* v_a_u2083_1394_, lean_object* v_a_u2084_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v_f_1391_, v_a_u2081_1392_, v_a_u2082_1393_, v_a_u2083_1394_, v_a_u2084_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2(lean_object* v___x_1412_, lean_object* v_e_x27_1413_, lean_object* v_snd_1414_, lean_object* v_arg_1415_, lean_object* v_arg_1416_, lean_object* v_e_1417_, lean_object* v_proof_1418_, uint8_t v___x_1419_, uint8_t v_contextDependent_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1431_; 
lean_inc_ref(v_snd_1414_);
lean_inc_ref(v_e_x27_1413_);
v___x_1431_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v___x_1412_, v_e_x27_1413_, v_snd_1414_, v_arg_1415_, v_arg_1416_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1443_; 
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1434_ = v___x_1431_;
v_isShared_1435_ = v_isSharedCheck_1443_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1431_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1443_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1436_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1));
v___x_1437_ = l_Lean_Expr_replaceFn(v_e_1417_, v___x_1436_);
v___x_1438_ = l_Lean_mkApp3(v___x_1437_, v_e_x27_1413_, v_snd_1414_, v_proof_1418_);
v___x_1439_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1439_, 0, v_a_1432_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
lean_ctor_set_uint8(v___x_1439_, sizeof(void*)*2, v___x_1419_);
lean_ctor_set_uint8(v___x_1439_, sizeof(void*)*2 + 1, v_contextDependent_1420_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1439_);
v___x_1441_ = v___x_1434_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec_ref(v_proof_1418_);
lean_dec_ref(v_e_1417_);
lean_dec_ref(v_snd_1414_);
lean_dec_ref(v_e_x27_1413_);
v_a_1444_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1431_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1431_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___boxed(lean_object** _args){
lean_object* v___x_1452_ = _args[0];
lean_object* v_e_x27_1453_ = _args[1];
lean_object* v_snd_1454_ = _args[2];
lean_object* v_arg_1455_ = _args[3];
lean_object* v_arg_1456_ = _args[4];
lean_object* v_e_1457_ = _args[5];
lean_object* v_proof_1458_ = _args[6];
lean_object* v___x_1459_ = _args[7];
lean_object* v_contextDependent_1460_ = _args[8];
lean_object* v___y_1461_ = _args[9];
lean_object* v___y_1462_ = _args[10];
lean_object* v___y_1463_ = _args[11];
lean_object* v___y_1464_ = _args[12];
lean_object* v___y_1465_ = _args[13];
lean_object* v___y_1466_ = _args[14];
lean_object* v___y_1467_ = _args[15];
lean_object* v___y_1468_ = _args[16];
lean_object* v___y_1469_ = _args[17];
lean_object* v___y_1470_ = _args[18];
_start:
{
uint8_t v___x_14775__boxed_1471_; uint8_t v_contextDependent_14776__boxed_1472_; lean_object* v_res_1473_; 
v___x_14775__boxed_1471_ = lean_unbox(v___x_1459_);
v_contextDependent_14776__boxed_1472_ = lean_unbox(v_contextDependent_1460_);
v_res_1473_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2(v___x_1452_, v_e_x27_1453_, v_snd_1454_, v_arg_1455_, v_arg_1456_, v_e_1457_, v_proof_1458_, v___x_14775__boxed_1471_, v_contextDependent_14776__boxed_1472_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1(uint8_t v___x_1487_, lean_object* v_e_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v___x_1502_; uint8_t v___x_1503_; 
lean_inc_ref(v_e_1488_);
v___x_1502_ = l_Lean_Expr_cleanupAnnotations(v_e_1488_);
v___x_1503_ = l_Lean_Expr_isApp(v___x_1502_);
if (v___x_1503_ == 0)
{
lean_dec_ref(v___x_1502_);
lean_dec_ref(v_e_1488_);
goto v___jp_1499_;
}
else
{
lean_object* v_arg_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; 
v_arg_1504_ = lean_ctor_get(v___x_1502_, 1);
lean_inc_ref(v_arg_1504_);
v___x_1505_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1502_);
v___x_1506_ = l_Lean_Expr_isApp(v___x_1505_);
if (v___x_1506_ == 0)
{
lean_dec_ref(v___x_1505_);
lean_dec_ref(v_arg_1504_);
lean_dec_ref(v_e_1488_);
goto v___jp_1499_;
}
else
{
lean_object* v_arg_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
v_arg_1507_ = lean_ctor_get(v___x_1505_, 1);
lean_inc_ref(v_arg_1507_);
v___x_1508_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1505_);
v___x_1509_ = l_Lean_Expr_isApp(v___x_1508_);
if (v___x_1509_ == 0)
{
lean_dec_ref(v___x_1508_);
lean_dec_ref(v_arg_1507_);
lean_dec_ref(v_arg_1504_);
lean_dec_ref(v_e_1488_);
goto v___jp_1499_;
}
else
{
lean_object* v_arg_1510_; lean_object* v___x_1511_; uint8_t v___x_1512_; 
v_arg_1510_ = lean_ctor_get(v___x_1508_, 1);
lean_inc_ref(v_arg_1510_);
v___x_1511_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1508_);
v___x_1512_ = l_Lean_Expr_isApp(v___x_1511_);
if (v___x_1512_ == 0)
{
lean_dec_ref(v___x_1511_);
lean_dec_ref(v_arg_1510_);
lean_dec_ref(v_arg_1507_);
lean_dec_ref(v_arg_1504_);
lean_dec_ref(v_e_1488_);
goto v___jp_1499_;
}
else
{
lean_object* v_arg_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; 
v_arg_1513_ = lean_ctor_get(v___x_1511_, 1);
lean_inc_ref(v_arg_1513_);
v___x_1514_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1511_);
v___x_1515_ = l_Lean_Expr_isApp(v___x_1514_);
if (v___x_1515_ == 0)
{
lean_dec_ref(v___x_1514_);
lean_dec_ref(v_arg_1513_);
lean_dec_ref(v_arg_1510_);
lean_dec_ref(v_arg_1507_);
lean_dec_ref(v_arg_1504_);
lean_dec_ref(v_e_1488_);
goto v___jp_1499_;
}
else
{
lean_object* v_arg_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v_arg_1516_ = lean_ctor_get(v___x_1514_, 1);
lean_inc_ref(v_arg_1516_);
v___x_1517_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1514_);
v___x_1518_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1));
v___x_1519_ = l_Lean_Expr_isConstOf(v___x_1517_, v___x_1518_);
if (v___x_1519_ == 0)
{
lean_dec_ref(v___x_1517_);
lean_dec_ref(v_arg_1516_);
lean_dec_ref(v_arg_1513_);
lean_dec_ref(v_arg_1510_);
lean_dec_ref(v_arg_1507_);
lean_dec_ref(v_arg_1504_);
lean_dec_ref(v_e_1488_);
goto v___jp_1499_;
}
else
{
lean_object* v___x_1520_; 
lean_inc(v___y_1497_);
lean_inc_ref(v___y_1496_);
lean_inc(v___y_1495_);
lean_inc_ref(v___y_1494_);
lean_inc(v___y_1493_);
lean_inc_ref(v___y_1492_);
lean_inc(v___y_1491_);
lean_inc_ref(v___y_1490_);
lean_inc(v___y_1489_);
lean_inc_ref(v_arg_1513_);
v___x_1520_ = lean_sym_simp(v_arg_1513_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1520_, 1);
if (lean_obj_tag(v_a_1521_) == 0)
{
uint8_t v_contextDependent_1522_; lean_object* v___x_1523_; 
lean_dec_ref(v_e_1488_);
v_contextDependent_1522_ = lean_ctor_get_uint8(v_a_1521_, 1);
lean_dec_ref_known(v_a_1521_, 0);
v___x_1523_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_1513_, v___y_1492_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1564_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1526_ = v___x_1523_;
v_isShared_1527_ = v_isSharedCheck_1564_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1523_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1564_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
uint8_t v___x_1528_; 
v___x_1528_ = lean_unbox(v_a_1524_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
lean_del_object(v___x_1526_);
v___x_1529_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_1513_, v___y_1492_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1547_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1547_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1547_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
uint8_t v___x_1534_; 
v___x_1534_ = lean_unbox(v_a_1530_);
lean_dec(v_a_1530_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___f_1536_; lean_object* v___x_1537_; 
lean_del_object(v___x_1532_);
lean_dec(v_a_1524_);
v___x_1535_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_1519_, v_contextDependent_1522_);
v___f_1536_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1536_, 0, v___x_1535_);
v___x_1537_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v___x_1517_, v_arg_1516_, v_arg_1513_, v_arg_1510_, v_arg_1507_, v_arg_1504_, v___f_1536_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec_ref(v___x_1517_);
return v___x_1537_;
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; lean_object* v___x_1545_; 
lean_dec_ref(v_arg_1513_);
lean_dec_ref(v_arg_1510_);
v___x_1538_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__2));
v___x_1539_ = l_Lean_Expr_constLevels_x21(v___x_1517_);
lean_dec_ref(v___x_1517_);
v___x_1540_ = l_Lean_mkConst(v___x_1538_, v___x_1539_);
lean_inc_ref(v_arg_1504_);
v___x_1541_ = l_Lean_mkApp3(v___x_1540_, v_arg_1516_, v_arg_1507_, v_arg_1504_);
v___x_1542_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1542_, 0, v_arg_1504_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = lean_unbox(v_a_1524_);
lean_dec(v_a_1524_);
lean_ctor_set_uint8(v___x_1542_, sizeof(void*)*2, v___x_1543_);
lean_ctor_set_uint8(v___x_1542_, sizeof(void*)*2 + 1, v_contextDependent_1522_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 0, v___x_1542_);
v___x_1545_ = v___x_1532_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1542_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_dec(v_a_1524_);
lean_dec_ref(v___x_1517_);
lean_dec_ref(v_arg_1516_);
lean_dec_ref(v_arg_1513_);
lean_dec_ref(v_arg_1510_);
lean_dec_ref(v_arg_1507_);
lean_dec_ref(v_arg_1504_);
v_a_1548_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1529_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1529_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1562_; 
lean_dec(v_a_1524_);
lean_dec_ref(v_arg_1513_);
lean_dec_ref(v_arg_1510_);
v___x_1556_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__3));
v___x_1557_ = l_Lean_Expr_constLevels_x21(v___x_1517_);
lean_dec_ref(v___x_1517_);
v___x_1558_ = l_Lean_mkConst(v___x_1556_, v___x_1557_);
lean_inc_ref(v_arg_1507_);
v___x_1559_ = l_Lean_mkApp3(v___x_1558_, v_arg_1516_, v_arg_1507_, v_arg_1504_);
v___x_1560_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1560_, 0, v_arg_1507_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
lean_ctor_set_uint8(v___x_1560_, sizeof(void*)*2, v___x_1487_);
lean_ctor_set_uint8(v___x_1560_, sizeof(void*)*2 + 1, v_contextDependent_1522_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1560_);
v___x_1562_ = v___x_1526_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec_ref(v___x_1517_);
lean_dec_ref(v_arg_1516_);
lean_dec_ref(v_arg_1513_);
lean_dec_ref(v_arg_1510_);
lean_dec_ref(v_arg_1507_);
lean_dec_ref(v_arg_1504_);
v_a_1565_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1523_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1523_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
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
lean_object* v_e_x27_1573_; lean_object* v_proof_1574_; uint8_t v_contextDependent_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1653_; 
v_e_x27_1573_ = lean_ctor_get(v_a_1521_, 0);
v_proof_1574_ = lean_ctor_get(v_a_1521_, 1);
v_contextDependent_1575_ = lean_ctor_get_uint8(v_a_1521_, sizeof(void*)*2 + 1);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_a_1521_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1577_ = v_a_1521_;
v_isShared_1578_ = v_isSharedCheck_1653_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_proof_1574_);
lean_inc(v_e_x27_1573_);
lean_dec(v_a_1521_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1653_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_1573_, v___y_1492_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1644_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1644_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1644_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
uint8_t v___x_1584_; 
v___x_1584_ = lean_unbox(v_a_1580_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; 
lean_del_object(v___x_1582_);
v___x_1585_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_1573_, v___y_1492_);
lean_dec_ref(v_e_x27_1573_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1626_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1588_ = v___x_1585_;
v_isShared_1589_ = v_isSharedCheck_1626_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1585_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1626_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
uint8_t v___x_1590_; 
v___x_1590_ = lean_unbox(v_a_1586_);
lean_dec(v_a_1586_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1591_; 
lean_del_object(v___x_1588_);
lean_dec(v_a_1580_);
lean_del_object(v___x_1577_);
lean_dec_ref(v_proof_1574_);
lean_inc_ref(v_arg_1510_);
v___x_1591_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance(v_arg_1510_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v_fst_1593_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1591_, 1);
v_fst_1593_ = lean_ctor_get(v_a_1592_, 0);
lean_inc(v_fst_1593_);
if (lean_obj_tag(v_fst_1593_) == 0)
{
uint8_t v_contextDependent_1594_; lean_object* v___x_1595_; lean_object* v___f_1596_; lean_object* v___x_1597_; 
lean_dec(v_a_1592_);
lean_dec_ref(v_e_1488_);
v_contextDependent_1594_ = lean_ctor_get_uint8(v_fst_1593_, 1);
lean_dec_ref_known(v_fst_1593_, 0);
v___x_1595_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_1519_, v_contextDependent_1594_);
v___f_1596_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1596_, 0, v___x_1595_);
v___x_1597_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v___x_1517_, v_arg_1516_, v_arg_1513_, v_arg_1510_, v_arg_1507_, v_arg_1504_, v___f_1596_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec_ref(v___x_1517_);
return v___x_1597_;
}
else
{
lean_object* v_snd_1598_; lean_object* v_e_x27_1599_; lean_object* v_proof_1600_; uint8_t v_contextDependent_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___f_1606_; lean_object* v___x_1607_; 
v_snd_1598_ = lean_ctor_get(v_a_1592_, 1);
lean_inc_n(v_snd_1598_, 2);
lean_dec(v_a_1592_);
v_e_x27_1599_ = lean_ctor_get(v_fst_1593_, 0);
lean_inc_ref_n(v_e_x27_1599_, 2);
v_proof_1600_ = lean_ctor_get(v_fst_1593_, 1);
lean_inc_ref_n(v_proof_1600_, 2);
v_contextDependent_1601_ = lean_ctor_get_uint8(v_fst_1593_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_1593_, 2);
v___x_1602_ = lean_unsigned_to_nat(4u);
v___x_1603_ = l_Lean_Expr_getBoundedAppFn(v___x_1602_, v_e_1488_);
v___x_1604_ = lean_box(v___x_1519_);
v___x_1605_ = lean_box(v_contextDependent_1601_);
lean_inc_ref(v_arg_1504_);
lean_inc_ref(v_arg_1507_);
v___f_1606_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___boxed), 19, 9);
lean_closure_set(v___f_1606_, 0, v___x_1603_);
lean_closure_set(v___f_1606_, 1, v_e_x27_1599_);
lean_closure_set(v___f_1606_, 2, v_snd_1598_);
lean_closure_set(v___f_1606_, 3, v_arg_1507_);
lean_closure_set(v___f_1606_, 4, v_arg_1504_);
lean_closure_set(v___f_1606_, 5, v_e_1488_);
lean_closure_set(v___f_1606_, 6, v_proof_1600_);
lean_closure_set(v___f_1606_, 7, v___x_1604_);
lean_closure_set(v___f_1606_, 8, v___x_1605_);
v___x_1607_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr(v___x_1517_, v_arg_1516_, v_arg_1513_, v_arg_1510_, v_arg_1507_, v_arg_1504_, v_e_x27_1599_, v_proof_1600_, v_snd_1598_, v___f_1606_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec_ref(v___x_1517_);
return v___x_1607_;
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec_ref(v___x_1517_);
lean_dec_ref(v_arg_1516_);
lean_dec_ref(v_arg_1513_);
lean_dec_ref(v_arg_1510_);
lean_dec_ref(v_arg_1507_);
lean_dec_ref(v_arg_1504_);
lean_dec_ref(v_e_1488_);
v_a_1608_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1591_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1591_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1620_; 
lean_dec_ref(v___x_1517_);
lean_dec_ref(v_arg_1516_);
lean_dec_ref(v_arg_1513_);
lean_dec_ref(v_arg_1510_);
lean_dec_ref(v_arg_1507_);
v___x_1616_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__5));
v___x_1617_ = l_Lean_Expr_replaceFn(v_e_1488_, v___x_1616_);
v___x_1618_ = l_Lean_Expr_app___override(v___x_1617_, v_proof_1574_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 1, v___x_1618_);
lean_ctor_set(v___x_1577_, 0, v_arg_1504_);
v___x_1620_ = v___x_1577_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_arg_1504_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
uint8_t v___x_1621_; lean_object* v___x_1623_; 
v___x_1621_ = lean_unbox(v_a_1580_);
lean_dec(v_a_1580_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*2, v___x_1621_);
lean_ctor_set_uint8(v___x_1620_, sizeof(void*)*2 + 1, v_contextDependent_1575_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 0, v___x_1620_);
v___x_1623_ = v___x_1588_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1620_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_dec(v_a_1580_);
lean_del_object(v___x_1577_);
lean_dec_ref(v_proof_1574_);
lean_dec_ref(v___x_1517_);
lean_dec_ref(v_arg_1516_);
lean_dec_ref(v_arg_1513_);
lean_dec_ref(v_arg_1510_);
lean_dec_ref(v_arg_1507_);
lean_dec_ref(v_arg_1504_);
lean_dec_ref(v_e_1488_);
v_a_1627_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1585_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1585_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
else
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1639_; 
lean_dec(v_a_1580_);
lean_dec_ref(v_e_x27_1573_);
lean_dec_ref(v___x_1517_);
lean_dec_ref(v_arg_1516_);
lean_dec_ref(v_arg_1513_);
lean_dec_ref(v_arg_1510_);
lean_dec_ref(v_arg_1504_);
v___x_1635_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__7));
v___x_1636_ = l_Lean_Expr_replaceFn(v_e_1488_, v___x_1635_);
v___x_1637_ = l_Lean_Expr_app___override(v___x_1636_, v_proof_1574_);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 1, v___x_1637_);
lean_ctor_set(v___x_1577_, 0, v_arg_1507_);
v___x_1639_ = v___x_1577_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_arg_1507_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v___x_1637_);
lean_ctor_set_uint8(v_reuseFailAlloc_1643_, sizeof(void*)*2 + 1, v_contextDependent_1575_);
v___x_1639_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1641_; 
lean_ctor_set_uint8(v___x_1639_, sizeof(void*)*2, v___x_1487_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v___x_1639_);
v___x_1641_ = v___x_1582_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_del_object(v___x_1577_);
lean_dec_ref(v_proof_1574_);
lean_dec_ref(v_e_x27_1573_);
lean_dec_ref(v___x_1517_);
lean_dec_ref(v_arg_1516_);
lean_dec_ref(v_arg_1513_);
lean_dec_ref(v_arg_1510_);
lean_dec_ref(v_arg_1507_);
lean_dec_ref(v_arg_1504_);
lean_dec_ref(v_e_1488_);
v_a_1645_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1579_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1579_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_1517_);
lean_dec_ref(v_arg_1516_);
lean_dec_ref(v_arg_1513_);
lean_dec_ref(v_arg_1510_);
lean_dec_ref(v_arg_1507_);
lean_dec_ref(v_arg_1504_);
lean_dec_ref(v_e_1488_);
return v___x_1520_;
}
}
}
}
}
}
}
v___jp_1499_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1500_, 0, v___x_1487_);
lean_ctor_set_uint8(v___x_1500_, 1, v___x_1487_);
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
return v___x_1501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___boxed(lean_object* v___x_1654_, lean_object* v_e_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
uint8_t v___x_14898__boxed_1666_; lean_object* v_res_1667_; 
v___x_14898__boxed_1666_ = lean_unbox(v___x_1654_);
v_res_1667_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1(v___x_14898__boxed_1666_, v_e_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv(lean_object* v_e_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v_numArgs_1679_; lean_object* v___x_1680_; uint8_t v___x_1681_; 
v_numArgs_1679_ = l_Lean_Expr_getAppNumArgs(v_e_1668_);
v___x_1680_ = lean_unsigned_to_nat(5u);
v___x_1681_ = lean_nat_dec_lt(v_numArgs_1679_, v___x_1680_);
if (v___x_1681_ == 0)
{
lean_object* v___x_1682_; lean_object* v___f_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1682_ = lean_box(v___x_1681_);
v___f_1683_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___boxed), 12, 1);
lean_closure_set(v___f_1683_, 0, v___x_1682_);
v___x_1684_ = lean_nat_sub(v_numArgs_1679_, v___x_1680_);
lean_dec(v_numArgs_1679_);
v___x_1685_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_1668_, v___x_1684_, v___f_1683_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_);
lean_dec(v___x_1684_);
return v___x_1685_;
}
else
{
uint8_t v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
lean_dec(v_numArgs_1679_);
lean_dec_ref(v_e_1668_);
v___x_1686_ = 0;
v___x_1687_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1687_, 0, v___x_1681_);
lean_ctor_set_uint8(v___x_1687_, 1, v___x_1686_);
v___x_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
return v___x_1688_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed(lean_object* v_e_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv(v_e_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
lean_dec(v_a_1692_);
lean_dec_ref(v_a_1691_);
lean_dec(v_a_1690_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(lean_object* v_f_1701_, lean_object* v_a_u2081_1702_, lean_object* v_a_u2082_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg(v_f_1701_, v_a_u2081_1702_, v_a_u2082_1703_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___boxed(lean_object* v_f_1715_, lean_object* v_a_u2081_1716_, lean_object* v_a_u2082_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(v_f_1715_, v_a_u2081_1716_, v_a_u2082_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_));
v___x_1787_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_));
v___x_1788_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed), 11, 0);
v___x_1789_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_1786_, v___x_1787_, v___x_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17____boxed(lean_object* v_a_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_();
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1793_; uint8_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1793_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_17_));
v___x_1794_ = 0;
v___x_1795_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed), 11, 0);
v___x_1796_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_1793_, v___x_1794_, v___x_1795_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_19____boxed(lean_object* v_a_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2649134028____hygCtx___hyg_19_();
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(lean_object* v_f_1809_, lean_object* v_00_u03b1_1810_, lean_object* v_c_1811_, lean_object* v_inst_1812_, lean_object* v_a_1813_, lean_object* v_b_1814_, lean_object* v_instToMatch_1815_, lean_object* v_fallback_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_instToMatch_1815_, v_a_1823_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1829_; uint8_t v___x_1830_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_a_1828_);
lean_dec_ref_known(v___x_1827_, 1);
v___x_1829_ = l_Lean_Expr_cleanupAnnotations(v_a_1828_);
v___x_1830_ = l_Lean_Expr_isApp(v___x_1829_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; 
lean_dec_ref(v___x_1829_);
lean_dec_ref(v_b_1814_);
lean_dec_ref(v_a_1813_);
lean_dec_ref(v_inst_1812_);
lean_dec_ref(v_c_1811_);
lean_dec_ref(v_00_u03b1_1810_);
lean_inc(v_a_1825_);
lean_inc_ref(v_a_1824_);
lean_inc(v_a_1823_);
lean_inc_ref(v_a_1822_);
lean_inc(v_a_1821_);
lean_inc_ref(v_a_1820_);
lean_inc(v_a_1819_);
lean_inc_ref(v_a_1818_);
lean_inc(v_a_1817_);
v___x_1831_ = lean_apply_10(v_fallback_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, lean_box(0));
return v___x_1831_;
}
else
{
lean_object* v_arg_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v_arg_1832_ = lean_ctor_get(v___x_1829_, 1);
lean_inc_ref(v_arg_1832_);
v___x_1833_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1829_);
v___x_1834_ = l_Lean_Expr_isApp(v___x_1833_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; 
lean_dec_ref(v___x_1833_);
lean_dec_ref(v_arg_1832_);
lean_dec_ref(v_b_1814_);
lean_dec_ref(v_a_1813_);
lean_dec_ref(v_inst_1812_);
lean_dec_ref(v_c_1811_);
lean_dec_ref(v_00_u03b1_1810_);
lean_inc(v_a_1825_);
lean_inc_ref(v_a_1824_);
lean_inc(v_a_1823_);
lean_inc_ref(v_a_1822_);
lean_inc(v_a_1821_);
lean_inc_ref(v_a_1820_);
lean_inc(v_a_1819_);
lean_inc_ref(v_a_1818_);
lean_inc(v_a_1817_);
v___x_1835_ = lean_apply_10(v_fallback_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, lean_box(0));
return v___x_1835_;
}
else
{
lean_object* v_arg_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; 
v_arg_1836_ = lean_ctor_get(v___x_1833_, 1);
lean_inc_ref(v_arg_1836_);
v___x_1837_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1833_);
v___x_1838_ = l_Lean_Expr_isApp(v___x_1837_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; 
lean_dec_ref(v___x_1837_);
lean_dec_ref(v_arg_1836_);
lean_dec_ref(v_arg_1832_);
lean_dec_ref(v_b_1814_);
lean_dec_ref(v_a_1813_);
lean_dec_ref(v_inst_1812_);
lean_dec_ref(v_c_1811_);
lean_dec_ref(v_00_u03b1_1810_);
lean_inc(v_a_1825_);
lean_inc_ref(v_a_1824_);
lean_inc(v_a_1823_);
lean_inc_ref(v_a_1822_);
lean_inc(v_a_1821_);
lean_inc_ref(v_a_1820_);
lean_inc(v_a_1819_);
lean_inc_ref(v_a_1818_);
lean_inc(v_a_1817_);
v___x_1839_ = lean_apply_10(v_fallback_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, lean_box(0));
return v___x_1839_;
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1840_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1837_);
v___x_1841_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_1842_ = l_Lean_Expr_isConstOf(v___x_1840_, v___x_1841_);
lean_dec_ref(v___x_1840_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; 
lean_dec_ref(v_arg_1836_);
lean_dec_ref(v_arg_1832_);
lean_dec_ref(v_b_1814_);
lean_dec_ref(v_a_1813_);
lean_dec_ref(v_inst_1812_);
lean_dec_ref(v_c_1811_);
lean_dec_ref(v_00_u03b1_1810_);
lean_inc(v_a_1825_);
lean_inc_ref(v_a_1824_);
lean_inc(v_a_1823_);
lean_inc_ref(v_a_1822_);
lean_inc(v_a_1821_);
lean_inc_ref(v_a_1820_);
lean_inc(v_a_1819_);
lean_inc_ref(v_a_1818_);
lean_inc(v_a_1817_);
v___x_1843_ = lean_apply_10(v_fallback_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, lean_box(0));
return v___x_1843_;
}
else
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1836_, v_a_1823_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref_known(v___x_1844_, 1);
v___x_1846_ = l_Lean_Expr_cleanupAnnotations(v_a_1845_);
v___x_1847_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_1848_ = l_Lean_Expr_isConstOf(v___x_1846_, v___x_1847_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; uint8_t v___x_1850_; 
v___x_1849_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_1850_ = l_Lean_Expr_isConstOf(v___x_1846_, v___x_1849_);
lean_dec_ref(v___x_1846_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; 
lean_dec_ref(v_arg_1832_);
lean_dec_ref(v_b_1814_);
lean_dec_ref(v_a_1813_);
lean_dec_ref(v_inst_1812_);
lean_dec_ref(v_c_1811_);
lean_dec_ref(v_00_u03b1_1810_);
lean_inc(v_a_1825_);
lean_inc_ref(v_a_1824_);
lean_inc(v_a_1823_);
lean_inc_ref(v_a_1822_);
lean_inc(v_a_1821_);
lean_inc_ref(v_a_1820_);
lean_inc(v_a_1819_);
lean_inc_ref(v_a_1818_);
lean_inc(v_a_1817_);
v___x_1851_ = lean_apply_10(v_fallback_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_, lean_box(0));
return v___x_1851_;
}
else
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_dec_ref(v_fallback_1816_);
v___x_1852_ = lean_unsigned_to_nat(1u);
v___x_1853_ = lean_mk_empty_array_with_capacity(v___x_1852_);
lean_inc_ref(v_arg_1832_);
v___x_1854_ = lean_array_push(v___x_1853_, v_arg_1832_);
lean_inc_ref(v_a_1813_);
v___x_1855_ = l_Lean_Expr_betaRev(v_a_1813_, v___x_1854_, v___x_1848_, v___x_1848_);
lean_dec_ref(v___x_1854_);
v___x_1856_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1855_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1869_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1859_ = v___x_1856_;
v_isShared_1860_ = v_isSharedCheck_1869_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1856_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1869_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1861_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1));
v___x_1862_ = l_Lean_Expr_constLevels_x21(v_f_1809_);
v___x_1863_ = l_Lean_mkConst(v___x_1861_, v___x_1862_);
v___x_1864_ = l_Lean_mkApp6(v___x_1863_, v_00_u03b1_1810_, v_c_1811_, v_inst_1812_, v_a_1813_, v_b_1814_, v_arg_1832_);
v___x_1865_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1865_, 0, v_a_1857_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
lean_ctor_set_uint8(v___x_1865_, sizeof(void*)*2, v___x_1848_);
lean_ctor_set_uint8(v___x_1865_, sizeof(void*)*2 + 1, v___x_1848_);
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1865_);
v___x_1867_ = v___x_1859_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
else
{
lean_object* v_a_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec_ref(v_arg_1832_);
lean_dec_ref(v_b_1814_);
lean_dec_ref(v_a_1813_);
lean_dec_ref(v_inst_1812_);
lean_dec_ref(v_c_1811_);
lean_dec_ref(v_00_u03b1_1810_);
v_a_1870_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1856_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_a_1870_);
lean_dec(v___x_1856_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
else
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_dec_ref(v___x_1846_);
lean_dec_ref(v_fallback_1816_);
v___x_1878_ = lean_unsigned_to_nat(1u);
v___x_1879_ = lean_mk_empty_array_with_capacity(v___x_1878_);
lean_inc_ref(v_arg_1832_);
v___x_1880_ = lean_array_push(v___x_1879_, v_arg_1832_);
v___x_1881_ = 0;
lean_inc_ref(v_b_1814_);
v___x_1882_ = l_Lean_Expr_betaRev(v_b_1814_, v___x_1880_, v___x_1881_, v___x_1881_);
lean_dec_ref(v___x_1880_);
v___x_1883_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1882_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1825_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1896_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1886_ = v___x_1883_;
v_isShared_1887_ = v_isSharedCheck_1896_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1896_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1894_; 
v___x_1888_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3));
v___x_1889_ = l_Lean_Expr_constLevels_x21(v_f_1809_);
v___x_1890_ = l_Lean_mkConst(v___x_1888_, v___x_1889_);
v___x_1891_ = l_Lean_mkApp6(v___x_1890_, v_00_u03b1_1810_, v_c_1811_, v_inst_1812_, v_a_1813_, v_b_1814_, v_arg_1832_);
v___x_1892_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1892_, 0, v_a_1884_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*2, v___x_1881_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*2 + 1, v___x_1881_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1892_);
v___x_1894_ = v___x_1886_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec_ref(v_arg_1832_);
lean_dec_ref(v_b_1814_);
lean_dec_ref(v_a_1813_);
lean_dec_ref(v_inst_1812_);
lean_dec_ref(v_c_1811_);
lean_dec_ref(v_00_u03b1_1810_);
v_a_1897_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1883_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1883_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
}
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec_ref(v_arg_1832_);
lean_dec_ref(v_fallback_1816_);
lean_dec_ref(v_b_1814_);
lean_dec_ref(v_a_1813_);
lean_dec_ref(v_inst_1812_);
lean_dec_ref(v_c_1811_);
lean_dec_ref(v_00_u03b1_1810_);
v_a_1905_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1844_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1844_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_a_1905_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
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
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec_ref(v_fallback_1816_);
lean_dec_ref(v_b_1814_);
lean_dec_ref(v_a_1813_);
lean_dec_ref(v_inst_1812_);
lean_dec_ref(v_c_1811_);
lean_dec_ref(v_00_u03b1_1810_);
v_a_1913_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1827_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1827_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___boxed(lean_object** _args){
lean_object* v_f_1921_ = _args[0];
lean_object* v_00_u03b1_1922_ = _args[1];
lean_object* v_c_1923_ = _args[2];
lean_object* v_inst_1924_ = _args[3];
lean_object* v_a_1925_ = _args[4];
lean_object* v_b_1926_ = _args[5];
lean_object* v_instToMatch_1927_ = _args[6];
lean_object* v_fallback_1928_ = _args[7];
lean_object* v_a_1929_ = _args[8];
lean_object* v_a_1930_ = _args[9];
lean_object* v_a_1931_ = _args[10];
lean_object* v_a_1932_ = _args[11];
lean_object* v_a_1933_ = _args[12];
lean_object* v_a_1934_ = _args[13];
lean_object* v_a_1935_ = _args[14];
lean_object* v_a_1936_ = _args[15];
lean_object* v_a_1937_ = _args[16];
lean_object* v_a_1938_ = _args[17];
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_1921_, v_00_u03b1_1922_, v_c_1923_, v_inst_1924_, v_a_1925_, v_b_1926_, v_instToMatch_1927_, v_fallback_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_);
lean_dec(v_a_1937_);
lean_dec_ref(v_a_1936_);
lean_dec(v_a_1935_);
lean_dec_ref(v_a_1934_);
lean_dec(v_a_1933_);
lean_dec_ref(v_a_1932_);
lean_dec(v_a_1931_);
lean_dec_ref(v_a_1930_);
lean_dec(v_a_1929_);
lean_dec_ref(v_f_1921_);
return v_res_1939_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2(void){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1944_ = lean_box(0);
v___x_1945_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__1));
v___x_1946_ = l_Lean_mkConst(v___x_1945_, v___x_1944_);
return v___x_1946_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7(void){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1956_ = lean_box(0);
v___x_1957_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__6));
v___x_1958_ = l_Lean_mkConst(v___x_1957_, v___x_1956_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(lean_object* v_f_1964_, lean_object* v_00_u03b1_1965_, lean_object* v_c_1966_, lean_object* v_inst_1967_, lean_object* v_a_1968_, lean_object* v_b_1969_, lean_object* v_c_x27_1970_, lean_object* v_h_1971_, lean_object* v_inst_x27_1972_, lean_object* v_fallback_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_x27_1972_, v_a_1980_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1984_, 1);
v___x_1986_ = l_Lean_Expr_cleanupAnnotations(v_a_1985_);
v___x_1987_ = l_Lean_Expr_isApp(v___x_1986_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; 
lean_dec_ref(v___x_1986_);
lean_dec_ref(v_h_1971_);
lean_dec_ref(v_c_x27_1970_);
lean_dec_ref(v_b_1969_);
lean_dec_ref(v_a_1968_);
lean_dec_ref(v_inst_1967_);
lean_dec_ref(v_c_1966_);
lean_dec_ref(v_00_u03b1_1965_);
lean_inc(v_a_1982_);
lean_inc_ref(v_a_1981_);
lean_inc(v_a_1980_);
lean_inc_ref(v_a_1979_);
lean_inc(v_a_1978_);
lean_inc_ref(v_a_1977_);
lean_inc(v_a_1976_);
lean_inc_ref(v_a_1975_);
lean_inc(v_a_1974_);
v___x_1988_ = lean_apply_10(v_fallback_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, lean_box(0));
return v___x_1988_;
}
else
{
lean_object* v_arg_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v_arg_1989_ = lean_ctor_get(v___x_1986_, 1);
lean_inc_ref(v_arg_1989_);
v___x_1990_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1986_);
v___x_1991_ = l_Lean_Expr_isApp(v___x_1990_);
if (v___x_1991_ == 0)
{
lean_object* v___x_1992_; 
lean_dec_ref(v___x_1990_);
lean_dec_ref(v_arg_1989_);
lean_dec_ref(v_h_1971_);
lean_dec_ref(v_c_x27_1970_);
lean_dec_ref(v_b_1969_);
lean_dec_ref(v_a_1968_);
lean_dec_ref(v_inst_1967_);
lean_dec_ref(v_c_1966_);
lean_dec_ref(v_00_u03b1_1965_);
lean_inc(v_a_1982_);
lean_inc_ref(v_a_1981_);
lean_inc(v_a_1980_);
lean_inc_ref(v_a_1979_);
lean_inc(v_a_1978_);
lean_inc_ref(v_a_1977_);
lean_inc(v_a_1976_);
lean_inc_ref(v_a_1975_);
lean_inc(v_a_1974_);
v___x_1992_ = lean_apply_10(v_fallback_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, lean_box(0));
return v___x_1992_;
}
else
{
lean_object* v_arg_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v_arg_1993_ = lean_ctor_get(v___x_1990_, 1);
lean_inc_ref(v_arg_1993_);
v___x_1994_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1990_);
v___x_1995_ = l_Lean_Expr_isApp(v___x_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; 
lean_dec_ref(v___x_1994_);
lean_dec_ref(v_arg_1993_);
lean_dec_ref(v_arg_1989_);
lean_dec_ref(v_h_1971_);
lean_dec_ref(v_c_x27_1970_);
lean_dec_ref(v_b_1969_);
lean_dec_ref(v_a_1968_);
lean_dec_ref(v_inst_1967_);
lean_dec_ref(v_c_1966_);
lean_dec_ref(v_00_u03b1_1965_);
lean_inc(v_a_1982_);
lean_inc_ref(v_a_1981_);
lean_inc(v_a_1980_);
lean_inc_ref(v_a_1979_);
lean_inc(v_a_1978_);
lean_inc_ref(v_a_1977_);
lean_inc(v_a_1976_);
lean_inc_ref(v_a_1975_);
lean_inc(v_a_1974_);
v___x_1996_ = lean_apply_10(v_fallback_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, lean_box(0));
return v___x_1996_;
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1997_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1994_);
v___x_1998_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_1999_ = l_Lean_Expr_isConstOf(v___x_1997_, v___x_1998_);
lean_dec_ref(v___x_1997_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; 
lean_dec_ref(v_arg_1993_);
lean_dec_ref(v_arg_1989_);
lean_dec_ref(v_h_1971_);
lean_dec_ref(v_c_x27_1970_);
lean_dec_ref(v_b_1969_);
lean_dec_ref(v_a_1968_);
lean_dec_ref(v_inst_1967_);
lean_dec_ref(v_c_1966_);
lean_dec_ref(v_00_u03b1_1965_);
lean_inc(v_a_1982_);
lean_inc_ref(v_a_1981_);
lean_inc(v_a_1980_);
lean_inc_ref(v_a_1979_);
lean_inc(v_a_1978_);
lean_inc_ref(v_a_1977_);
lean_inc(v_a_1976_);
lean_inc_ref(v_a_1975_);
lean_inc(v_a_1974_);
v___x_2000_ = lean_apply_10(v_fallback_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, lean_box(0));
return v___x_2000_;
}
else
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1993_, v_a_1980_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; uint8_t v___x_2005_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_2001_, 1);
v___x_2003_ = l_Lean_Expr_cleanupAnnotations(v_a_2002_);
v___x_2004_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_2005_ = l_Lean_Expr_isConstOf(v___x_2003_, v___x_2004_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; uint8_t v___x_2007_; 
v___x_2006_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_2007_ = l_Lean_Expr_isConstOf(v___x_2003_, v___x_2006_);
lean_dec_ref(v___x_2003_);
if (v___x_2007_ == 0)
{
lean_object* v___x_2008_; 
lean_dec_ref(v_arg_1989_);
lean_dec_ref(v_h_1971_);
lean_dec_ref(v_c_x27_1970_);
lean_dec_ref(v_b_1969_);
lean_dec_ref(v_a_1968_);
lean_dec_ref(v_inst_1967_);
lean_dec_ref(v_c_1966_);
lean_dec_ref(v_00_u03b1_1965_);
lean_inc(v_a_1982_);
lean_inc_ref(v_a_1981_);
lean_inc(v_a_1980_);
lean_inc_ref(v_a_1979_);
lean_inc(v_a_1978_);
lean_inc_ref(v_a_1977_);
lean_inc(v_a_1976_);
lean_inc_ref(v_a_1975_);
lean_inc(v_a_1974_);
v___x_2008_ = lean_apply_10(v_fallback_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, lean_box(0));
return v___x_2008_;
}
else
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_dec_ref(v_fallback_1973_);
v___x_2009_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2);
lean_inc_ref(v_arg_1989_);
lean_inc_ref(v_h_1971_);
lean_inc_ref(v_c_x27_1970_);
lean_inc_ref(v_c_1966_);
v___x_2010_ = l_Lean_mkApp4(v___x_2009_, v_c_1966_, v_c_x27_1970_, v_h_1971_, v_arg_1989_);
v___x_2011_ = lean_unsigned_to_nat(1u);
v___x_2012_ = lean_mk_empty_array_with_capacity(v___x_2011_);
v___x_2013_ = lean_array_push(v___x_2012_, v___x_2010_);
lean_inc_ref(v_a_1968_);
v___x_2014_ = l_Lean_Expr_betaRev(v_a_1968_, v___x_2013_, v___x_2005_, v___x_2005_);
lean_dec_ref(v___x_2013_);
v___x_2015_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2014_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2028_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2028_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2028_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2020_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4));
v___x_2021_ = l_Lean_Expr_constLevels_x21(v_f_1964_);
v___x_2022_ = l_Lean_mkConst(v___x_2020_, v___x_2021_);
v___x_2023_ = l_Lean_mkApp8(v___x_2022_, v_00_u03b1_1965_, v_c_1966_, v_inst_1967_, v_a_1968_, v_b_1969_, v_c_x27_1970_, v_h_1971_, v_arg_1989_);
v___x_2024_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2024_, 0, v_a_2016_);
lean_ctor_set(v___x_2024_, 1, v___x_2023_);
lean_ctor_set_uint8(v___x_2024_, sizeof(void*)*2, v___x_2005_);
lean_ctor_set_uint8(v___x_2024_, sizeof(void*)*2 + 1, v___x_2005_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2024_);
v___x_2026_ = v___x_2018_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
return v___x_2026_;
}
}
}
else
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec_ref(v_arg_1989_);
lean_dec_ref(v_h_1971_);
lean_dec_ref(v_c_x27_1970_);
lean_dec_ref(v_b_1969_);
lean_dec_ref(v_a_1968_);
lean_dec_ref(v_inst_1967_);
lean_dec_ref(v_c_1966_);
lean_dec_ref(v_00_u03b1_1965_);
v_a_2029_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2015_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2015_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
else
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; uint8_t v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
lean_dec_ref(v___x_2003_);
lean_dec_ref(v_fallback_1973_);
v___x_2037_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7);
lean_inc_ref(v_arg_1989_);
lean_inc_ref(v_h_1971_);
lean_inc_ref(v_c_x27_1970_);
lean_inc_ref(v_c_1966_);
v___x_2038_ = l_Lean_mkApp4(v___x_2037_, v_c_1966_, v_c_x27_1970_, v_h_1971_, v_arg_1989_);
v___x_2039_ = lean_unsigned_to_nat(1u);
v___x_2040_ = lean_mk_empty_array_with_capacity(v___x_2039_);
v___x_2041_ = lean_array_push(v___x_2040_, v___x_2038_);
v___x_2042_ = 0;
lean_inc_ref(v_b_1969_);
v___x_2043_ = l_Lean_Expr_betaRev(v_b_1969_, v___x_2041_, v___x_2042_, v___x_2042_);
lean_dec_ref(v___x_2041_);
v___x_2044_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2043_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2057_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2047_ = v___x_2044_;
v_isShared_2048_ = v_isSharedCheck_2057_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2044_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2057_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2049_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9));
v___x_2050_ = l_Lean_Expr_constLevels_x21(v_f_1964_);
v___x_2051_ = l_Lean_mkConst(v___x_2049_, v___x_2050_);
v___x_2052_ = l_Lean_mkApp8(v___x_2051_, v_00_u03b1_1965_, v_c_1966_, v_inst_1967_, v_a_1968_, v_b_1969_, v_c_x27_1970_, v_h_1971_, v_arg_1989_);
v___x_2053_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2053_, 0, v_a_2045_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
lean_ctor_set_uint8(v___x_2053_, sizeof(void*)*2, v___x_2042_);
lean_ctor_set_uint8(v___x_2053_, sizeof(void*)*2 + 1, v___x_2042_);
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 0, v___x_2053_);
v___x_2055_ = v___x_2047_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec_ref(v_arg_1989_);
lean_dec_ref(v_h_1971_);
lean_dec_ref(v_c_x27_1970_);
lean_dec_ref(v_b_1969_);
lean_dec_ref(v_a_1968_);
lean_dec_ref(v_inst_1967_);
lean_dec_ref(v_c_1966_);
lean_dec_ref(v_00_u03b1_1965_);
v_a_2058_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2044_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2044_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec_ref(v_arg_1989_);
lean_dec_ref(v_fallback_1973_);
lean_dec_ref(v_h_1971_);
lean_dec_ref(v_c_x27_1970_);
lean_dec_ref(v_b_1969_);
lean_dec_ref(v_a_1968_);
lean_dec_ref(v_inst_1967_);
lean_dec_ref(v_c_1966_);
lean_dec_ref(v_00_u03b1_1965_);
v_a_2066_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2001_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2001_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
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
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec_ref(v_fallback_1973_);
lean_dec_ref(v_h_1971_);
lean_dec_ref(v_c_x27_1970_);
lean_dec_ref(v_b_1969_);
lean_dec_ref(v_a_1968_);
lean_dec_ref(v_inst_1967_);
lean_dec_ref(v_c_1966_);
lean_dec_ref(v_00_u03b1_1965_);
v_a_2074_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_1984_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_1984_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_2082_ = _args[0];
lean_object* v_00_u03b1_2083_ = _args[1];
lean_object* v_c_2084_ = _args[2];
lean_object* v_inst_2085_ = _args[3];
lean_object* v_a_2086_ = _args[4];
lean_object* v_b_2087_ = _args[5];
lean_object* v_c_x27_2088_ = _args[6];
lean_object* v_h_2089_ = _args[7];
lean_object* v_inst_x27_2090_ = _args[8];
lean_object* v_fallback_2091_ = _args[9];
lean_object* v_a_2092_ = _args[10];
lean_object* v_a_2093_ = _args[11];
lean_object* v_a_2094_ = _args[12];
lean_object* v_a_2095_ = _args[13];
lean_object* v_a_2096_ = _args[14];
lean_object* v_a_2097_ = _args[15];
lean_object* v_a_2098_ = _args[16];
lean_object* v_a_2099_ = _args[17];
lean_object* v_a_2100_ = _args[18];
lean_object* v_a_2101_ = _args[19];
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(v_f_2082_, v_00_u03b1_2083_, v_c_2084_, v_inst_2085_, v_a_2086_, v_b_2087_, v_c_x27_2088_, v_h_2089_, v_inst_x27_2090_, v_fallback_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
lean_dec(v_a_2094_);
lean_dec_ref(v_a_2093_);
lean_dec(v_a_2092_);
lean_dec_ref(v_f_2082_);
return v_res_2102_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2(void){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2106_ = lean_box(0);
v___x_2107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__1));
v___x_2108_ = l_Lean_mkConst(v___x_2107_, v___x_2106_);
return v___x_2108_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = lean_box(0);
v___x_2113_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__4));
v___x_2114_ = l_Lean_mkConst(v___x_2113_, v___x_2112_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(lean_object* v_f_2115_, lean_object* v_00_u03b1_2116_, lean_object* v_c_2117_, lean_object* v_inst_2118_, lean_object* v_a_2119_, lean_object* v_b_2120_, lean_object* v_fallback_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v___x_2132_; uint8_t v___x_2133_; lean_object* v___x_2134_; lean_object* v___f_2135_; lean_object* v___x_2136_; 
v___x_2132_ = lean_unsigned_to_nat(0u);
v___x_2133_ = 5;
v___x_2134_ = lean_box(v___x_2133_);
lean_inc_ref(v_inst_2118_);
v___f_2135_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2135_, 0, v___x_2134_);
lean_closure_set(v___f_2135_, 1, v_inst_2118_);
lean_closure_set(v___f_2135_, 2, v___x_2132_);
v___x_2136_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2135_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
if (lean_obj_tag(v_a_2137_) == 0)
{
lean_object* v___x_2138_; 
lean_inc(v_a_2130_);
lean_inc_ref(v_a_2129_);
lean_inc(v_a_2128_);
lean_inc_ref(v_a_2127_);
lean_inc(v_a_2126_);
lean_inc_ref(v_a_2125_);
lean_inc(v_a_2124_);
lean_inc_ref(v_a_2123_);
lean_inc(v_a_2122_);
lean_inc_ref(v_inst_2118_);
v___x_2138_ = lean_sym_simp(v_inst_2118_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref_known(v___x_2138_, 1);
if (lean_obj_tag(v_a_2139_) == 0)
{
uint8_t v_contextDependent_2140_; lean_object* v___x_2141_; 
v_contextDependent_2140_ = lean_ctor_get_uint8(v_a_2139_, 1);
lean_dec_ref_known(v_a_2139_, 0);
lean_inc_ref(v_inst_2118_);
v___x_2141_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_2115_, v_00_u03b1_2116_, v_c_2117_, v_inst_2118_, v_a_2119_, v_b_2120_, v_inst_2118_, v_fallback_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; uint8_t v___y_2144_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
if (v_contextDependent_2140_ == 0)
{
lean_dec(v_a_2142_);
return v___x_2141_;
}
else
{
if (lean_obj_tag(v_a_2142_) == 0)
{
uint8_t v_contextDependent_2154_; 
v_contextDependent_2154_ = lean_ctor_get_uint8(v_a_2142_, 1);
v___y_2144_ = v_contextDependent_2154_;
goto v___jp_2143_;
}
else
{
uint8_t v_contextDependent_2155_; 
v_contextDependent_2155_ = lean_ctor_get_uint8(v_a_2142_, sizeof(void*)*2 + 1);
v___y_2144_ = v_contextDependent_2155_;
goto v___jp_2143_;
}
}
v___jp_2143_:
{
if (v___y_2144_ == 0)
{
lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2152_; 
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2152_ == 0)
{
lean_object* v_unused_2153_; 
v_unused_2153_ = lean_ctor_get(v___x_2141_, 0);
lean_dec(v_unused_2153_);
v___x_2146_ = v___x_2141_;
v_isShared_2147_ = v_isSharedCheck_2152_;
goto v_resetjp_2145_;
}
else
{
lean_dec(v___x_2141_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2152_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2148_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2142_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2148_);
v___x_2150_ = v___x_2146_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
else
{
lean_dec(v_a_2142_);
return v___x_2141_;
}
}
}
else
{
return v___x_2141_;
}
}
else
{
lean_object* v_e_x27_2156_; uint8_t v_contextDependent_2157_; lean_object* v___x_2158_; 
v_e_x27_2156_ = lean_ctor_get(v_a_2139_, 0);
lean_inc_ref(v_e_x27_2156_);
v_contextDependent_2157_ = lean_ctor_get_uint8(v_a_2139_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2139_, 2);
v___x_2158_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_2115_, v_00_u03b1_2116_, v_c_2117_, v_inst_2118_, v_a_2119_, v_b_2120_, v_e_x27_2156_, v_fallback_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; uint8_t v___y_2161_; 
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2159_);
if (v_contextDependent_2157_ == 0)
{
lean_dec(v_a_2159_);
return v___x_2158_;
}
else
{
if (lean_obj_tag(v_a_2159_) == 0)
{
uint8_t v_contextDependent_2171_; 
v_contextDependent_2171_ = lean_ctor_get_uint8(v_a_2159_, 1);
v___y_2161_ = v_contextDependent_2171_;
goto v___jp_2160_;
}
else
{
uint8_t v_contextDependent_2172_; 
v_contextDependent_2172_ = lean_ctor_get_uint8(v_a_2159_, sizeof(void*)*2 + 1);
v___y_2161_ = v_contextDependent_2172_;
goto v___jp_2160_;
}
}
v___jp_2160_:
{
if (v___y_2161_ == 0)
{
lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2169_; 
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2169_ == 0)
{
lean_object* v_unused_2170_; 
v_unused_2170_ = lean_ctor_get(v___x_2158_, 0);
lean_dec(v_unused_2170_);
v___x_2163_ = v___x_2158_;
v_isShared_2164_ = v_isSharedCheck_2169_;
goto v_resetjp_2162_;
}
else
{
lean_dec(v___x_2158_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2169_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
v___x_2165_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2159_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2165_);
v___x_2167_ = v___x_2163_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
else
{
lean_dec(v_a_2159_);
return v___x_2158_;
}
}
}
else
{
return v___x_2158_;
}
}
}
else
{
lean_dec_ref(v_fallback_2121_);
lean_dec_ref(v_b_2120_);
lean_dec_ref(v_a_2119_);
lean_dec_ref(v_inst_2118_);
lean_dec_ref(v_c_2117_);
lean_dec_ref(v_00_u03b1_2116_);
return v___x_2138_;
}
}
else
{
lean_object* v_val_2173_; lean_object* v___x_2174_; 
v_val_2173_ = lean_ctor_get(v_a_2137_, 0);
lean_inc(v_val_2173_);
lean_dec_ref_known(v_a_2137_, 1);
v___x_2174_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2173_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc_n(v_a_2175_, 3);
lean_dec_ref_known(v___x_2174_, 1);
v___x_2176_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2);
v___x_2177_ = lean_unsigned_to_nat(1u);
v___x_2178_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8);
v___x_2179_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10);
v___x_2180_ = l_Lean_mkAppB(v___x_2178_, v___x_2179_, v_a_2175_);
lean_inc(v_a_2130_);
lean_inc_ref(v_a_2129_);
lean_inc(v_a_2128_);
lean_inc_ref(v_a_2127_);
lean_inc(v_a_2126_);
lean_inc_ref(v_a_2125_);
lean_inc(v_a_2124_);
lean_inc_ref(v_a_2123_);
lean_inc(v_a_2122_);
v___x_2181_ = lean_sym_simp(v_a_2175_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; uint8_t v___x_2183_; lean_object* v_e_x27_2185_; lean_object* v_proof_2186_; uint8_t v_contextDependent_2187_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
lean_dec_ref_known(v___x_2181_, 1);
v___x_2183_ = 0;
if (lean_obj_tag(v_a_2182_) == 0)
{
uint8_t v_contextDependent_2278_; 
v_contextDependent_2278_ = lean_ctor_get_uint8(v_a_2182_, 1);
lean_dec_ref_known(v_a_2182_, 0);
v_e_x27_2185_ = v_a_2175_;
v_proof_2186_ = v___x_2180_;
v_contextDependent_2187_ = v_contextDependent_2278_;
goto v___jp_2184_;
}
else
{
lean_object* v_e_x27_2279_; lean_object* v_proof_2280_; uint8_t v_contextDependent_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v_e_x27_2279_ = lean_ctor_get(v_a_2182_, 0);
lean_inc_ref_n(v_e_x27_2279_, 2);
v_proof_2280_ = lean_ctor_get(v_a_2182_, 1);
lean_inc_ref(v_proof_2280_);
v_contextDependent_2281_ = lean_ctor_get_uint8(v_a_2182_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2182_, 2);
lean_inc_ref(v_inst_2118_);
lean_inc_ref(v_c_2117_);
v___x_2282_ = l_Lean_mkAppB(v___x_2176_, v_c_2117_, v_inst_2118_);
v___x_2283_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___x_2282_, v_a_2175_, v___x_2180_, v_e_x27_2279_, v_proof_2280_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2284_);
lean_dec_ref_known(v___x_2283_, 1);
v_e_x27_2185_ = v_e_x27_2279_;
v_proof_2186_ = v_a_2284_;
v_contextDependent_2187_ = v_contextDependent_2281_;
goto v___jp_2184_;
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_dec_ref(v_e_x27_2279_);
lean_dec_ref(v_fallback_2121_);
lean_dec_ref(v_b_2120_);
lean_dec_ref(v_a_2119_);
lean_dec_ref(v_inst_2118_);
lean_dec_ref(v_c_2117_);
lean_dec_ref(v_00_u03b1_2116_);
v_a_2285_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2283_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2283_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
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
v___jp_2184_:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_x27_2185_, v_a_2128_);
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
lean_dec_ref_known(v___x_2188_, 1);
v___x_2190_ = l_Lean_Expr_cleanupAnnotations(v_a_2189_);
v___x_2191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_2192_ = l_Lean_Expr_isConstOf(v___x_2190_, v___x_2191_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2193_; uint8_t v___x_2194_; 
v___x_2193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_2194_ = l_Lean_Expr_isConstOf(v___x_2190_, v___x_2193_);
lean_dec_ref(v___x_2190_);
if (v___x_2194_ == 0)
{
lean_object* v___x_2195_; 
lean_dec_ref(v_proof_2186_);
lean_dec_ref(v_b_2120_);
lean_dec_ref(v_a_2119_);
lean_dec_ref(v_inst_2118_);
lean_dec_ref(v_c_2117_);
lean_dec_ref(v_00_u03b1_2116_);
lean_inc(v_a_2130_);
lean_inc_ref(v_a_2129_);
lean_inc(v_a_2128_);
lean_inc_ref(v_a_2127_);
lean_inc(v_a_2126_);
lean_inc_ref(v_a_2125_);
lean_inc(v_a_2124_);
lean_inc_ref(v_a_2123_);
lean_inc(v_a_2122_);
v___x_2195_ = lean_apply_10(v_fallback_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, lean_box(0));
return v___x_2195_;
}
else
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
lean_dec_ref(v_fallback_2121_);
v___x_2196_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2);
lean_inc_ref(v_inst_2118_);
lean_inc_ref(v_c_2117_);
v___x_2197_ = l_Lean_mkApp3(v___x_2196_, v_c_2117_, v_inst_2118_, v_proof_2186_);
v___x_2198_ = l_Lean_Meta_Sym_shareCommon(v___x_2197_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc_n(v_a_2199_, 2);
lean_dec_ref_known(v___x_2198_, 1);
v___x_2200_ = lean_mk_empty_array_with_capacity(v___x_2177_);
v___x_2201_ = lean_array_push(v___x_2200_, v_a_2199_);
lean_inc_ref(v_a_2119_);
v___x_2202_ = l_Lean_Expr_betaRev(v_a_2119_, v___x_2201_, v___x_2183_, v___x_2183_);
lean_dec_ref(v___x_2201_);
v___x_2203_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2202_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2216_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2216_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2216_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1));
v___x_2209_ = l_Lean_Expr_constLevels_x21(v_f_2115_);
v___x_2210_ = l_Lean_mkConst(v___x_2208_, v___x_2209_);
v___x_2211_ = l_Lean_mkApp6(v___x_2210_, v_00_u03b1_2116_, v_c_2117_, v_inst_2118_, v_a_2119_, v_b_2120_, v_a_2199_);
v___x_2212_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2212_, 0, v_a_2204_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
lean_ctor_set_uint8(v___x_2212_, sizeof(void*)*2, v___x_2183_);
lean_ctor_set_uint8(v___x_2212_, sizeof(void*)*2 + 1, v_contextDependent_2187_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2212_);
v___x_2214_ = v___x_2206_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec(v_a_2199_);
lean_dec_ref(v_b_2120_);
lean_dec_ref(v_a_2119_);
lean_dec_ref(v_inst_2118_);
lean_dec_ref(v_c_2117_);
lean_dec_ref(v_00_u03b1_2116_);
v_a_2217_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2203_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2203_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec_ref(v_b_2120_);
lean_dec_ref(v_a_2119_);
lean_dec_ref(v_inst_2118_);
lean_dec_ref(v_c_2117_);
lean_dec_ref(v_00_u03b1_2116_);
v_a_2225_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2198_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2198_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
}
else
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
lean_dec_ref(v___x_2190_);
lean_dec_ref(v_fallback_2121_);
v___x_2233_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5);
lean_inc_ref(v_inst_2118_);
lean_inc_ref(v_c_2117_);
v___x_2234_ = l_Lean_mkApp3(v___x_2233_, v_c_2117_, v_inst_2118_, v_proof_2186_);
v___x_2235_ = l_Lean_Meta_Sym_shareCommon(v___x_2234_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc_n(v_a_2236_, 2);
lean_dec_ref_known(v___x_2235_, 1);
v___x_2237_ = lean_mk_empty_array_with_capacity(v___x_2177_);
v___x_2238_ = lean_array_push(v___x_2237_, v_a_2236_);
lean_inc_ref(v_b_2120_);
v___x_2239_ = l_Lean_Expr_betaRev(v_b_2120_, v___x_2238_, v___x_2183_, v___x_2183_);
lean_dec_ref(v___x_2238_);
v___x_2240_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2239_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2253_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2253_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2253_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2251_; 
v___x_2245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3));
v___x_2246_ = l_Lean_Expr_constLevels_x21(v_f_2115_);
v___x_2247_ = l_Lean_mkConst(v___x_2245_, v___x_2246_);
v___x_2248_ = l_Lean_mkApp6(v___x_2247_, v_00_u03b1_2116_, v_c_2117_, v_inst_2118_, v_a_2119_, v_b_2120_, v_a_2236_);
v___x_2249_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2249_, 0, v_a_2241_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
lean_ctor_set_uint8(v___x_2249_, sizeof(void*)*2, v___x_2183_);
lean_ctor_set_uint8(v___x_2249_, sizeof(void*)*2 + 1, v_contextDependent_2187_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v___x_2249_);
v___x_2251_ = v___x_2243_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
lean_dec(v_a_2236_);
lean_dec_ref(v_b_2120_);
lean_dec_ref(v_a_2119_);
lean_dec_ref(v_inst_2118_);
lean_dec_ref(v_c_2117_);
lean_dec_ref(v_00_u03b1_2116_);
v_a_2254_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2240_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2240_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_dec_ref(v_b_2120_);
lean_dec_ref(v_a_2119_);
lean_dec_ref(v_inst_2118_);
lean_dec_ref(v_c_2117_);
lean_dec_ref(v_00_u03b1_2116_);
v_a_2262_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2235_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2235_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec_ref(v_proof_2186_);
lean_dec_ref(v_fallback_2121_);
lean_dec_ref(v_b_2120_);
lean_dec_ref(v_a_2119_);
lean_dec_ref(v_inst_2118_);
lean_dec_ref(v_c_2117_);
lean_dec_ref(v_00_u03b1_2116_);
v_a_2270_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2188_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2188_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2180_);
lean_dec(v_a_2175_);
lean_dec_ref(v_fallback_2121_);
lean_dec_ref(v_b_2120_);
lean_dec_ref(v_a_2119_);
lean_dec_ref(v_inst_2118_);
lean_dec_ref(v_c_2117_);
lean_dec_ref(v_00_u03b1_2116_);
return v___x_2181_;
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_dec_ref(v_fallback_2121_);
lean_dec_ref(v_b_2120_);
lean_dec_ref(v_a_2119_);
lean_dec_ref(v_inst_2118_);
lean_dec_ref(v_c_2117_);
lean_dec_ref(v_00_u03b1_2116_);
v_a_2293_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2174_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2174_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
lean_dec_ref(v_fallback_2121_);
lean_dec_ref(v_b_2120_);
lean_dec_ref(v_a_2119_);
lean_dec_ref(v_inst_2118_);
lean_dec_ref(v_c_2117_);
lean_dec_ref(v_00_u03b1_2116_);
v_a_2301_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2136_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2136_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___boxed(lean_object** _args){
lean_object* v_f_2309_ = _args[0];
lean_object* v_00_u03b1_2310_ = _args[1];
lean_object* v_c_2311_ = _args[2];
lean_object* v_inst_2312_ = _args[3];
lean_object* v_a_2313_ = _args[4];
lean_object* v_b_2314_ = _args[5];
lean_object* v_fallback_2315_ = _args[6];
lean_object* v_a_2316_ = _args[7];
lean_object* v_a_2317_ = _args[8];
lean_object* v_a_2318_ = _args[9];
lean_object* v_a_2319_ = _args[10];
lean_object* v_a_2320_ = _args[11];
lean_object* v_a_2321_ = _args[12];
lean_object* v_a_2322_ = _args[13];
lean_object* v_a_2323_ = _args[14];
lean_object* v_a_2324_ = _args[15];
lean_object* v_a_2325_ = _args[16];
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v_f_2309_, v_00_u03b1_2310_, v_c_2311_, v_inst_2312_, v_a_2313_, v_b_2314_, v_fallback_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
lean_dec(v_a_2322_);
lean_dec_ref(v_a_2321_);
lean_dec(v_a_2320_);
lean_dec_ref(v_a_2319_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_f_2309_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr(lean_object* v_f_2327_, lean_object* v_00_u03b1_2328_, lean_object* v_c_2329_, lean_object* v_inst_2330_, lean_object* v_a_2331_, lean_object* v_b_2332_, lean_object* v_c_x27_2333_, lean_object* v_h_2334_, lean_object* v_inst_x27_2335_, lean_object* v_fallback_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v___x_2347_; uint8_t v___x_2348_; lean_object* v___x_2349_; lean_object* v___f_2350_; lean_object* v___x_2351_; 
v___x_2347_ = lean_unsigned_to_nat(0u);
v___x_2348_ = 5;
v___x_2349_ = lean_box(v___x_2348_);
lean_inc_ref(v_inst_x27_2335_);
v___f_2350_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2350_, 0, v___x_2349_);
lean_closure_set(v___f_2350_, 1, v_inst_x27_2335_);
lean_closure_set(v___f_2350_, 2, v___x_2347_);
v___x_2351_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2350_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_a_2352_);
lean_dec_ref_known(v___x_2351_, 1);
if (lean_obj_tag(v_a_2352_) == 0)
{
lean_object* v___x_2353_; 
lean_inc(v_a_2345_);
lean_inc_ref(v_a_2344_);
lean_inc(v_a_2343_);
lean_inc_ref(v_a_2342_);
lean_inc(v_a_2341_);
lean_inc_ref(v_a_2340_);
lean_inc(v_a_2339_);
lean_inc_ref(v_a_2338_);
lean_inc(v_a_2337_);
lean_inc_ref(v_inst_x27_2335_);
v___x_2353_ = lean_sym_simp(v_inst_x27_2335_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___x_2353_, 1);
if (lean_obj_tag(v_a_2354_) == 0)
{
uint8_t v_contextDependent_2355_; lean_object* v___x_2356_; 
v_contextDependent_2355_ = lean_ctor_get_uint8(v_a_2354_, 1);
lean_dec_ref_known(v_a_2354_, 0);
v___x_2356_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(v_f_2327_, v_00_u03b1_2328_, v_c_2329_, v_inst_2330_, v_a_2331_, v_b_2332_, v_c_x27_2333_, v_h_2334_, v_inst_x27_2335_, v_fallback_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; uint8_t v___y_2359_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_a_2357_);
if (v_contextDependent_2355_ == 0)
{
lean_dec(v_a_2357_);
return v___x_2356_;
}
else
{
if (lean_obj_tag(v_a_2357_) == 0)
{
uint8_t v_contextDependent_2369_; 
v_contextDependent_2369_ = lean_ctor_get_uint8(v_a_2357_, 1);
v___y_2359_ = v_contextDependent_2369_;
goto v___jp_2358_;
}
else
{
uint8_t v_contextDependent_2370_; 
v_contextDependent_2370_ = lean_ctor_get_uint8(v_a_2357_, sizeof(void*)*2 + 1);
v___y_2359_ = v_contextDependent_2370_;
goto v___jp_2358_;
}
}
v___jp_2358_:
{
if (v___y_2359_ == 0)
{
lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2367_; 
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2367_ == 0)
{
lean_object* v_unused_2368_; 
v_unused_2368_ = lean_ctor_get(v___x_2356_, 0);
lean_dec(v_unused_2368_);
v___x_2361_ = v___x_2356_;
v_isShared_2362_ = v_isSharedCheck_2367_;
goto v_resetjp_2360_;
}
else
{
lean_dec(v___x_2356_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2367_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2363_; lean_object* v___x_2365_; 
v___x_2363_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2357_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2363_);
v___x_2365_ = v___x_2361_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2363_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
else
{
lean_dec(v_a_2357_);
return v___x_2356_;
}
}
}
else
{
return v___x_2356_;
}
}
else
{
lean_object* v_e_x27_2371_; uint8_t v_contextDependent_2372_; lean_object* v___x_2373_; 
lean_dec_ref(v_inst_x27_2335_);
v_e_x27_2371_ = lean_ctor_get(v_a_2354_, 0);
lean_inc_ref(v_e_x27_2371_);
v_contextDependent_2372_ = lean_ctor_get_uint8(v_a_2354_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2354_, 2);
v___x_2373_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(v_f_2327_, v_00_u03b1_2328_, v_c_2329_, v_inst_2330_, v_a_2331_, v_b_2332_, v_c_x27_2333_, v_h_2334_, v_e_x27_2371_, v_fallback_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; uint8_t v___y_2376_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2374_);
if (v_contextDependent_2372_ == 0)
{
lean_dec(v_a_2374_);
return v___x_2373_;
}
else
{
if (lean_obj_tag(v_a_2374_) == 0)
{
uint8_t v_contextDependent_2386_; 
v_contextDependent_2386_ = lean_ctor_get_uint8(v_a_2374_, 1);
v___y_2376_ = v_contextDependent_2386_;
goto v___jp_2375_;
}
else
{
uint8_t v_contextDependent_2387_; 
v_contextDependent_2387_ = lean_ctor_get_uint8(v_a_2374_, sizeof(void*)*2 + 1);
v___y_2376_ = v_contextDependent_2387_;
goto v___jp_2375_;
}
}
v___jp_2375_:
{
if (v___y_2376_ == 0)
{
lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2384_; 
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2384_ == 0)
{
lean_object* v_unused_2385_; 
v_unused_2385_ = lean_ctor_get(v___x_2373_, 0);
lean_dec(v_unused_2385_);
v___x_2378_ = v___x_2373_;
v_isShared_2379_ = v_isSharedCheck_2384_;
goto v_resetjp_2377_;
}
else
{
lean_dec(v___x_2373_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2384_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2380_; lean_object* v___x_2382_; 
v___x_2380_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2374_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2380_);
v___x_2382_ = v___x_2378_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2380_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
else
{
lean_dec(v_a_2374_);
return v___x_2373_;
}
}
}
else
{
return v___x_2373_;
}
}
}
else
{
lean_dec_ref(v_fallback_2336_);
lean_dec_ref(v_inst_x27_2335_);
lean_dec_ref(v_h_2334_);
lean_dec_ref(v_c_x27_2333_);
lean_dec_ref(v_b_2332_);
lean_dec_ref(v_a_2331_);
lean_dec_ref(v_inst_2330_);
lean_dec_ref(v_c_2329_);
lean_dec_ref(v_00_u03b1_2328_);
return v___x_2353_;
}
}
else
{
lean_object* v_val_2388_; lean_object* v___x_2389_; 
v_val_2388_ = lean_ctor_get(v_a_2352_, 0);
lean_inc(v_val_2388_);
lean_dec_ref_known(v_a_2352_, 1);
v___x_2389_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2388_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc_n(v_a_2390_, 3);
lean_dec_ref_known(v___x_2389_, 1);
v___x_2391_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2);
v___x_2392_ = lean_unsigned_to_nat(1u);
v___x_2393_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8);
v___x_2394_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10);
v___x_2395_ = l_Lean_mkAppB(v___x_2393_, v___x_2394_, v_a_2390_);
lean_inc(v_a_2345_);
lean_inc_ref(v_a_2344_);
lean_inc(v_a_2343_);
lean_inc_ref(v_a_2342_);
lean_inc(v_a_2341_);
lean_inc_ref(v_a_2340_);
lean_inc(v_a_2339_);
lean_inc_ref(v_a_2338_);
lean_inc(v_a_2337_);
v___x_2396_ = lean_sym_simp(v_a_2390_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; uint8_t v___x_2398_; lean_object* v_e_x27_2400_; lean_object* v_proof_2401_; uint8_t v_contextDependent_2402_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref_known(v___x_2396_, 1);
v___x_2398_ = 0;
if (lean_obj_tag(v_a_2397_) == 0)
{
uint8_t v_contextDependent_2497_; 
v_contextDependent_2497_ = lean_ctor_get_uint8(v_a_2397_, 1);
lean_dec_ref_known(v_a_2397_, 0);
v_e_x27_2400_ = v_a_2390_;
v_proof_2401_ = v___x_2395_;
v_contextDependent_2402_ = v_contextDependent_2497_;
goto v___jp_2399_;
}
else
{
lean_object* v_e_x27_2498_; lean_object* v_proof_2499_; uint8_t v_contextDependent_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v_e_x27_2498_ = lean_ctor_get(v_a_2397_, 0);
lean_inc_ref_n(v_e_x27_2498_, 2);
v_proof_2499_ = lean_ctor_get(v_a_2397_, 1);
lean_inc_ref(v_proof_2499_);
v_contextDependent_2500_ = lean_ctor_get_uint8(v_a_2397_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2397_, 2);
lean_inc_ref(v_inst_x27_2335_);
lean_inc_ref(v_c_x27_2333_);
v___x_2501_ = l_Lean_mkAppB(v___x_2391_, v_c_x27_2333_, v_inst_x27_2335_);
v___x_2502_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___x_2501_, v_a_2390_, v___x_2395_, v_e_x27_2498_, v_proof_2499_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2503_);
lean_dec_ref_known(v___x_2502_, 1);
v_e_x27_2400_ = v_e_x27_2498_;
v_proof_2401_ = v_a_2503_;
v_contextDependent_2402_ = v_contextDependent_2500_;
goto v___jp_2399_;
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_dec_ref(v_e_x27_2498_);
lean_dec_ref(v_fallback_2336_);
lean_dec_ref(v_inst_x27_2335_);
lean_dec_ref(v_h_2334_);
lean_dec_ref(v_c_x27_2333_);
lean_dec_ref(v_b_2332_);
lean_dec_ref(v_a_2331_);
lean_dec_ref(v_inst_2330_);
lean_dec_ref(v_c_2329_);
lean_dec_ref(v_00_u03b1_2328_);
v_a_2504_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2502_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2502_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
v___jp_2399_:
{
lean_object* v___x_2403_; 
v___x_2403_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_x27_2400_, v_a_2343_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2404_);
lean_dec_ref_known(v___x_2403_, 1);
v___x_2405_ = l_Lean_Expr_cleanupAnnotations(v_a_2404_);
v___x_2406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_2407_ = l_Lean_Expr_isConstOf(v___x_2405_, v___x_2406_);
if (v___x_2407_ == 0)
{
lean_object* v___x_2408_; uint8_t v___x_2409_; 
v___x_2408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_2409_ = l_Lean_Expr_isConstOf(v___x_2405_, v___x_2408_);
lean_dec_ref(v___x_2405_);
if (v___x_2409_ == 0)
{
lean_object* v___x_2410_; 
lean_dec_ref(v_proof_2401_);
lean_dec_ref(v_inst_x27_2335_);
lean_dec_ref(v_h_2334_);
lean_dec_ref(v_c_x27_2333_);
lean_dec_ref(v_b_2332_);
lean_dec_ref(v_a_2331_);
lean_dec_ref(v_inst_2330_);
lean_dec_ref(v_c_2329_);
lean_dec_ref(v_00_u03b1_2328_);
lean_inc(v_a_2345_);
lean_inc_ref(v_a_2344_);
lean_inc(v_a_2343_);
lean_inc_ref(v_a_2342_);
lean_inc(v_a_2341_);
lean_inc_ref(v_a_2340_);
lean_inc(v_a_2339_);
lean_inc_ref(v_a_2338_);
lean_inc(v_a_2337_);
v___x_2410_ = lean_apply_10(v_fallback_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, lean_box(0));
return v___x_2410_;
}
else
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
lean_dec_ref(v_fallback_2336_);
v___x_2411_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2);
lean_inc_ref(v_c_x27_2333_);
v___x_2412_ = l_Lean_mkApp3(v___x_2411_, v_c_x27_2333_, v_inst_x27_2335_, v_proof_2401_);
v___x_2413_ = l_Lean_Meta_Sym_shareCommon(v___x_2412_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc_n(v_a_2414_, 2);
lean_dec_ref_known(v___x_2413_, 1);
v___x_2415_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2);
lean_inc_ref(v_h_2334_);
lean_inc_ref(v_c_x27_2333_);
lean_inc_ref(v_c_2329_);
v___x_2416_ = l_Lean_mkApp4(v___x_2415_, v_c_2329_, v_c_x27_2333_, v_h_2334_, v_a_2414_);
v___x_2417_ = lean_mk_empty_array_with_capacity(v___x_2392_);
v___x_2418_ = lean_array_push(v___x_2417_, v___x_2416_);
lean_inc_ref(v_a_2331_);
v___x_2419_ = l_Lean_Expr_betaRev(v_a_2331_, v___x_2418_, v___x_2398_, v___x_2398_);
lean_dec_ref(v___x_2418_);
v___x_2420_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2419_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2433_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2423_ = v___x_2420_;
v_isShared_2424_ = v_isSharedCheck_2433_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2420_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2433_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2431_; 
v___x_2425_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4));
v___x_2426_ = l_Lean_Expr_constLevels_x21(v_f_2327_);
v___x_2427_ = l_Lean_mkConst(v___x_2425_, v___x_2426_);
v___x_2428_ = l_Lean_mkApp8(v___x_2427_, v_00_u03b1_2328_, v_c_2329_, v_inst_2330_, v_a_2331_, v_b_2332_, v_c_x27_2333_, v_h_2334_, v_a_2414_);
v___x_2429_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2429_, 0, v_a_2421_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
lean_ctor_set_uint8(v___x_2429_, sizeof(void*)*2, v___x_2398_);
lean_ctor_set_uint8(v___x_2429_, sizeof(void*)*2 + 1, v_contextDependent_2402_);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 0, v___x_2429_);
v___x_2431_ = v___x_2423_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2429_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_dec(v_a_2414_);
lean_dec_ref(v_h_2334_);
lean_dec_ref(v_c_x27_2333_);
lean_dec_ref(v_b_2332_);
lean_dec_ref(v_a_2331_);
lean_dec_ref(v_inst_2330_);
lean_dec_ref(v_c_2329_);
lean_dec_ref(v_00_u03b1_2328_);
v_a_2434_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2420_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2420_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec_ref(v_h_2334_);
lean_dec_ref(v_c_x27_2333_);
lean_dec_ref(v_b_2332_);
lean_dec_ref(v_a_2331_);
lean_dec_ref(v_inst_2330_);
lean_dec_ref(v_c_2329_);
lean_dec_ref(v_00_u03b1_2328_);
v_a_2442_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2413_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2413_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2442_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
}
else
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
lean_dec_ref(v___x_2405_);
lean_dec_ref(v_fallback_2336_);
v___x_2450_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5);
lean_inc_ref(v_c_x27_2333_);
v___x_2451_ = l_Lean_mkApp3(v___x_2450_, v_c_x27_2333_, v_inst_x27_2335_, v_proof_2401_);
v___x_2452_ = l_Lean_Meta_Sym_shareCommon(v___x_2451_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc_n(v_a_2453_, 2);
lean_dec_ref_known(v___x_2452_, 1);
v___x_2454_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7);
lean_inc_ref(v_h_2334_);
lean_inc_ref(v_c_x27_2333_);
lean_inc_ref(v_c_2329_);
v___x_2455_ = l_Lean_mkApp4(v___x_2454_, v_c_2329_, v_c_x27_2333_, v_h_2334_, v_a_2453_);
v___x_2456_ = lean_mk_empty_array_with_capacity(v___x_2392_);
v___x_2457_ = lean_array_push(v___x_2456_, v___x_2455_);
lean_inc_ref(v_b_2332_);
v___x_2458_ = l_Lean_Expr_betaRev(v_b_2332_, v___x_2457_, v___x_2398_, v___x_2398_);
lean_dec_ref(v___x_2457_);
v___x_2459_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2458_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2472_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2462_ = v___x_2459_;
v_isShared_2463_ = v_isSharedCheck_2472_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2459_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2472_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2470_; 
v___x_2464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9));
v___x_2465_ = l_Lean_Expr_constLevels_x21(v_f_2327_);
v___x_2466_ = l_Lean_mkConst(v___x_2464_, v___x_2465_);
v___x_2467_ = l_Lean_mkApp8(v___x_2466_, v_00_u03b1_2328_, v_c_2329_, v_inst_2330_, v_a_2331_, v_b_2332_, v_c_x27_2333_, v_h_2334_, v_a_2453_);
v___x_2468_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2468_, 0, v_a_2460_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*2, v___x_2398_);
lean_ctor_set_uint8(v___x_2468_, sizeof(void*)*2 + 1, v_contextDependent_2402_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 0, v___x_2468_);
v___x_2470_ = v___x_2462_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec(v_a_2453_);
lean_dec_ref(v_h_2334_);
lean_dec_ref(v_c_x27_2333_);
lean_dec_ref(v_b_2332_);
lean_dec_ref(v_a_2331_);
lean_dec_ref(v_inst_2330_);
lean_dec_ref(v_c_2329_);
lean_dec_ref(v_00_u03b1_2328_);
v_a_2473_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2459_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2459_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec_ref(v_h_2334_);
lean_dec_ref(v_c_x27_2333_);
lean_dec_ref(v_b_2332_);
lean_dec_ref(v_a_2331_);
lean_dec_ref(v_inst_2330_);
lean_dec_ref(v_c_2329_);
lean_dec_ref(v_00_u03b1_2328_);
v_a_2481_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2452_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2452_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
}
else
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
lean_dec_ref(v_proof_2401_);
lean_dec_ref(v_fallback_2336_);
lean_dec_ref(v_inst_x27_2335_);
lean_dec_ref(v_h_2334_);
lean_dec_ref(v_c_x27_2333_);
lean_dec_ref(v_b_2332_);
lean_dec_ref(v_a_2331_);
lean_dec_ref(v_inst_2330_);
lean_dec_ref(v_c_2329_);
lean_dec_ref(v_00_u03b1_2328_);
v_a_2489_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2403_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2403_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2395_);
lean_dec(v_a_2390_);
lean_dec_ref(v_fallback_2336_);
lean_dec_ref(v_inst_x27_2335_);
lean_dec_ref(v_h_2334_);
lean_dec_ref(v_c_x27_2333_);
lean_dec_ref(v_b_2332_);
lean_dec_ref(v_a_2331_);
lean_dec_ref(v_inst_2330_);
lean_dec_ref(v_c_2329_);
lean_dec_ref(v_00_u03b1_2328_);
return v___x_2396_;
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
lean_dec_ref(v_fallback_2336_);
lean_dec_ref(v_inst_x27_2335_);
lean_dec_ref(v_h_2334_);
lean_dec_ref(v_c_x27_2333_);
lean_dec_ref(v_b_2332_);
lean_dec_ref(v_a_2331_);
lean_dec_ref(v_inst_2330_);
lean_dec_ref(v_c_2329_);
lean_dec_ref(v_00_u03b1_2328_);
v_a_2512_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2389_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2389_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec_ref(v_fallback_2336_);
lean_dec_ref(v_inst_x27_2335_);
lean_dec_ref(v_h_2334_);
lean_dec_ref(v_c_x27_2333_);
lean_dec_ref(v_b_2332_);
lean_dec_ref(v_a_2331_);
lean_dec_ref(v_inst_2330_);
lean_dec_ref(v_c_2329_);
lean_dec_ref(v_00_u03b1_2328_);
v_a_2520_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2351_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2351_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_2528_ = _args[0];
lean_object* v_00_u03b1_2529_ = _args[1];
lean_object* v_c_2530_ = _args[2];
lean_object* v_inst_2531_ = _args[3];
lean_object* v_a_2532_ = _args[4];
lean_object* v_b_2533_ = _args[5];
lean_object* v_c_x27_2534_ = _args[6];
lean_object* v_h_2535_ = _args[7];
lean_object* v_inst_x27_2536_ = _args[8];
lean_object* v_fallback_2537_ = _args[9];
lean_object* v_a_2538_ = _args[10];
lean_object* v_a_2539_ = _args[11];
lean_object* v_a_2540_ = _args[12];
lean_object* v_a_2541_ = _args[13];
lean_object* v_a_2542_ = _args[14];
lean_object* v_a_2543_ = _args[15];
lean_object* v_a_2544_ = _args[16];
lean_object* v_a_2545_ = _args[17];
lean_object* v_a_2546_ = _args[18];
lean_object* v_a_2547_ = _args[19];
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr(v_f_2528_, v_00_u03b1_2529_, v_c_2530_, v_inst_2531_, v_a_2532_, v_b_2533_, v_c_x27_2534_, v_h_2535_, v_inst_x27_2536_, v_fallback_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_);
lean_dec(v_a_2546_);
lean_dec_ref(v_a_2545_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
lean_dec(v_a_2540_);
lean_dec_ref(v_a_2539_);
lean_dec(v_a_2538_);
lean_dec_ref(v_f_2528_);
return v_res_2548_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2552_ = lean_unsigned_to_nat(0u);
v___x_2553_ = l_Lean_mkBVar(v___x_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2(lean_object* v_proof_2559_, lean_object* v_arg_2560_, lean_object* v_e_x27_2561_, lean_object* v_arg_2562_, uint8_t v_a_2563_, lean_object* v_arg_2564_, lean_object* v___x_2565_, lean_object* v_snd_2566_, lean_object* v_e_2567_, uint8_t v___x_2568_, uint8_t v_contextDependent_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l_Lean_Meta_Sym_shareCommon(v_proof_2559_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v___x_2582_; uint8_t v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc_n(v_a_2581_, 2);
lean_dec_ref_known(v___x_2580_, 1);
v___x_2582_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__1));
v___x_2583_ = 0;
v___x_2584_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2);
v___x_2585_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__2);
lean_inc_ref_n(v_e_x27_2561_, 2);
lean_inc_ref(v_arg_2560_);
v___x_2586_ = l_Lean_mkApp4(v___x_2584_, v_arg_2560_, v_e_x27_2561_, v_a_2581_, v___x_2585_);
v___x_2587_ = lean_unsigned_to_nat(1u);
v___x_2588_ = lean_mk_empty_array_with_capacity(v___x_2587_);
lean_inc_ref(v___x_2588_);
v___x_2589_ = lean_array_push(v___x_2588_, v___x_2586_);
v___x_2590_ = l_Lean_Expr_betaRev(v_arg_2562_, v___x_2589_, v_a_2563_, v_a_2563_);
lean_dec_ref(v___x_2589_);
v___x_2591_ = l_Lean_mkLambda(v___x_2582_, v___x_2583_, v_e_x27_2561_, v___x_2590_);
v___x_2592_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2591_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_a_2593_);
lean_dec_ref_known(v___x_2592_, 1);
lean_inc_ref_n(v_e_x27_2561_, 2);
v___x_2594_ = l_Lean_mkNot(v_e_x27_2561_);
v___x_2595_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7);
lean_inc(v_a_2581_);
v___x_2596_ = l_Lean_mkApp4(v___x_2595_, v_arg_2560_, v_e_x27_2561_, v_a_2581_, v___x_2585_);
v___x_2597_ = lean_array_push(v___x_2588_, v___x_2596_);
v___x_2598_ = l_Lean_Expr_betaRev(v_arg_2564_, v___x_2597_, v_a_2563_, v_a_2563_);
lean_dec_ref(v___x_2597_);
v___x_2599_ = l_Lean_mkLambda(v___x_2582_, v___x_2583_, v___x_2594_, v___x_2598_);
v___x_2600_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2599_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v___x_2602_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref_known(v___x_2600_, 1);
lean_inc_ref(v_snd_2566_);
lean_inc_ref(v_e_x27_2561_);
v___x_2602_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v___x_2565_, v_e_x27_2561_, v_snd_2566_, v_a_2593_, v_a_2601_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
if (lean_obj_tag(v___x_2602_) == 0)
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2614_; 
v_a_2603_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2605_ = v___x_2602_;
v_isShared_2606_ = v_isSharedCheck_2614_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v___x_2602_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2614_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2612_; 
v___x_2607_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__4));
v___x_2608_ = l_Lean_Expr_replaceFn(v_e_2567_, v___x_2607_);
v___x_2609_ = l_Lean_mkApp3(v___x_2608_, v_e_x27_2561_, v_snd_2566_, v_a_2581_);
v___x_2610_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2610_, 0, v_a_2603_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*2, v___x_2568_);
lean_ctor_set_uint8(v___x_2610_, sizeof(void*)*2 + 1, v_contextDependent_2569_);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 0, v___x_2610_);
v___x_2612_ = v___x_2605_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2610_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec(v_a_2581_);
lean_dec_ref(v_e_2567_);
lean_dec_ref(v_snd_2566_);
lean_dec_ref(v_e_x27_2561_);
v_a_2615_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2602_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2602_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_dec(v_a_2593_);
lean_dec(v_a_2581_);
lean_dec_ref(v_e_2567_);
lean_dec_ref(v_snd_2566_);
lean_dec_ref(v___x_2565_);
lean_dec_ref(v_e_x27_2561_);
v_a_2623_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2600_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2600_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
lean_dec_ref(v___x_2588_);
lean_dec(v_a_2581_);
lean_dec_ref(v_e_2567_);
lean_dec_ref(v_snd_2566_);
lean_dec_ref(v___x_2565_);
lean_dec_ref(v_arg_2564_);
lean_dec_ref(v_e_x27_2561_);
lean_dec_ref(v_arg_2560_);
v_a_2631_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2592_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2592_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_dec_ref(v_e_2567_);
lean_dec_ref(v_snd_2566_);
lean_dec_ref(v___x_2565_);
lean_dec_ref(v_arg_2564_);
lean_dec_ref(v_arg_2562_);
lean_dec_ref(v_e_x27_2561_);
lean_dec_ref(v_arg_2560_);
v_a_2639_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2580_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2580_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___boxed(lean_object** _args){
lean_object* v_proof_2647_ = _args[0];
lean_object* v_arg_2648_ = _args[1];
lean_object* v_e_x27_2649_ = _args[2];
lean_object* v_arg_2650_ = _args[3];
lean_object* v_a_2651_ = _args[4];
lean_object* v_arg_2652_ = _args[5];
lean_object* v___x_2653_ = _args[6];
lean_object* v_snd_2654_ = _args[7];
lean_object* v_e_2655_ = _args[8];
lean_object* v___x_2656_ = _args[9];
lean_object* v_contextDependent_2657_ = _args[10];
lean_object* v___y_2658_ = _args[11];
lean_object* v___y_2659_ = _args[12];
lean_object* v___y_2660_ = _args[13];
lean_object* v___y_2661_ = _args[14];
lean_object* v___y_2662_ = _args[15];
lean_object* v___y_2663_ = _args[16];
lean_object* v___y_2664_ = _args[17];
lean_object* v___y_2665_ = _args[18];
lean_object* v___y_2666_ = _args[19];
lean_object* v___y_2667_ = _args[20];
_start:
{
uint8_t v_a_30533__boxed_2668_; uint8_t v___x_30537__boxed_2669_; uint8_t v_contextDependent_30538__boxed_2670_; lean_object* v_res_2671_; 
v_a_30533__boxed_2668_ = lean_unbox(v_a_2651_);
v___x_30537__boxed_2669_ = lean_unbox(v___x_2656_);
v_contextDependent_30538__boxed_2670_ = lean_unbox(v_contextDependent_2657_);
v_res_2671_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2(v_proof_2647_, v_arg_2648_, v_e_x27_2649_, v_arg_2650_, v_a_30533__boxed_2668_, v_arg_2652_, v___x_2653_, v_snd_2654_, v_e_2655_, v___x_30537__boxed_2669_, v_contextDependent_30538__boxed_2670_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
return v_res_2671_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2678_ = lean_box(0);
v___x_2679_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
v___x_2680_ = l_Lean_mkConst(v___x_2679_, v___x_2678_);
return v___x_2680_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2681_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4);
v___x_2682_ = lean_unsigned_to_nat(1u);
v___x_2683_ = lean_mk_empty_array_with_capacity(v___x_2682_);
v___x_2684_ = lean_array_push(v___x_2683_, v___x_2681_);
return v___x_2684_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2691_ = lean_box(0);
v___x_2692_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8));
v___x_2693_ = l_Lean_mkConst(v___x_2692_, v___x_2691_);
return v___x_2693_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2694_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
v___x_2695_ = lean_unsigned_to_nat(1u);
v___x_2696_ = lean_mk_empty_array_with_capacity(v___x_2695_);
v___x_2697_ = lean_array_push(v___x_2696_, v___x_2694_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(uint8_t v___x_2706_, lean_object* v_e_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___x_2721_; uint8_t v___x_2722_; 
lean_inc_ref(v_e_2707_);
v___x_2721_ = l_Lean_Expr_cleanupAnnotations(v_e_2707_);
v___x_2722_ = l_Lean_Expr_isApp(v___x_2721_);
if (v___x_2722_ == 0)
{
lean_dec_ref(v___x_2721_);
lean_dec_ref(v_e_2707_);
goto v___jp_2718_;
}
else
{
lean_object* v_arg_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; 
v_arg_2723_ = lean_ctor_get(v___x_2721_, 1);
lean_inc_ref(v_arg_2723_);
v___x_2724_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2721_);
v___x_2725_ = l_Lean_Expr_isApp(v___x_2724_);
if (v___x_2725_ == 0)
{
lean_dec_ref(v___x_2724_);
lean_dec_ref(v_arg_2723_);
lean_dec_ref(v_e_2707_);
goto v___jp_2718_;
}
else
{
lean_object* v_arg_2726_; lean_object* v___x_2727_; uint8_t v___x_2728_; 
v_arg_2726_ = lean_ctor_get(v___x_2724_, 1);
lean_inc_ref(v_arg_2726_);
v___x_2727_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2724_);
v___x_2728_ = l_Lean_Expr_isApp(v___x_2727_);
if (v___x_2728_ == 0)
{
lean_dec_ref(v___x_2727_);
lean_dec_ref(v_arg_2726_);
lean_dec_ref(v_arg_2723_);
lean_dec_ref(v_e_2707_);
goto v___jp_2718_;
}
else
{
lean_object* v_arg_2729_; lean_object* v___x_2730_; uint8_t v___x_2731_; 
v_arg_2729_ = lean_ctor_get(v___x_2727_, 1);
lean_inc_ref(v_arg_2729_);
v___x_2730_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2727_);
v___x_2731_ = l_Lean_Expr_isApp(v___x_2730_);
if (v___x_2731_ == 0)
{
lean_dec_ref(v___x_2730_);
lean_dec_ref(v_arg_2729_);
lean_dec_ref(v_arg_2726_);
lean_dec_ref(v_arg_2723_);
lean_dec_ref(v_e_2707_);
goto v___jp_2718_;
}
else
{
lean_object* v_arg_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; 
v_arg_2732_ = lean_ctor_get(v___x_2730_, 1);
lean_inc_ref(v_arg_2732_);
v___x_2733_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2730_);
v___x_2734_ = l_Lean_Expr_isApp(v___x_2733_);
if (v___x_2734_ == 0)
{
lean_dec_ref(v___x_2733_);
lean_dec_ref(v_arg_2732_);
lean_dec_ref(v_arg_2729_);
lean_dec_ref(v_arg_2726_);
lean_dec_ref(v_arg_2723_);
lean_dec_ref(v_e_2707_);
goto v___jp_2718_;
}
else
{
lean_object* v_arg_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; uint8_t v___x_2738_; 
v_arg_2735_ = lean_ctor_get(v___x_2733_, 1);
lean_inc_ref(v_arg_2735_);
v___x_2736_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2733_);
v___x_2737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1));
v___x_2738_ = l_Lean_Expr_isConstOf(v___x_2736_, v___x_2737_);
if (v___x_2738_ == 0)
{
lean_dec_ref(v___x_2736_);
lean_dec_ref(v_arg_2735_);
lean_dec_ref(v_arg_2732_);
lean_dec_ref(v_arg_2729_);
lean_dec_ref(v_arg_2726_);
lean_dec_ref(v_arg_2723_);
lean_dec_ref(v_e_2707_);
goto v___jp_2718_;
}
else
{
lean_object* v___x_2739_; 
lean_inc(v___y_2716_);
lean_inc_ref(v___y_2715_);
lean_inc(v___y_2714_);
lean_inc_ref(v___y_2713_);
lean_inc(v___y_2712_);
lean_inc_ref(v___y_2711_);
lean_inc(v___y_2710_);
lean_inc_ref(v___y_2709_);
lean_inc(v___y_2708_);
lean_inc_ref(v_arg_2732_);
v___x_2739_ = lean_sym_simp(v_arg_2732_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
lean_inc(v_a_2740_);
lean_dec_ref_known(v___x_2739_, 1);
if (lean_obj_tag(v_a_2740_) == 0)
{
uint8_t v_contextDependent_2741_; lean_object* v___x_2742_; 
lean_dec_ref(v_e_2707_);
v_contextDependent_2741_ = lean_ctor_get_uint8(v_a_2740_, 1);
lean_dec_ref_known(v_a_2740_, 0);
v___x_2742_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_2732_, v___y_2711_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; uint8_t v___x_2744_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref_known(v___x_2742_, 1);
v___x_2744_ = lean_unbox(v_a_2743_);
if (v___x_2744_ == 0)
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_2732_, v___y_2711_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; uint8_t v___x_2747_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc(v_a_2746_);
lean_dec_ref_known(v___x_2745_, 1);
v___x_2747_ = lean_unbox(v_a_2746_);
lean_dec(v_a_2746_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2748_; lean_object* v___f_2749_; lean_object* v___x_2750_; 
lean_dec(v_a_2743_);
v___x_2748_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_2738_, v_contextDependent_2741_);
v___f_2749_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2749_, 0, v___x_2748_);
v___x_2750_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v___x_2736_, v_arg_2735_, v_arg_2732_, v_arg_2729_, v_arg_2726_, v_arg_2723_, v___f_2749_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
lean_dec_ref(v___x_2736_);
return v___x_2750_;
}
else
{
lean_object* v___x_2751_; uint8_t v___x_2752_; uint8_t v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
lean_dec_ref(v_arg_2732_);
lean_dec_ref(v_arg_2729_);
v___x_2751_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5);
v___x_2752_ = lean_unbox(v_a_2743_);
v___x_2753_ = lean_unbox(v_a_2743_);
lean_inc_ref(v_arg_2723_);
v___x_2754_ = l_Lean_Expr_betaRev(v_arg_2723_, v___x_2751_, v___x_2752_, v___x_2753_);
v___x_2755_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2754_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2769_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2758_ = v___x_2755_;
v_isShared_2759_ = v_isSharedCheck_2769_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2755_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2769_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; uint8_t v___x_2765_; lean_object* v___x_2767_; 
v___x_2760_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6));
v___x_2761_ = l_Lean_Expr_constLevels_x21(v___x_2736_);
lean_dec_ref(v___x_2736_);
v___x_2762_ = l_Lean_mkConst(v___x_2760_, v___x_2761_);
v___x_2763_ = l_Lean_mkApp3(v___x_2762_, v_arg_2735_, v_arg_2726_, v_arg_2723_);
v___x_2764_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2764_, 0, v_a_2756_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = lean_unbox(v_a_2743_);
lean_dec(v_a_2743_);
lean_ctor_set_uint8(v___x_2764_, sizeof(void*)*2, v___x_2765_);
lean_ctor_set_uint8(v___x_2764_, sizeof(void*)*2 + 1, v_contextDependent_2741_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2764_);
v___x_2767_ = v___x_2758_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2764_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec(v_a_2743_);
lean_dec_ref(v___x_2736_);
lean_dec_ref(v_arg_2735_);
lean_dec_ref(v_arg_2726_);
lean_dec_ref(v_arg_2723_);
v_a_2770_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2755_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2755_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
lean_dec(v_a_2743_);
lean_dec_ref(v___x_2736_);
lean_dec_ref(v_arg_2735_);
lean_dec_ref(v_arg_2732_);
lean_dec_ref(v_arg_2729_);
lean_dec_ref(v_arg_2726_);
lean_dec_ref(v_arg_2723_);
v_a_2778_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2745_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2745_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
else
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
lean_dec(v_a_2743_);
lean_dec_ref(v_arg_2732_);
lean_dec_ref(v_arg_2729_);
v___x_2786_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10);
lean_inc_ref(v_arg_2726_);
v___x_2787_ = l_Lean_Expr_betaRev(v_arg_2726_, v___x_2786_, v___x_2706_, v___x_2706_);
v___x_2788_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2787_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2801_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2801_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2801_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2799_; 
v___x_2793_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11));
v___x_2794_ = l_Lean_Expr_constLevels_x21(v___x_2736_);
lean_dec_ref(v___x_2736_);
v___x_2795_ = l_Lean_mkConst(v___x_2793_, v___x_2794_);
v___x_2796_ = l_Lean_mkApp3(v___x_2795_, v_arg_2735_, v_arg_2726_, v_arg_2723_);
v___x_2797_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2797_, 0, v_a_2789_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
lean_ctor_set_uint8(v___x_2797_, sizeof(void*)*2, v___x_2706_);
lean_ctor_set_uint8(v___x_2797_, sizeof(void*)*2 + 1, v_contextDependent_2741_);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2797_);
v___x_2799_ = v___x_2791_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec_ref(v___x_2736_);
lean_dec_ref(v_arg_2735_);
lean_dec_ref(v_arg_2726_);
lean_dec_ref(v_arg_2723_);
v_a_2802_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2788_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2788_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec_ref(v___x_2736_);
lean_dec_ref(v_arg_2735_);
lean_dec_ref(v_arg_2732_);
lean_dec_ref(v_arg_2729_);
lean_dec_ref(v_arg_2726_);
lean_dec_ref(v_arg_2723_);
v_a_2810_ = lean_ctor_get(v___x_2742_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2742_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2742_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2742_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
else
{
lean_object* v_e_x27_2818_; lean_object* v_proof_2819_; uint8_t v_contextDependent_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2950_; 
v_e_x27_2818_ = lean_ctor_get(v_a_2740_, 0);
v_proof_2819_ = lean_ctor_get(v_a_2740_, 1);
v_contextDependent_2820_ = lean_ctor_get_uint8(v_a_2740_, sizeof(void*)*2 + 1);
v_isSharedCheck_2950_ = !lean_is_exclusive(v_a_2740_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2822_ = v_a_2740_;
v_isShared_2823_ = v_isSharedCheck_2950_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_proof_2819_);
lean_inc(v_e_x27_2818_);
lean_dec(v_a_2740_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2950_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_2818_, v___y_2711_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; uint8_t v___x_2826_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref_known(v___x_2824_, 1);
v___x_2826_ = lean_unbox(v_a_2825_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_2818_, v___y_2711_);
lean_dec_ref(v_e_x27_2818_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; uint8_t v___x_2829_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2827_, 1);
v___x_2829_ = lean_unbox(v_a_2828_);
if (v___x_2829_ == 0)
{
lean_object* v___x_2830_; 
lean_dec(v_a_2825_);
lean_del_object(v___x_2822_);
lean_dec_ref(v_proof_2819_);
lean_inc_ref(v_arg_2729_);
v___x_2830_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance(v_arg_2729_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v_fst_2832_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2830_, 1);
v_fst_2832_ = lean_ctor_get(v_a_2831_, 0);
lean_inc(v_fst_2832_);
if (lean_obj_tag(v_fst_2832_) == 0)
{
uint8_t v_contextDependent_2833_; lean_object* v___x_2834_; lean_object* v___f_2835_; lean_object* v___x_2836_; 
lean_dec(v_a_2831_);
lean_dec(v_a_2828_);
lean_dec_ref(v_e_2707_);
v_contextDependent_2833_ = lean_ctor_get_uint8(v_fst_2832_, 1);
lean_dec_ref_known(v_fst_2832_, 0);
v___x_2834_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_2738_, v_contextDependent_2833_);
v___f_2835_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2835_, 0, v___x_2834_);
v___x_2836_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v___x_2736_, v_arg_2735_, v_arg_2732_, v_arg_2729_, v_arg_2726_, v_arg_2723_, v___f_2835_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
lean_dec_ref(v___x_2736_);
return v___x_2836_;
}
else
{
lean_object* v_snd_2837_; lean_object* v_e_x27_2838_; lean_object* v_proof_2839_; uint8_t v_contextDependent_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___f_2845_; lean_object* v___x_2846_; 
v_snd_2837_ = lean_ctor_get(v_a_2831_, 1);
lean_inc_n(v_snd_2837_, 2);
lean_dec(v_a_2831_);
v_e_x27_2838_ = lean_ctor_get(v_fst_2832_, 0);
lean_inc_ref_n(v_e_x27_2838_, 2);
v_proof_2839_ = lean_ctor_get(v_fst_2832_, 1);
lean_inc_ref_n(v_proof_2839_, 2);
v_contextDependent_2840_ = lean_ctor_get_uint8(v_fst_2832_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_2832_, 2);
v___x_2841_ = lean_unsigned_to_nat(4u);
v___x_2842_ = l_Lean_Expr_getBoundedAppFn(v___x_2841_, v_e_2707_);
v___x_2843_ = lean_box(v___x_2738_);
v___x_2844_ = lean_box(v_contextDependent_2840_);
lean_inc_ref(v_arg_2723_);
lean_inc_ref(v_arg_2726_);
lean_inc_ref(v_arg_2732_);
v___f_2845_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___boxed), 21, 11);
lean_closure_set(v___f_2845_, 0, v_proof_2839_);
lean_closure_set(v___f_2845_, 1, v_arg_2732_);
lean_closure_set(v___f_2845_, 2, v_e_x27_2838_);
lean_closure_set(v___f_2845_, 3, v_arg_2726_);
lean_closure_set(v___f_2845_, 4, v_a_2828_);
lean_closure_set(v___f_2845_, 5, v_arg_2723_);
lean_closure_set(v___f_2845_, 6, v___x_2842_);
lean_closure_set(v___f_2845_, 7, v_snd_2837_);
lean_closure_set(v___f_2845_, 8, v_e_2707_);
lean_closure_set(v___f_2845_, 9, v___x_2843_);
lean_closure_set(v___f_2845_, 10, v___x_2844_);
v___x_2846_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr(v___x_2736_, v_arg_2735_, v_arg_2732_, v_arg_2729_, v_arg_2726_, v_arg_2723_, v_e_x27_2838_, v_proof_2839_, v_snd_2837_, v___f_2845_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
lean_dec_ref(v___x_2736_);
return v___x_2846_;
}
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_dec(v_a_2828_);
lean_dec_ref(v___x_2736_);
lean_dec_ref(v_arg_2735_);
lean_dec_ref(v_arg_2732_);
lean_dec_ref(v_arg_2729_);
lean_dec_ref(v_arg_2726_);
lean_dec_ref(v_arg_2723_);
lean_dec_ref(v_e_2707_);
v_a_2847_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2830_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2830_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
else
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
lean_dec(v_a_2828_);
lean_dec_ref(v___x_2736_);
lean_dec_ref(v_arg_2735_);
lean_dec_ref(v_arg_2729_);
lean_dec_ref(v_arg_2726_);
lean_inc_ref(v_proof_2819_);
v___x_2855_ = l_Lean_Meta_mkOfEqFalseCore(v_arg_2732_, v_proof_2819_);
v___x_2856_ = l_Lean_Meta_Sym_shareCommon(v___x_2855_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; uint8_t v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2857_);
lean_dec_ref_known(v___x_2856_, 1);
v___x_2858_ = lean_unsigned_to_nat(1u);
v___x_2859_ = lean_mk_empty_array_with_capacity(v___x_2858_);
v___x_2860_ = lean_array_push(v___x_2859_, v_a_2857_);
v___x_2861_ = lean_unbox(v_a_2825_);
v___x_2862_ = lean_unbox(v_a_2825_);
v___x_2863_ = l_Lean_Expr_betaRev(v_arg_2723_, v___x_2860_, v___x_2861_, v___x_2862_);
lean_dec_ref(v___x_2860_);
v___x_2864_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2863_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2879_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2867_ = v___x_2864_;
v_isShared_2868_ = v_isSharedCheck_2879_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2864_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2879_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2873_; 
v___x_2869_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13));
v___x_2870_ = l_Lean_Expr_replaceFn(v_e_2707_, v___x_2869_);
v___x_2871_ = l_Lean_Expr_app___override(v___x_2870_, v_proof_2819_);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 1, v___x_2871_);
lean_ctor_set(v___x_2822_, 0, v_a_2865_);
v___x_2873_ = v___x_2822_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2865_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v___x_2871_);
v___x_2873_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
uint8_t v___x_2874_; lean_object* v___x_2876_; 
v___x_2874_ = lean_unbox(v_a_2825_);
lean_dec(v_a_2825_);
lean_ctor_set_uint8(v___x_2873_, sizeof(void*)*2, v___x_2874_);
lean_ctor_set_uint8(v___x_2873_, sizeof(void*)*2 + 1, v_contextDependent_2820_);
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 0, v___x_2873_);
v___x_2876_ = v___x_2867_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2873_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec(v_a_2825_);
lean_del_object(v___x_2822_);
lean_dec_ref(v_proof_2819_);
lean_dec_ref(v_e_2707_);
v_a_2880_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2864_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2864_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec(v_a_2825_);
lean_del_object(v___x_2822_);
lean_dec_ref(v_proof_2819_);
lean_dec_ref(v_arg_2723_);
lean_dec_ref(v_e_2707_);
v_a_2888_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2856_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2856_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v_a_2825_);
lean_del_object(v___x_2822_);
lean_dec_ref(v_proof_2819_);
lean_dec_ref(v___x_2736_);
lean_dec_ref(v_arg_2735_);
lean_dec_ref(v_arg_2732_);
lean_dec_ref(v_arg_2729_);
lean_dec_ref(v_arg_2726_);
lean_dec_ref(v_arg_2723_);
lean_dec_ref(v_e_2707_);
v_a_2896_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2827_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2827_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
else
{
lean_object* v___x_2904_; lean_object* v___x_2905_; 
lean_dec(v_a_2825_);
lean_dec_ref(v_e_x27_2818_);
lean_dec_ref(v___x_2736_);
lean_dec_ref(v_arg_2735_);
lean_dec_ref(v_arg_2729_);
lean_dec_ref(v_arg_2723_);
lean_inc_ref(v_proof_2819_);
v___x_2904_ = l_Lean_Meta_mkOfEqTrueCore(v_arg_2732_, v_proof_2819_);
v___x_2905_ = l_Lean_Meta_Sym_shareCommon(v___x_2904_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref_known(v___x_2905_, 1);
v___x_2907_ = lean_unsigned_to_nat(1u);
v___x_2908_ = lean_mk_empty_array_with_capacity(v___x_2907_);
v___x_2909_ = lean_array_push(v___x_2908_, v_a_2906_);
v___x_2910_ = l_Lean_Expr_betaRev(v_arg_2726_, v___x_2909_, v___x_2706_, v___x_2706_);
lean_dec_ref(v___x_2909_);
v___x_2911_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2910_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2925_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2914_ = v___x_2911_;
v_isShared_2915_ = v_isSharedCheck_2925_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2911_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2925_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2920_; 
v___x_2916_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15));
v___x_2917_ = l_Lean_Expr_replaceFn(v_e_2707_, v___x_2916_);
v___x_2918_ = l_Lean_Expr_app___override(v___x_2917_, v_proof_2819_);
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 1, v___x_2918_);
lean_ctor_set(v___x_2822_, 0, v_a_2912_);
v___x_2920_ = v___x_2822_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2912_);
lean_ctor_set(v_reuseFailAlloc_2924_, 1, v___x_2918_);
lean_ctor_set_uint8(v_reuseFailAlloc_2924_, sizeof(void*)*2 + 1, v_contextDependent_2820_);
v___x_2920_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2922_; 
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*2, v___x_2706_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v___x_2920_);
v___x_2922_ = v___x_2914_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2920_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
lean_del_object(v___x_2822_);
lean_dec_ref(v_proof_2819_);
lean_dec_ref(v_e_2707_);
v_a_2926_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2911_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2911_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_del_object(v___x_2822_);
lean_dec_ref(v_proof_2819_);
lean_dec_ref(v_arg_2726_);
lean_dec_ref(v_e_2707_);
v_a_2934_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2905_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2905_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_del_object(v___x_2822_);
lean_dec_ref(v_proof_2819_);
lean_dec_ref(v_e_x27_2818_);
lean_dec_ref(v___x_2736_);
lean_dec_ref(v_arg_2735_);
lean_dec_ref(v_arg_2732_);
lean_dec_ref(v_arg_2729_);
lean_dec_ref(v_arg_2726_);
lean_dec_ref(v_arg_2723_);
lean_dec_ref(v_e_2707_);
v_a_2942_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2824_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2824_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2736_);
lean_dec_ref(v_arg_2735_);
lean_dec_ref(v_arg_2732_);
lean_dec_ref(v_arg_2729_);
lean_dec_ref(v_arg_2726_);
lean_dec_ref(v_arg_2723_);
lean_dec_ref(v_e_2707_);
return v___x_2739_;
}
}
}
}
}
}
}
v___jp_2718_:
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2719_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2719_, 0, v___x_2706_);
lean_ctor_set_uint8(v___x_2719_, 1, v___x_2706_);
v___x_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
return v___x_2720_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed(lean_object* v___x_2951_, lean_object* v_e_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
uint8_t v___x_30804__boxed_2963_; lean_object* v_res_2964_; 
v___x_30804__boxed_2963_ = lean_unbox(v___x_2951_);
v_res_2964_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(v___x_30804__boxed_2963_, v_e_2952_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv(lean_object* v_e_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_){
_start:
{
lean_object* v_numArgs_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v_numArgs_2976_ = l_Lean_Expr_getAppNumArgs(v_e_2965_);
v___x_2977_ = lean_unsigned_to_nat(5u);
v___x_2978_ = lean_nat_dec_lt(v_numArgs_2976_, v___x_2977_);
if (v___x_2978_ == 0)
{
lean_object* v___x_2979_; lean_object* v___f_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2979_ = lean_box(v___x_2978_);
v___f_2980_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2980_, 0, v___x_2979_);
v___x_2981_ = lean_nat_sub(v_numArgs_2976_, v___x_2977_);
lean_dec(v_numArgs_2976_);
v___x_2982_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_2965_, v___x_2981_, v___f_2980_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_);
lean_dec(v___x_2981_);
return v___x_2982_;
}
else
{
uint8_t v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
lean_dec(v_numArgs_2976_);
lean_dec_ref(v_e_2965_);
v___x_2983_ = 0;
v___x_2984_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2984_, 0, v___x_2978_);
lean_ctor_set_uint8(v___x_2984_, 1, v___x_2983_);
v___x_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
return v___x_2985_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed(lean_object* v_e_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv(v_e_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_);
lean_dec(v_a_2995_);
lean_dec_ref(v_a_2994_);
lean_dec(v_a_2993_);
lean_dec_ref(v_a_2992_);
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
lean_dec(v_a_2989_);
lean_dec_ref(v_a_2988_);
lean_dec(v_a_2987_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3016_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17_));
v___x_3017_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17_));
v___x_3018_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed), 11, 0);
v___x_3019_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_3016_, v___x_3017_, v___x_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17____boxed(lean_object* v_a_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17_();
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_3023_; uint8_t v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3023_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_17_));
v___x_3024_ = 0;
v___x_3025_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed), 11, 0);
v___x_3026_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_3023_, v___x_3024_, v___x_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_19____boxed(lean_object* v_a_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3443402405____hygCtx___hyg_19_();
return v_res_3028_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3034_ = lean_box(0);
v___x_3035_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1));
v___x_3036_ = l_Lean_mkConst(v___x_3035_, v___x_3034_);
return v___x_3036_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5(void){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3042_ = lean_box(0);
v___x_3043_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4));
v___x_3044_ = l_Lean_mkConst(v___x_3043_, v___x_3042_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(lean_object* v_p_3045_, lean_object* v_inst_3046_, lean_object* v_instToMatch_3047_, lean_object* v_fallback_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_){
_start:
{
lean_object* v___x_3059_; 
v___x_3059_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_instToMatch_3047_, v_a_3055_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3060_);
lean_dec_ref_known(v___x_3059_, 1);
v___x_3061_ = l_Lean_Expr_cleanupAnnotations(v_a_3060_);
v___x_3062_ = l_Lean_Expr_isApp(v___x_3061_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; 
lean_dec_ref(v___x_3061_);
lean_dec_ref(v_inst_3046_);
lean_dec_ref(v_p_3045_);
lean_inc(v_a_3057_);
lean_inc_ref(v_a_3056_);
lean_inc(v_a_3055_);
lean_inc_ref(v_a_3054_);
lean_inc(v_a_3053_);
lean_inc_ref(v_a_3052_);
lean_inc(v_a_3051_);
lean_inc_ref(v_a_3050_);
lean_inc(v_a_3049_);
v___x_3063_ = lean_apply_10(v_fallback_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_, lean_box(0));
return v___x_3063_;
}
else
{
lean_object* v_arg_3064_; lean_object* v___x_3065_; uint8_t v___x_3066_; 
v_arg_3064_ = lean_ctor_get(v___x_3061_, 1);
lean_inc_ref(v_arg_3064_);
v___x_3065_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3061_);
v___x_3066_ = l_Lean_Expr_isApp(v___x_3065_);
if (v___x_3066_ == 0)
{
lean_object* v___x_3067_; 
lean_dec_ref(v___x_3065_);
lean_dec_ref(v_arg_3064_);
lean_dec_ref(v_inst_3046_);
lean_dec_ref(v_p_3045_);
lean_inc(v_a_3057_);
lean_inc_ref(v_a_3056_);
lean_inc(v_a_3055_);
lean_inc_ref(v_a_3054_);
lean_inc(v_a_3053_);
lean_inc_ref(v_a_3052_);
lean_inc(v_a_3051_);
lean_inc_ref(v_a_3050_);
lean_inc(v_a_3049_);
v___x_3067_ = lean_apply_10(v_fallback_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_, lean_box(0));
return v___x_3067_;
}
else
{
lean_object* v_arg_3068_; lean_object* v___x_3069_; uint8_t v___x_3070_; 
v_arg_3068_ = lean_ctor_get(v___x_3065_, 1);
lean_inc_ref(v_arg_3068_);
v___x_3069_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3065_);
v___x_3070_ = l_Lean_Expr_isApp(v___x_3069_);
if (v___x_3070_ == 0)
{
lean_object* v___x_3071_; 
lean_dec_ref(v___x_3069_);
lean_dec_ref(v_arg_3068_);
lean_dec_ref(v_arg_3064_);
lean_dec_ref(v_inst_3046_);
lean_dec_ref(v_p_3045_);
lean_inc(v_a_3057_);
lean_inc_ref(v_a_3056_);
lean_inc(v_a_3055_);
lean_inc_ref(v_a_3054_);
lean_inc(v_a_3053_);
lean_inc_ref(v_a_3052_);
lean_inc(v_a_3051_);
lean_inc_ref(v_a_3050_);
lean_inc(v_a_3049_);
v___x_3071_ = lean_apply_10(v_fallback_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_, lean_box(0));
return v___x_3071_;
}
else
{
lean_object* v___x_3072_; lean_object* v___x_3073_; uint8_t v___x_3074_; 
v___x_3072_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3069_);
v___x_3073_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_3074_ = l_Lean_Expr_isConstOf(v___x_3072_, v___x_3073_);
lean_dec_ref(v___x_3072_);
if (v___x_3074_ == 0)
{
lean_object* v___x_3075_; 
lean_dec_ref(v_arg_3068_);
lean_dec_ref(v_arg_3064_);
lean_dec_ref(v_inst_3046_);
lean_dec_ref(v_p_3045_);
lean_inc(v_a_3057_);
lean_inc_ref(v_a_3056_);
lean_inc(v_a_3055_);
lean_inc_ref(v_a_3054_);
lean_inc(v_a_3053_);
lean_inc_ref(v_a_3052_);
lean_inc(v_a_3051_);
lean_inc_ref(v_a_3050_);
lean_inc(v_a_3049_);
v___x_3075_ = lean_apply_10(v_fallback_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_, lean_box(0));
return v___x_3075_;
}
else
{
lean_object* v___x_3076_; 
v___x_3076_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_3068_, v_a_3055_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_a_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; uint8_t v___x_3080_; 
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_a_3077_);
lean_dec_ref_known(v___x_3076_, 1);
v___x_3078_ = l_Lean_Expr_cleanupAnnotations(v_a_3077_);
v___x_3079_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_3080_ = l_Lean_Expr_isConstOf(v___x_3078_, v___x_3079_);
if (v___x_3080_ == 0)
{
lean_object* v___x_3081_; uint8_t v___x_3082_; 
v___x_3081_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_3082_ = l_Lean_Expr_isConstOf(v___x_3078_, v___x_3081_);
lean_dec_ref(v___x_3078_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; 
lean_dec_ref(v_arg_3064_);
lean_dec_ref(v_inst_3046_);
lean_dec_ref(v_p_3045_);
lean_inc(v_a_3057_);
lean_inc_ref(v_a_3056_);
lean_inc(v_a_3055_);
lean_inc_ref(v_a_3054_);
lean_inc(v_a_3053_);
lean_inc_ref(v_a_3052_);
lean_inc(v_a_3051_);
lean_inc_ref(v_a_3050_);
lean_inc(v_a_3049_);
v___x_3083_ = lean_apply_10(v_fallback_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_, lean_box(0));
return v___x_3083_;
}
else
{
lean_object* v___x_3084_; 
lean_dec_ref(v_fallback_3048_);
v___x_3084_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_3052_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3095_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3095_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3095_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3093_; 
v___x_3089_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2);
v___x_3090_ = l_Lean_mkApp3(v___x_3089_, v_p_3045_, v_inst_3046_, v_arg_3064_);
v___x_3091_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3091_, 0, v_a_3085_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
lean_ctor_set_uint8(v___x_3091_, sizeof(void*)*2, v___x_3080_);
lean_ctor_set_uint8(v___x_3091_, sizeof(void*)*2 + 1, v___x_3080_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v___x_3091_);
v___x_3093_ = v___x_3087_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3091_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec_ref(v_arg_3064_);
lean_dec_ref(v_inst_3046_);
lean_dec_ref(v_p_3045_);
v_a_3096_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3084_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3084_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
}
else
{
lean_object* v___x_3104_; 
lean_dec_ref(v___x_3078_);
lean_dec_ref(v_fallback_3048_);
v___x_3104_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_3052_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3116_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3107_ = v___x_3104_;
v_isShared_3108_ = v_isSharedCheck_3116_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3104_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3116_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3114_; 
v___x_3109_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5);
v___x_3110_ = l_Lean_mkApp3(v___x_3109_, v_p_3045_, v_inst_3046_, v_arg_3064_);
v___x_3111_ = 0;
v___x_3112_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3112_, 0, v_a_3105_);
lean_ctor_set(v___x_3112_, 1, v___x_3110_);
lean_ctor_set_uint8(v___x_3112_, sizeof(void*)*2, v___x_3111_);
lean_ctor_set_uint8(v___x_3112_, sizeof(void*)*2 + 1, v___x_3111_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 0, v___x_3112_);
v___x_3114_ = v___x_3107_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3112_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec_ref(v_arg_3064_);
lean_dec_ref(v_inst_3046_);
lean_dec_ref(v_p_3045_);
v_a_3117_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3104_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3104_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
}
else
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
lean_dec_ref(v_arg_3064_);
lean_dec_ref(v_fallback_3048_);
lean_dec_ref(v_inst_3046_);
lean_dec_ref(v_p_3045_);
v_a_3125_ = lean_ctor_get(v___x_3076_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_3076_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3076_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3128_ == 0)
{
v___x_3130_ = v___x_3127_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
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
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
lean_dec_ref(v_fallback_3048_);
lean_dec_ref(v_inst_3046_);
lean_dec_ref(v_p_3045_);
v_a_3133_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3059_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3059_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___boxed(lean_object* v_p_3141_, lean_object* v_inst_3142_, lean_object* v_instToMatch_3143_, lean_object* v_fallback_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_3141_, v_inst_3142_, v_instToMatch_3143_, v_fallback_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_, v_a_3153_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
lean_dec(v_a_3151_);
lean_dec_ref(v_a_3150_);
lean_dec(v_a_3149_);
lean_dec_ref(v_a_3148_);
lean_dec(v_a_3147_);
lean_dec_ref(v_a_3146_);
lean_dec(v_a_3145_);
return v_res_3155_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2(void){
_start:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3161_ = lean_box(0);
v___x_3162_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1));
v___x_3163_ = l_Lean_mkConst(v___x_3162_, v___x_3161_);
return v___x_3163_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5(void){
_start:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3169_ = lean_box(0);
v___x_3170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4));
v___x_3171_ = l_Lean_mkConst(v___x_3170_, v___x_3169_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(lean_object* v_p_3172_, lean_object* v_p_x27_3173_, lean_object* v_h_3174_, lean_object* v_inst_3175_, lean_object* v_inst_x27_3176_, lean_object* v_fallback_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_){
_start:
{
lean_object* v___x_3188_; 
v___x_3188_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_x27_3176_, v_a_3184_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_a_3189_; lean_object* v___x_3190_; uint8_t v___x_3191_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3189_);
lean_dec_ref_known(v___x_3188_, 1);
v___x_3190_ = l_Lean_Expr_cleanupAnnotations(v_a_3189_);
v___x_3191_ = l_Lean_Expr_isApp(v___x_3190_);
if (v___x_3191_ == 0)
{
lean_object* v___x_3192_; 
lean_dec_ref(v___x_3190_);
lean_dec_ref(v_inst_3175_);
lean_dec_ref(v_h_3174_);
lean_dec_ref(v_p_x27_3173_);
lean_dec_ref(v_p_3172_);
lean_inc(v_a_3186_);
lean_inc_ref(v_a_3185_);
lean_inc(v_a_3184_);
lean_inc_ref(v_a_3183_);
lean_inc(v_a_3182_);
lean_inc_ref(v_a_3181_);
lean_inc(v_a_3180_);
lean_inc_ref(v_a_3179_);
lean_inc(v_a_3178_);
v___x_3192_ = lean_apply_10(v_fallback_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, lean_box(0));
return v___x_3192_;
}
else
{
lean_object* v_arg_3193_; lean_object* v___x_3194_; uint8_t v___x_3195_; 
v_arg_3193_ = lean_ctor_get(v___x_3190_, 1);
lean_inc_ref(v_arg_3193_);
v___x_3194_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3190_);
v___x_3195_ = l_Lean_Expr_isApp(v___x_3194_);
if (v___x_3195_ == 0)
{
lean_object* v___x_3196_; 
lean_dec_ref(v___x_3194_);
lean_dec_ref(v_arg_3193_);
lean_dec_ref(v_inst_3175_);
lean_dec_ref(v_h_3174_);
lean_dec_ref(v_p_x27_3173_);
lean_dec_ref(v_p_3172_);
lean_inc(v_a_3186_);
lean_inc_ref(v_a_3185_);
lean_inc(v_a_3184_);
lean_inc_ref(v_a_3183_);
lean_inc(v_a_3182_);
lean_inc_ref(v_a_3181_);
lean_inc(v_a_3180_);
lean_inc_ref(v_a_3179_);
lean_inc(v_a_3178_);
v___x_3196_ = lean_apply_10(v_fallback_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, lean_box(0));
return v___x_3196_;
}
else
{
lean_object* v_arg_3197_; lean_object* v___x_3198_; uint8_t v___x_3199_; 
v_arg_3197_ = lean_ctor_get(v___x_3194_, 1);
lean_inc_ref(v_arg_3197_);
v___x_3198_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3194_);
v___x_3199_ = l_Lean_Expr_isApp(v___x_3198_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; 
lean_dec_ref(v___x_3198_);
lean_dec_ref(v_arg_3197_);
lean_dec_ref(v_arg_3193_);
lean_dec_ref(v_inst_3175_);
lean_dec_ref(v_h_3174_);
lean_dec_ref(v_p_x27_3173_);
lean_dec_ref(v_p_3172_);
lean_inc(v_a_3186_);
lean_inc_ref(v_a_3185_);
lean_inc(v_a_3184_);
lean_inc_ref(v_a_3183_);
lean_inc(v_a_3182_);
lean_inc_ref(v_a_3181_);
lean_inc(v_a_3180_);
lean_inc_ref(v_a_3179_);
lean_inc(v_a_3178_);
v___x_3200_ = lean_apply_10(v_fallback_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, lean_box(0));
return v___x_3200_;
}
else
{
lean_object* v___x_3201_; lean_object* v___x_3202_; uint8_t v___x_3203_; 
v___x_3201_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3198_);
v___x_3202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_3203_ = l_Lean_Expr_isConstOf(v___x_3201_, v___x_3202_);
lean_dec_ref(v___x_3201_);
if (v___x_3203_ == 0)
{
lean_object* v___x_3204_; 
lean_dec_ref(v_arg_3197_);
lean_dec_ref(v_arg_3193_);
lean_dec_ref(v_inst_3175_);
lean_dec_ref(v_h_3174_);
lean_dec_ref(v_p_x27_3173_);
lean_dec_ref(v_p_3172_);
lean_inc(v_a_3186_);
lean_inc_ref(v_a_3185_);
lean_inc(v_a_3184_);
lean_inc_ref(v_a_3183_);
lean_inc(v_a_3182_);
lean_inc_ref(v_a_3181_);
lean_inc(v_a_3180_);
lean_inc_ref(v_a_3179_);
lean_inc(v_a_3178_);
v___x_3204_ = lean_apply_10(v_fallback_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, lean_box(0));
return v___x_3204_;
}
else
{
lean_object* v___x_3205_; 
v___x_3205_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_3197_, v_a_3184_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_a_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; uint8_t v___x_3209_; 
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
lean_inc(v_a_3206_);
lean_dec_ref_known(v___x_3205_, 1);
v___x_3207_ = l_Lean_Expr_cleanupAnnotations(v_a_3206_);
v___x_3208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_3209_ = l_Lean_Expr_isConstOf(v___x_3207_, v___x_3208_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; uint8_t v___x_3211_; 
v___x_3210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_3211_ = l_Lean_Expr_isConstOf(v___x_3207_, v___x_3210_);
lean_dec_ref(v___x_3207_);
if (v___x_3211_ == 0)
{
lean_object* v___x_3212_; 
lean_dec_ref(v_arg_3193_);
lean_dec_ref(v_inst_3175_);
lean_dec_ref(v_h_3174_);
lean_dec_ref(v_p_x27_3173_);
lean_dec_ref(v_p_3172_);
lean_inc(v_a_3186_);
lean_inc_ref(v_a_3185_);
lean_inc(v_a_3184_);
lean_inc_ref(v_a_3183_);
lean_inc(v_a_3182_);
lean_inc_ref(v_a_3181_);
lean_inc(v_a_3180_);
lean_inc_ref(v_a_3179_);
lean_inc(v_a_3178_);
v___x_3212_ = lean_apply_10(v_fallback_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, lean_box(0));
return v___x_3212_;
}
else
{
lean_object* v___x_3213_; 
lean_dec_ref(v_fallback_3177_);
v___x_3213_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_3181_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3224_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3216_ = v___x_3213_;
v_isShared_3217_ = v_isSharedCheck_3224_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3213_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3224_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3222_; 
v___x_3218_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2);
v___x_3219_ = l_Lean_mkApp5(v___x_3218_, v_p_3172_, v_p_x27_3173_, v_h_3174_, v_inst_3175_, v_arg_3193_);
v___x_3220_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3220_, 0, v_a_3214_);
lean_ctor_set(v___x_3220_, 1, v___x_3219_);
lean_ctor_set_uint8(v___x_3220_, sizeof(void*)*2, v___x_3209_);
lean_ctor_set_uint8(v___x_3220_, sizeof(void*)*2 + 1, v___x_3209_);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 0, v___x_3220_);
v___x_3222_ = v___x_3216_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v___x_3220_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
else
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3232_; 
lean_dec_ref(v_arg_3193_);
lean_dec_ref(v_inst_3175_);
lean_dec_ref(v_h_3174_);
lean_dec_ref(v_p_x27_3173_);
lean_dec_ref(v_p_3172_);
v_a_3225_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3227_ = v___x_3213_;
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3213_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3230_; 
if (v_isShared_3228_ == 0)
{
v___x_3230_ = v___x_3227_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3225_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
}
}
else
{
lean_object* v___x_3233_; 
lean_dec_ref(v___x_3207_);
lean_dec_ref(v_fallback_3177_);
v___x_3233_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_3181_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3245_; 
v_a_3234_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3236_ = v___x_3233_;
v_isShared_3237_ = v_isSharedCheck_3245_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3233_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3245_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; uint8_t v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3243_; 
v___x_3238_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5);
v___x_3239_ = l_Lean_mkApp5(v___x_3238_, v_p_3172_, v_p_x27_3173_, v_h_3174_, v_inst_3175_, v_arg_3193_);
v___x_3240_ = 0;
v___x_3241_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3241_, 0, v_a_3234_);
lean_ctor_set(v___x_3241_, 1, v___x_3239_);
lean_ctor_set_uint8(v___x_3241_, sizeof(void*)*2, v___x_3240_);
lean_ctor_set_uint8(v___x_3241_, sizeof(void*)*2 + 1, v___x_3240_);
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 0, v___x_3241_);
v___x_3243_ = v___x_3236_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3241_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
else
{
lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3253_; 
lean_dec_ref(v_arg_3193_);
lean_dec_ref(v_inst_3175_);
lean_dec_ref(v_h_3174_);
lean_dec_ref(v_p_x27_3173_);
lean_dec_ref(v_p_3172_);
v_a_3246_ = lean_ctor_get(v___x_3233_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3248_ = v___x_3233_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3233_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_a_3246_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
}
else
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_dec_ref(v_arg_3193_);
lean_dec_ref(v_fallback_3177_);
lean_dec_ref(v_inst_3175_);
lean_dec_ref(v_h_3174_);
lean_dec_ref(v_p_x27_3173_);
lean_dec_ref(v_p_3172_);
v_a_3254_ = lean_ctor_get(v___x_3205_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3205_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3205_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
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
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_dec_ref(v_fallback_3177_);
lean_dec_ref(v_inst_3175_);
lean_dec_ref(v_h_3174_);
lean_dec_ref(v_p_x27_3173_);
lean_dec_ref(v_p_3172_);
v_a_3262_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3188_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3188_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___boxed(lean_object* v_p_3270_, lean_object* v_p_x27_3271_, lean_object* v_h_3272_, lean_object* v_inst_3273_, lean_object* v_inst_x27_3274_, lean_object* v_fallback_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_3270_, v_p_x27_3271_, v_h_3272_, v_inst_3273_, v_inst_x27_3274_, v_fallback_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_);
lean_dec(v_a_3284_);
lean_dec_ref(v_a_3283_);
lean_dec(v_a_3282_);
lean_dec_ref(v_a_3281_);
lean_dec(v_a_3280_);
lean_dec_ref(v_a_3279_);
lean_dec(v_a_3278_);
lean_dec_ref(v_a_3277_);
lean_dec(v_a_3276_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(lean_object* v_p_3287_, lean_object* v_inst_3288_, lean_object* v_fallback_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_){
_start:
{
lean_object* v___x_3300_; uint8_t v___x_3301_; lean_object* v___x_3302_; lean_object* v___f_3303_; lean_object* v___x_3304_; 
v___x_3300_ = lean_unsigned_to_nat(0u);
v___x_3301_ = 5;
v___x_3302_ = lean_box(v___x_3301_);
lean_inc_ref(v_inst_3288_);
v___f_3303_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3303_, 0, v___x_3302_);
lean_closure_set(v___f_3303_, 1, v_inst_3288_);
lean_closure_set(v___f_3303_, 2, v___x_3300_);
v___x_3304_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_3303_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_a_3305_);
lean_dec_ref_known(v___x_3304_, 1);
if (lean_obj_tag(v_a_3305_) == 0)
{
lean_object* v___x_3306_; 
lean_inc(v_a_3298_);
lean_inc_ref(v_a_3297_);
lean_inc(v_a_3296_);
lean_inc_ref(v_a_3295_);
lean_inc(v_a_3294_);
lean_inc_ref(v_a_3293_);
lean_inc(v_a_3292_);
lean_inc_ref(v_a_3291_);
lean_inc(v_a_3290_);
lean_inc_ref(v_inst_3288_);
v___x_3306_ = lean_sym_simp(v_inst_3288_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3307_);
lean_dec_ref_known(v___x_3306_, 1);
if (lean_obj_tag(v_a_3307_) == 0)
{
uint8_t v_contextDependent_3308_; lean_object* v___x_3309_; 
v_contextDependent_3308_ = lean_ctor_get_uint8(v_a_3307_, 1);
lean_dec_ref_known(v_a_3307_, 0);
lean_inc_ref(v_inst_3288_);
v___x_3309_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_3287_, v_inst_3288_, v_inst_3288_, v_fallback_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_a_3310_; uint8_t v___y_3312_; 
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
lean_inc(v_a_3310_);
if (v_contextDependent_3308_ == 0)
{
lean_dec(v_a_3310_);
return v___x_3309_;
}
else
{
if (lean_obj_tag(v_a_3310_) == 0)
{
uint8_t v_contextDependent_3322_; 
v_contextDependent_3322_ = lean_ctor_get_uint8(v_a_3310_, 1);
v___y_3312_ = v_contextDependent_3322_;
goto v___jp_3311_;
}
else
{
uint8_t v_contextDependent_3323_; 
v_contextDependent_3323_ = lean_ctor_get_uint8(v_a_3310_, sizeof(void*)*2 + 1);
v___y_3312_ = v_contextDependent_3323_;
goto v___jp_3311_;
}
}
v___jp_3311_:
{
if (v___y_3312_ == 0)
{
lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3320_; 
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3320_ == 0)
{
lean_object* v_unused_3321_; 
v_unused_3321_ = lean_ctor_get(v___x_3309_, 0);
lean_dec(v_unused_3321_);
v___x_3314_ = v___x_3309_;
v_isShared_3315_ = v_isSharedCheck_3320_;
goto v_resetjp_3313_;
}
else
{
lean_dec(v___x_3309_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3320_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3316_; lean_object* v___x_3318_; 
v___x_3316_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3310_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 0, v___x_3316_);
v___x_3318_ = v___x_3314_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3316_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
else
{
lean_dec(v_a_3310_);
return v___x_3309_;
}
}
}
else
{
return v___x_3309_;
}
}
else
{
lean_object* v_e_x27_3324_; uint8_t v_contextDependent_3325_; lean_object* v___x_3326_; 
v_e_x27_3324_ = lean_ctor_get(v_a_3307_, 0);
lean_inc_ref(v_e_x27_3324_);
v_contextDependent_3325_ = lean_ctor_get_uint8(v_a_3307_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_3307_, 2);
v___x_3326_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_3287_, v_inst_3288_, v_e_x27_3324_, v_fallback_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; uint8_t v___y_3329_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
if (v_contextDependent_3325_ == 0)
{
lean_dec(v_a_3327_);
return v___x_3326_;
}
else
{
if (lean_obj_tag(v_a_3327_) == 0)
{
uint8_t v_contextDependent_3339_; 
v_contextDependent_3339_ = lean_ctor_get_uint8(v_a_3327_, 1);
v___y_3329_ = v_contextDependent_3339_;
goto v___jp_3328_;
}
else
{
uint8_t v_contextDependent_3340_; 
v_contextDependent_3340_ = lean_ctor_get_uint8(v_a_3327_, sizeof(void*)*2 + 1);
v___y_3329_ = v_contextDependent_3340_;
goto v___jp_3328_;
}
}
v___jp_3328_:
{
if (v___y_3329_ == 0)
{
lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3337_; 
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3337_ == 0)
{
lean_object* v_unused_3338_; 
v_unused_3338_ = lean_ctor_get(v___x_3326_, 0);
lean_dec(v_unused_3338_);
v___x_3331_ = v___x_3326_;
v_isShared_3332_ = v_isSharedCheck_3337_;
goto v_resetjp_3330_;
}
else
{
lean_dec(v___x_3326_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3337_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; lean_object* v___x_3335_; 
v___x_3333_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3327_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v___x_3333_);
v___x_3335_ = v___x_3331_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3333_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
else
{
lean_dec(v_a_3327_);
return v___x_3326_;
}
}
}
else
{
return v___x_3326_;
}
}
}
else
{
lean_dec_ref(v_fallback_3289_);
lean_dec_ref(v_inst_3288_);
lean_dec_ref(v_p_3287_);
return v___x_3306_;
}
}
else
{
lean_object* v_val_3341_; lean_object* v___x_3342_; 
lean_dec_ref(v_fallback_3289_);
lean_dec_ref(v_inst_3288_);
lean_dec_ref(v_p_3287_);
v_val_3341_ = lean_ctor_get(v_a_3305_, 0);
lean_inc(v_val_3341_);
lean_dec_ref_known(v_a_3305_, 1);
v___x_3342_ = l_Lean_Meta_Sym_shareCommonInc(v_val_3341_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3355_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3345_ = v___x_3342_;
v_isShared_3346_ = v_isSharedCheck_3355_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3342_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3355_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; uint8_t v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3353_; 
v___x_3347_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8);
v___x_3348_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10);
lean_inc(v_a_3343_);
v___x_3349_ = l_Lean_mkAppB(v___x_3347_, v___x_3348_, v_a_3343_);
v___x_3350_ = 0;
v___x_3351_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3351_, 0, v_a_3343_);
lean_ctor_set(v___x_3351_, 1, v___x_3349_);
lean_ctor_set_uint8(v___x_3351_, sizeof(void*)*2, v___x_3350_);
lean_ctor_set_uint8(v___x_3351_, sizeof(void*)*2 + 1, v___x_3350_);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 0, v___x_3351_);
v___x_3353_ = v___x_3345_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v___x_3351_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
else
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3363_; 
v_a_3356_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3363_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3363_ == 0)
{
v___x_3358_ = v___x_3342_;
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3342_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3363_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3361_; 
if (v_isShared_3359_ == 0)
{
v___x_3361_ = v___x_3358_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3362_; 
v_reuseFailAlloc_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3362_, 0, v_a_3356_);
v___x_3361_ = v_reuseFailAlloc_3362_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
return v___x_3361_;
}
}
}
}
}
else
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3371_; 
lean_dec_ref(v_fallback_3289_);
lean_dec_ref(v_inst_3288_);
lean_dec_ref(v_p_3287_);
v_a_3364_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3371_ == 0)
{
v___x_3366_ = v___x_3304_;
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3304_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3371_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3367_ == 0)
{
v___x_3369_ = v___x_3366_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_a_3364_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable___boxed(lean_object* v_p_3372_, lean_object* v_inst_3373_, lean_object* v_fallback_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_){
_start:
{
lean_object* v_res_3385_; 
v_res_3385_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(v_p_3372_, v_inst_3373_, v_fallback_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
lean_dec(v_a_3383_);
lean_dec_ref(v_a_3382_);
lean_dec(v_a_3381_);
lean_dec_ref(v_a_3380_);
lean_dec(v_a_3379_);
lean_dec_ref(v_a_3378_);
lean_dec(v_a_3377_);
lean_dec_ref(v_a_3376_);
lean_dec(v_a_3375_);
return v_res_3385_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__2(void){
_start:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3391_ = lean_box(0);
v___x_3392_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__1));
v___x_3393_ = l_Lean_mkConst(v___x_3392_, v___x_3391_);
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(lean_object* v_p_3394_, lean_object* v_p_x27_3395_, lean_object* v_h_3396_, lean_object* v_inst_3397_, lean_object* v_inst_x27_3398_, lean_object* v_fallback_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_){
_start:
{
lean_object* v___x_3410_; uint8_t v___x_3411_; lean_object* v___x_3412_; lean_object* v___f_3413_; lean_object* v___x_3414_; 
v___x_3410_ = lean_unsigned_to_nat(0u);
v___x_3411_ = 5;
v___x_3412_ = lean_box(v___x_3411_);
lean_inc_ref(v_inst_x27_3398_);
v___f_3413_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3413_, 0, v___x_3412_);
lean_closure_set(v___f_3413_, 1, v_inst_x27_3398_);
lean_closure_set(v___f_3413_, 2, v___x_3410_);
v___x_3414_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_3413_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
lean_inc(v_a_3415_);
lean_dec_ref_known(v___x_3414_, 1);
if (lean_obj_tag(v_a_3415_) == 0)
{
lean_object* v___x_3416_; 
lean_inc(v_a_3408_);
lean_inc_ref(v_a_3407_);
lean_inc(v_a_3406_);
lean_inc_ref(v_a_3405_);
lean_inc(v_a_3404_);
lean_inc_ref(v_a_3403_);
lean_inc(v_a_3402_);
lean_inc_ref(v_a_3401_);
lean_inc(v_a_3400_);
lean_inc_ref(v_inst_x27_3398_);
v___x_3416_ = lean_sym_simp(v_inst_x27_3398_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v_a_3417_; 
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc(v_a_3417_);
lean_dec_ref_known(v___x_3416_, 1);
if (lean_obj_tag(v_a_3417_) == 0)
{
uint8_t v_contextDependent_3418_; lean_object* v___x_3419_; 
v_contextDependent_3418_ = lean_ctor_get_uint8(v_a_3417_, 1);
lean_dec_ref_known(v_a_3417_, 0);
v___x_3419_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_3394_, v_p_x27_3395_, v_h_3396_, v_inst_3397_, v_inst_x27_3398_, v_fallback_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_object* v_a_3420_; uint8_t v___y_3422_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc(v_a_3420_);
if (v_contextDependent_3418_ == 0)
{
lean_dec(v_a_3420_);
return v___x_3419_;
}
else
{
if (lean_obj_tag(v_a_3420_) == 0)
{
uint8_t v_contextDependent_3432_; 
v_contextDependent_3432_ = lean_ctor_get_uint8(v_a_3420_, 1);
v___y_3422_ = v_contextDependent_3432_;
goto v___jp_3421_;
}
else
{
uint8_t v_contextDependent_3433_; 
v_contextDependent_3433_ = lean_ctor_get_uint8(v_a_3420_, sizeof(void*)*2 + 1);
v___y_3422_ = v_contextDependent_3433_;
goto v___jp_3421_;
}
}
v___jp_3421_:
{
if (v___y_3422_ == 0)
{
lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3430_; 
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3430_ == 0)
{
lean_object* v_unused_3431_; 
v_unused_3431_ = lean_ctor_get(v___x_3419_, 0);
lean_dec(v_unused_3431_);
v___x_3424_ = v___x_3419_;
v_isShared_3425_ = v_isSharedCheck_3430_;
goto v_resetjp_3423_;
}
else
{
lean_dec(v___x_3419_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3430_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3426_; lean_object* v___x_3428_; 
v___x_3426_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3420_);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 0, v___x_3426_);
v___x_3428_ = v___x_3424_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v___x_3426_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
else
{
lean_dec(v_a_3420_);
return v___x_3419_;
}
}
}
else
{
return v___x_3419_;
}
}
else
{
lean_object* v_e_x27_3434_; uint8_t v_contextDependent_3435_; lean_object* v___x_3436_; 
lean_dec_ref(v_inst_x27_3398_);
v_e_x27_3434_ = lean_ctor_get(v_a_3417_, 0);
lean_inc_ref(v_e_x27_3434_);
v_contextDependent_3435_ = lean_ctor_get_uint8(v_a_3417_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_3417_, 2);
v___x_3436_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_3394_, v_p_x27_3395_, v_h_3396_, v_inst_3397_, v_e_x27_3434_, v_fallback_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_a_3437_; uint8_t v___y_3439_; 
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_a_3437_);
if (v_contextDependent_3435_ == 0)
{
lean_dec(v_a_3437_);
return v___x_3436_;
}
else
{
if (lean_obj_tag(v_a_3437_) == 0)
{
uint8_t v_contextDependent_3449_; 
v_contextDependent_3449_ = lean_ctor_get_uint8(v_a_3437_, 1);
v___y_3439_ = v_contextDependent_3449_;
goto v___jp_3438_;
}
else
{
uint8_t v_contextDependent_3450_; 
v_contextDependent_3450_ = lean_ctor_get_uint8(v_a_3437_, sizeof(void*)*2 + 1);
v___y_3439_ = v_contextDependent_3450_;
goto v___jp_3438_;
}
}
v___jp_3438_:
{
if (v___y_3439_ == 0)
{
lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3447_; 
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3447_ == 0)
{
lean_object* v_unused_3448_; 
v_unused_3448_ = lean_ctor_get(v___x_3436_, 0);
lean_dec(v_unused_3448_);
v___x_3441_ = v___x_3436_;
v_isShared_3442_ = v_isSharedCheck_3447_;
goto v_resetjp_3440_;
}
else
{
lean_dec(v___x_3436_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3447_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3443_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3437_);
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 0, v___x_3443_);
v___x_3445_ = v___x_3441_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
else
{
lean_dec(v_a_3437_);
return v___x_3436_;
}
}
}
else
{
return v___x_3436_;
}
}
}
else
{
lean_dec_ref(v_fallback_3399_);
lean_dec_ref(v_inst_x27_3398_);
lean_dec_ref(v_inst_3397_);
lean_dec_ref(v_h_3396_);
lean_dec_ref(v_p_x27_3395_);
lean_dec_ref(v_p_3394_);
return v___x_3416_;
}
}
else
{
lean_object* v_val_3451_; lean_object* v___x_3452_; 
lean_dec_ref(v_fallback_3399_);
v_val_3451_ = lean_ctor_get(v_a_3415_, 0);
lean_inc(v_val_3451_);
lean_dec_ref_known(v_a_3415_, 1);
v___x_3452_ = l_Lean_Meta_Sym_shareCommonInc(v_val_3451_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3467_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3455_ = v___x_3452_;
v_isShared_3456_ = v_isSharedCheck_3467_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3452_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3467_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; uint8_t v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3465_; 
v___x_3457_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8);
v___x_3458_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10);
lean_inc_n(v_a_3453_, 2);
v___x_3459_ = l_Lean_mkAppB(v___x_3457_, v___x_3458_, v_a_3453_);
v___x_3460_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__2);
v___x_3461_ = l_Lean_mkApp7(v___x_3460_, v_p_3394_, v_p_x27_3395_, v_h_3396_, v_inst_3397_, v_inst_x27_3398_, v_a_3453_, v___x_3459_);
v___x_3462_ = 0;
v___x_3463_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3463_, 0, v_a_3453_);
lean_ctor_set(v___x_3463_, 1, v___x_3461_);
lean_ctor_set_uint8(v___x_3463_, sizeof(void*)*2, v___x_3462_);
lean_ctor_set_uint8(v___x_3463_, sizeof(void*)*2 + 1, v___x_3462_);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v___x_3463_);
v___x_3465_ = v___x_3455_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
else
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
lean_dec_ref(v_inst_x27_3398_);
lean_dec_ref(v_inst_3397_);
lean_dec_ref(v_h_3396_);
lean_dec_ref(v_p_x27_3395_);
lean_dec_ref(v_p_3394_);
v_a_3468_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3470_ = v___x_3452_;
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3452_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3468_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
}
else
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
lean_dec_ref(v_fallback_3399_);
lean_dec_ref(v_inst_x27_3398_);
lean_dec_ref(v_inst_3397_);
lean_dec_ref(v_h_3396_);
lean_dec_ref(v_p_x27_3395_);
lean_dec_ref(v_p_3394_);
v_a_3476_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3478_ = v___x_3414_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3414_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3481_; 
if (v_isShared_3479_ == 0)
{
v___x_3481_ = v___x_3478_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3476_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___boxed(lean_object* v_p_3484_, lean_object* v_p_x27_3485_, lean_object* v_h_3486_, lean_object* v_inst_3487_, lean_object* v_inst_x27_3488_, lean_object* v_fallback_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(v_p_3484_, v_p_x27_3485_, v_h_3486_, v_inst_3487_, v_inst_x27_3488_, v_fallback_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_);
lean_dec(v_a_3498_);
lean_dec_ref(v_a_3497_);
lean_dec(v_a_3496_);
lean_dec_ref(v_a_3495_);
lean_dec(v_a_3494_);
lean_dec_ref(v_a_3493_);
lean_dec(v_a_3492_);
lean_dec_ref(v_a_3491_);
lean_dec(v_a_3490_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2(lean_object* v___x_3502_, lean_object* v_e_x27_3503_, lean_object* v_snd_3504_, lean_object* v___x_3505_, lean_object* v___x_3506_, lean_object* v___x_3507_, lean_object* v_arg_3508_, lean_object* v_proof_3509_, lean_object* v_arg_3510_, uint8_t v___x_3511_, uint8_t v_contextDependent_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
lean_object* v___x_3523_; 
v___x_3523_ = l_Lean_Meta_Sym_shareCommon(v___x_3502_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; lean_object* v___x_3525_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3524_);
lean_dec_ref_known(v___x_3523_, 1);
lean_inc_ref(v_snd_3504_);
lean_inc_ref(v_e_x27_3503_);
v___x_3525_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg(v_a_3524_, v_e_x27_3503_, v_snd_3504_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3538_; 
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3528_ = v___x_3525_;
v_isShared_3529_ = v_isSharedCheck_3538_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3525_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3538_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3536_; 
v___x_3530_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2___closed__0));
v___x_3531_ = l_Lean_Name_mkStr3(v___x_3505_, v___x_3506_, v___x_3530_);
v___x_3532_ = l_Lean_mkConst(v___x_3531_, v___x_3507_);
v___x_3533_ = l_Lean_mkApp5(v___x_3532_, v_arg_3508_, v_e_x27_3503_, v_proof_3509_, v_arg_3510_, v_snd_3504_);
v___x_3534_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3534_, 0, v_a_3526_);
lean_ctor_set(v___x_3534_, 1, v___x_3533_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*2, v___x_3511_);
lean_ctor_set_uint8(v___x_3534_, sizeof(void*)*2 + 1, v_contextDependent_3512_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3534_);
v___x_3536_ = v___x_3528_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3534_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec_ref(v_arg_3510_);
lean_dec_ref(v_proof_3509_);
lean_dec_ref(v_arg_3508_);
lean_dec(v___x_3507_);
lean_dec_ref(v___x_3506_);
lean_dec_ref(v___x_3505_);
lean_dec_ref(v_snd_3504_);
lean_dec_ref(v_e_x27_3503_);
v_a_3539_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3525_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3525_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
else
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3554_; 
lean_dec_ref(v_arg_3510_);
lean_dec_ref(v_proof_3509_);
lean_dec_ref(v_arg_3508_);
lean_dec(v___x_3507_);
lean_dec_ref(v___x_3506_);
lean_dec_ref(v___x_3505_);
lean_dec_ref(v_snd_3504_);
lean_dec_ref(v_e_x27_3503_);
v_a_3547_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___x_3523_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3523_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3552_; 
if (v_isShared_3550_ == 0)
{
v___x_3552_ = v___x_3549_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_a_3547_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2___boxed(lean_object** _args){
lean_object* v___x_3555_ = _args[0];
lean_object* v_e_x27_3556_ = _args[1];
lean_object* v_snd_3557_ = _args[2];
lean_object* v___x_3558_ = _args[3];
lean_object* v___x_3559_ = _args[4];
lean_object* v___x_3560_ = _args[5];
lean_object* v_arg_3561_ = _args[6];
lean_object* v_proof_3562_ = _args[7];
lean_object* v_arg_3563_ = _args[8];
lean_object* v___x_3564_ = _args[9];
lean_object* v_contextDependent_3565_ = _args[10];
lean_object* v___y_3566_ = _args[11];
lean_object* v___y_3567_ = _args[12];
lean_object* v___y_3568_ = _args[13];
lean_object* v___y_3569_ = _args[14];
lean_object* v___y_3570_ = _args[15];
lean_object* v___y_3571_ = _args[16];
lean_object* v___y_3572_ = _args[17];
lean_object* v___y_3573_ = _args[18];
lean_object* v___y_3574_ = _args[19];
lean_object* v___y_3575_ = _args[20];
_start:
{
uint8_t v___x_20258__boxed_3576_; uint8_t v_contextDependent_20259__boxed_3577_; lean_object* v_res_3578_; 
v___x_20258__boxed_3576_ = lean_unbox(v___x_3564_);
v_contextDependent_20259__boxed_3577_ = lean_unbox(v_contextDependent_3565_);
v_res_3578_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2(v___x_3555_, v_e_x27_3556_, v_snd_3557_, v___x_3558_, v___x_3559_, v___x_3560_, v_arg_3561_, v_proof_3562_, v_arg_3563_, v___x_20258__boxed_3576_, v_contextDependent_20259__boxed_3577_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v___y_3567_);
lean_dec(v___y_3566_);
return v_res_3578_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3582_ = lean_box(0);
v___x_3583_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1));
v___x_3584_ = l_Lean_mkConst(v___x_3583_, v___x_3582_);
return v___x_3584_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3588_ = lean_box(0);
v___x_3589_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4));
v___x_3590_ = l_Lean_mkConst(v___x_3589_, v___x_3588_);
return v___x_3590_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3596_ = lean_box(0);
v___x_3597_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7));
v___x_3598_ = l_Lean_mkConst(v___x_3597_, v___x_3596_);
return v___x_3598_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11(void){
_start:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3604_ = lean_box(0);
v___x_3605_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10));
v___x_3606_ = l_Lean_mkConst(v___x_3605_, v___x_3604_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0(uint8_t v___x_3607_, lean_object* v_e_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v___x_3622_; uint8_t v___x_3623_; 
v___x_3622_ = l_Lean_Expr_cleanupAnnotations(v_e_3608_);
v___x_3623_ = l_Lean_Expr_isApp(v___x_3622_);
if (v___x_3623_ == 0)
{
lean_dec_ref(v___x_3622_);
goto v___jp_3619_;
}
else
{
lean_object* v_arg_3624_; lean_object* v___x_3625_; uint8_t v___x_3626_; 
v_arg_3624_ = lean_ctor_get(v___x_3622_, 1);
lean_inc_ref(v_arg_3624_);
v___x_3625_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3622_);
v___x_3626_ = l_Lean_Expr_isApp(v___x_3625_);
if (v___x_3626_ == 0)
{
lean_dec_ref(v___x_3625_);
lean_dec_ref(v_arg_3624_);
goto v___jp_3619_;
}
else
{
lean_object* v_arg_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; uint8_t v___x_3632_; 
v_arg_3627_ = lean_ctor_get(v___x_3625_, 1);
lean_inc_ref(v_arg_3627_);
v___x_3628_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3625_);
v___x_3629_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0___closed__0));
v___x_3630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__0));
v___x_3631_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__1));
v___x_3632_ = l_Lean_Expr_isConstOf(v___x_3628_, v___x_3631_);
lean_dec_ref(v___x_3628_);
if (v___x_3632_ == 0)
{
lean_dec_ref(v_arg_3627_);
lean_dec_ref(v_arg_3624_);
goto v___jp_3619_;
}
else
{
lean_object* v___x_3633_; 
lean_inc(v___y_3617_);
lean_inc_ref(v___y_3616_);
lean_inc(v___y_3615_);
lean_inc_ref(v___y_3614_);
lean_inc(v___y_3613_);
lean_inc_ref(v___y_3612_);
lean_inc(v___y_3611_);
lean_inc_ref(v___y_3610_);
lean_inc(v___y_3609_);
lean_inc_ref(v_arg_3627_);
v___x_3633_ = lean_sym_simp(v_arg_3627_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref_known(v___x_3633_, 1);
if (lean_obj_tag(v_a_3634_) == 0)
{
uint8_t v_contextDependent_3635_; lean_object* v___x_3636_; 
v_contextDependent_3635_ = lean_ctor_get_uint8(v_a_3634_, 1);
lean_dec_ref_known(v_a_3634_, 0);
v___x_3636_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_3627_, v___y_3612_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; uint8_t v___x_3638_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_a_3637_);
lean_dec_ref_known(v___x_3636_, 1);
v___x_3638_ = lean_unbox(v_a_3637_);
if (v___x_3638_ == 0)
{
lean_object* v___x_3639_; 
v___x_3639_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_3627_, v___y_3612_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3640_; uint8_t v___x_3641_; 
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_a_3640_);
lean_dec_ref_known(v___x_3639_, 1);
v___x_3641_ = lean_unbox(v_a_3640_);
lean_dec(v_a_3640_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3642_; lean_object* v___f_3643_; lean_object* v___x_3644_; 
lean_dec(v_a_3637_);
v___x_3642_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_3632_, v_contextDependent_3635_);
v___f_3643_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_3643_, 0, v___x_3642_);
v___x_3644_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(v_arg_3627_, v_arg_3624_, v___f_3643_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
return v___x_3644_;
}
else
{
lean_object* v___x_3645_; 
lean_dec_ref(v_arg_3627_);
v___x_3645_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_3612_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3657_; 
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3648_ = v___x_3645_;
v_isShared_3649_ = v_isSharedCheck_3657_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3645_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3657_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; uint8_t v___x_3653_; lean_object* v___x_3655_; 
v___x_3650_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2);
v___x_3651_ = l_Lean_Expr_app___override(v___x_3650_, v_arg_3624_);
v___x_3652_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3652_, 0, v_a_3646_);
lean_ctor_set(v___x_3652_, 1, v___x_3651_);
v___x_3653_ = lean_unbox(v_a_3637_);
lean_dec(v_a_3637_);
lean_ctor_set_uint8(v___x_3652_, sizeof(void*)*2, v___x_3653_);
lean_ctor_set_uint8(v___x_3652_, sizeof(void*)*2 + 1, v_contextDependent_3635_);
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 0, v___x_3652_);
v___x_3655_ = v___x_3648_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v___x_3652_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
else
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3665_; 
lean_dec(v_a_3637_);
lean_dec_ref(v_arg_3624_);
v_a_3658_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3660_ = v___x_3645_;
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3645_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3663_; 
if (v_isShared_3661_ == 0)
{
v___x_3663_ = v___x_3660_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3658_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
}
else
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
lean_dec(v_a_3637_);
lean_dec_ref(v_arg_3627_);
lean_dec_ref(v_arg_3624_);
v_a_3666_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3668_ = v___x_3639_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3639_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3669_ == 0)
{
v___x_3671_ = v___x_3668_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_a_3666_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
else
{
lean_object* v___x_3674_; 
lean_dec(v_a_3637_);
lean_dec_ref(v_arg_3627_);
v___x_3674_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_3612_);
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3685_; 
v_a_3675_ = lean_ctor_get(v___x_3674_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3674_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3677_ = v___x_3674_;
v_isShared_3678_ = v_isSharedCheck_3685_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3674_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3685_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3683_; 
v___x_3679_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5);
v___x_3680_ = l_Lean_Expr_app___override(v___x_3679_, v_arg_3624_);
v___x_3681_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3681_, 0, v_a_3675_);
lean_ctor_set(v___x_3681_, 1, v___x_3680_);
lean_ctor_set_uint8(v___x_3681_, sizeof(void*)*2, v___x_3607_);
lean_ctor_set_uint8(v___x_3681_, sizeof(void*)*2 + 1, v_contextDependent_3635_);
if (v_isShared_3678_ == 0)
{
lean_ctor_set(v___x_3677_, 0, v___x_3681_);
v___x_3683_ = v___x_3677_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3681_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
lean_dec_ref(v_arg_3624_);
v_a_3686_ = lean_ctor_get(v___x_3674_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3674_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3674_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3674_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
}
else
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
lean_dec_ref(v_arg_3627_);
lean_dec_ref(v_arg_3624_);
v_a_3694_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3696_ = v___x_3636_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3636_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3694_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
else
{
lean_object* v_e_x27_3702_; lean_object* v_proof_3703_; uint8_t v_contextDependent_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3800_; 
v_e_x27_3702_ = lean_ctor_get(v_a_3634_, 0);
v_proof_3703_ = lean_ctor_get(v_a_3634_, 1);
v_contextDependent_3704_ = lean_ctor_get_uint8(v_a_3634_, sizeof(void*)*2 + 1);
v_isSharedCheck_3800_ = !lean_is_exclusive(v_a_3634_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3706_ = v_a_3634_;
v_isShared_3707_ = v_isSharedCheck_3800_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_proof_3703_);
lean_inc(v_e_x27_3702_);
lean_dec(v_a_3634_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3800_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3708_; 
v___x_3708_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_3702_, v___y_3612_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; uint8_t v___x_3710_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_a_3709_);
lean_dec_ref_known(v___x_3708_, 1);
v___x_3710_ = lean_unbox(v_a_3709_);
if (v___x_3710_ == 0)
{
lean_object* v___x_3711_; 
v___x_3711_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_3702_, v___y_3612_);
lean_dec_ref(v_e_x27_3702_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; uint8_t v___x_3713_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_a_3712_);
lean_dec_ref_known(v___x_3711_, 1);
v___x_3713_ = lean_unbox(v_a_3712_);
lean_dec(v_a_3712_);
if (v___x_3713_ == 0)
{
lean_object* v___x_3714_; 
lean_dec(v_a_3709_);
lean_del_object(v___x_3706_);
lean_dec_ref(v_proof_3703_);
lean_inc_ref(v_arg_3624_);
v___x_3714_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance(v_arg_3624_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_object* v_a_3715_; lean_object* v_fst_3716_; 
v_a_3715_ = lean_ctor_get(v___x_3714_, 0);
lean_inc(v_a_3715_);
lean_dec_ref_known(v___x_3714_, 1);
v_fst_3716_ = lean_ctor_get(v_a_3715_, 0);
lean_inc(v_fst_3716_);
if (lean_obj_tag(v_fst_3716_) == 0)
{
uint8_t v_contextDependent_3717_; lean_object* v___x_3718_; lean_object* v___f_3719_; lean_object* v___x_3720_; 
lean_dec(v_a_3715_);
v_contextDependent_3717_ = lean_ctor_get_uint8(v_fst_3716_, 1);
lean_dec_ref_known(v_fst_3716_, 0);
v___x_3718_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_3632_, v_contextDependent_3717_);
v___f_3719_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_3719_, 0, v___x_3718_);
v___x_3720_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(v_arg_3627_, v_arg_3624_, v___f_3719_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
return v___x_3720_;
}
else
{
lean_object* v_snd_3721_; lean_object* v_e_x27_3722_; lean_object* v_proof_3723_; uint8_t v_contextDependent_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___f_3729_; lean_object* v___x_3730_; 
v_snd_3721_ = lean_ctor_get(v_a_3715_, 1);
lean_inc_n(v_snd_3721_, 2);
lean_dec(v_a_3715_);
v_e_x27_3722_ = lean_ctor_get(v_fst_3716_, 0);
lean_inc_ref_n(v_e_x27_3722_, 2);
v_proof_3723_ = lean_ctor_get(v_fst_3716_, 1);
lean_inc_ref_n(v_proof_3723_, 2);
v_contextDependent_3724_ = lean_ctor_get_uint8(v_fst_3716_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_3716_, 2);
v___x_3725_ = lean_box(0);
v___x_3726_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2);
v___x_3727_ = lean_box(v___x_3632_);
v___x_3728_ = lean_box(v_contextDependent_3724_);
lean_inc_ref(v_arg_3624_);
lean_inc_ref(v_arg_3627_);
v___f_3729_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2___boxed), 21, 11);
lean_closure_set(v___f_3729_, 0, v___x_3726_);
lean_closure_set(v___f_3729_, 1, v_e_x27_3722_);
lean_closure_set(v___f_3729_, 2, v_snd_3721_);
lean_closure_set(v___f_3729_, 3, v___x_3629_);
lean_closure_set(v___f_3729_, 4, v___x_3630_);
lean_closure_set(v___f_3729_, 5, v___x_3725_);
lean_closure_set(v___f_3729_, 6, v_arg_3627_);
lean_closure_set(v___f_3729_, 7, v_proof_3723_);
lean_closure_set(v___f_3729_, 8, v_arg_3624_);
lean_closure_set(v___f_3729_, 9, v___x_3727_);
lean_closure_set(v___f_3729_, 10, v___x_3728_);
v___x_3730_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(v_arg_3627_, v_e_x27_3722_, v_proof_3723_, v_arg_3624_, v_snd_3721_, v___f_3729_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
return v___x_3730_;
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
lean_dec_ref(v_arg_3627_);
lean_dec_ref(v_arg_3624_);
v_a_3731_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3714_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3714_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
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
lean_object* v___x_3739_; 
v___x_3739_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_3612_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3753_; 
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3742_ = v___x_3739_;
v_isShared_3743_ = v_isSharedCheck_3753_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3739_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3753_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3747_; 
v___x_3744_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8);
v___x_3745_ = l_Lean_mkApp3(v___x_3744_, v_arg_3627_, v_arg_3624_, v_proof_3703_);
if (v_isShared_3707_ == 0)
{
lean_ctor_set(v___x_3706_, 1, v___x_3745_);
lean_ctor_set(v___x_3706_, 0, v_a_3740_);
v___x_3747_ = v___x_3706_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3740_);
lean_ctor_set(v_reuseFailAlloc_3752_, 1, v___x_3745_);
v___x_3747_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
uint8_t v___x_3748_; lean_object* v___x_3750_; 
v___x_3748_ = lean_unbox(v_a_3709_);
lean_dec(v_a_3709_);
lean_ctor_set_uint8(v___x_3747_, sizeof(void*)*2, v___x_3748_);
lean_ctor_set_uint8(v___x_3747_, sizeof(void*)*2 + 1, v_contextDependent_3704_);
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 0, v___x_3747_);
v___x_3750_ = v___x_3742_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v___x_3747_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
lean_dec(v_a_3709_);
lean_del_object(v___x_3706_);
lean_dec_ref(v_proof_3703_);
lean_dec_ref(v_arg_3627_);
lean_dec_ref(v_arg_3624_);
v_a_3754_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3739_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3739_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
}
else
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
lean_dec(v_a_3709_);
lean_del_object(v___x_3706_);
lean_dec_ref(v_proof_3703_);
lean_dec_ref(v_arg_3627_);
lean_dec_ref(v_arg_3624_);
v_a_3762_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3764_ = v___x_3711_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3711_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3767_; 
if (v_isShared_3765_ == 0)
{
v___x_3767_ = v___x_3764_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3762_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
}
else
{
lean_object* v___x_3770_; 
lean_dec(v_a_3709_);
lean_dec_ref(v_e_x27_3702_);
v___x_3770_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_3612_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v_a_3771_; lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3783_; 
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3773_ = v___x_3770_;
v_isShared_3774_ = v_isSharedCheck_3783_;
goto v_resetjp_3772_;
}
else
{
lean_inc(v_a_3771_);
lean_dec(v___x_3770_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3783_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3778_; 
v___x_3775_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11);
v___x_3776_ = l_Lean_mkApp3(v___x_3775_, v_arg_3627_, v_arg_3624_, v_proof_3703_);
if (v_isShared_3707_ == 0)
{
lean_ctor_set(v___x_3706_, 1, v___x_3776_);
lean_ctor_set(v___x_3706_, 0, v_a_3771_);
v___x_3778_ = v___x_3706_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3771_);
lean_ctor_set(v_reuseFailAlloc_3782_, 1, v___x_3776_);
lean_ctor_set_uint8(v_reuseFailAlloc_3782_, sizeof(void*)*2 + 1, v_contextDependent_3704_);
v___x_3778_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
lean_object* v___x_3780_; 
lean_ctor_set_uint8(v___x_3778_, sizeof(void*)*2, v___x_3607_);
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 0, v___x_3778_);
v___x_3780_ = v___x_3773_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3778_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
lean_del_object(v___x_3706_);
lean_dec_ref(v_proof_3703_);
lean_dec_ref(v_arg_3627_);
lean_dec_ref(v_arg_3624_);
v_a_3784_ = lean_ctor_get(v___x_3770_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3770_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3770_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3770_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
lean_del_object(v___x_3706_);
lean_dec_ref(v_proof_3703_);
lean_dec_ref(v_e_x27_3702_);
lean_dec_ref(v_arg_3627_);
lean_dec_ref(v_arg_3624_);
v_a_3792_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3708_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3708_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_3627_);
lean_dec_ref(v_arg_3624_);
return v___x_3633_;
}
}
}
}
v___jp_3619_:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3620_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3620_, 0, v___x_3607_);
lean_ctor_set_uint8(v___x_3620_, 1, v___x_3607_);
v___x_3621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3620_);
return v___x_3621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___boxed(lean_object* v___x_3801_, lean_object* v_e_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
uint8_t v___x_20445__boxed_3813_; lean_object* v_res_3814_; 
v___x_20445__boxed_3813_ = lean_unbox(v___x_3801_);
v_res_3814_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0(v___x_20445__boxed_3813_, v_e_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
lean_dec(v___y_3811_);
lean_dec_ref(v___y_3810_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv(lean_object* v_e_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_){
_start:
{
lean_object* v_numArgs_3826_; lean_object* v___x_3827_; uint8_t v___x_3828_; 
v_numArgs_3826_ = l_Lean_Expr_getAppNumArgs(v_e_3815_);
v___x_3827_ = lean_unsigned_to_nat(2u);
v___x_3828_ = lean_nat_dec_lt(v_numArgs_3826_, v___x_3827_);
if (v___x_3828_ == 0)
{
lean_object* v___x_3829_; lean_object* v___f_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3829_ = lean_box(v___x_3828_);
v___f_3830_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___boxed), 12, 1);
lean_closure_set(v___f_3830_, 0, v___x_3829_);
v___x_3831_ = lean_nat_sub(v_numArgs_3826_, v___x_3827_);
lean_dec(v_numArgs_3826_);
v___x_3832_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_3815_, v___x_3831_, v___f_3830_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_);
lean_dec(v___x_3831_);
return v___x_3832_;
}
else
{
uint8_t v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; 
lean_dec(v_numArgs_3826_);
lean_dec_ref(v_e_3815_);
v___x_3833_ = 0;
v___x_3834_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3834_, 0, v___x_3828_);
lean_ctor_set_uint8(v___x_3834_, 1, v___x_3833_);
v___x_3835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3834_);
return v___x_3835_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed(lean_object* v_e_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_){
_start:
{
lean_object* v_res_3847_; 
v_res_3847_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv(v_e_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_);
lean_dec(v_a_3845_);
lean_dec_ref(v_a_3844_);
lean_dec(v_a_3843_);
lean_dec_ref(v_a_3842_);
lean_dec(v_a_3841_);
lean_dec_ref(v_a_3840_);
lean_dec(v_a_3839_);
lean_dec_ref(v_a_3838_);
lean_dec(v_a_3837_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3863_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_));
v___x_3864_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_));
v___x_3865_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed), 11, 0);
v___x_3866_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_3863_, v___x_3864_, v___x_3865_);
return v___x_3866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14____boxed(lean_object* v_a_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_();
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_3870_; uint8_t v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3870_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_));
v___x_3871_ = 0;
v___x_3872_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed), 11, 0);
v___x_3873_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_3870_, v___x_3871_, v___x_3872_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_16____boxed(lean_object* v_a_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_16_();
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond(lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_){
_start:
{
lean_object* v___x_3887_; 
v___x_3887_ = l_Lean_Meta_Sym_Simp_simpCond(v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___boxed(lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond(v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_);
lean_dec(v_a_3897_);
lean_dec_ref(v_a_3896_);
lean_dec(v_a_3895_);
lean_dec_ref(v_a_3894_);
lean_dec(v_a_3893_);
lean_dec_ref(v_a_3892_);
lean_dec(v_a_3891_);
lean_dec_ref(v_a_3890_);
lean_dec(v_a_3889_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_(){
_start:
{
lean_object* v___f_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___f_3926_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_));
v___x_3927_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_));
v___x_3928_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_));
v___x_3929_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_3927_, v___x_3928_, v___f_3926_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16____boxed(lean_object* v_a_3930_){
_start:
{
lean_object* v_res_3931_; 
v_res_3931_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_();
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_18_(){
_start:
{
lean_object* v___f_3933_; lean_object* v___x_3934_; uint8_t v___x_3935_; lean_object* v___x_3936_; 
v___f_3933_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_));
v___x_3934_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_));
v___x_3935_ = 0;
v___x_3936_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_3934_, v___x_3935_, v___f_3933_);
return v___x_3936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_18____boxed(lean_object* v_a_3937_){
_start:
{
lean_object* v_res_3938_; 
v_res_3938_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_18_();
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(lean_object* v_msgData_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_){
_start:
{
lean_object* v___x_3945_; lean_object* v_env_3946_; lean_object* v___x_3947_; lean_object* v_mctx_3948_; lean_object* v_lctx_3949_; lean_object* v_options_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v___x_3945_ = lean_st_ref_get(v___y_3943_);
v_env_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc_ref(v_env_3946_);
lean_dec(v___x_3945_);
v___x_3947_ = lean_st_ref_get(v___y_3941_);
v_mctx_3948_ = lean_ctor_get(v___x_3947_, 0);
lean_inc_ref(v_mctx_3948_);
lean_dec(v___x_3947_);
v_lctx_3949_ = lean_ctor_get(v___y_3940_, 2);
v_options_3950_ = lean_ctor_get(v___y_3942_, 1);
lean_inc_ref(v_options_3950_);
lean_inc_ref(v_lctx_3949_);
v___x_3951_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3951_, 0, v_env_3946_);
lean_ctor_set(v___x_3951_, 1, v_mctx_3948_);
lean_ctor_set(v___x_3951_, 2, v_lctx_3949_);
lean_ctor_set(v___x_3951_, 3, v_options_3950_);
v___x_3952_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3951_);
lean_ctor_set(v___x_3952_, 1, v_msgData_3939_);
v___x_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3952_);
return v___x_3953_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0___boxed(lean_object* v_msgData_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(v_msgData_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
return v_res_3960_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_3961_; double v___x_3962_; 
v___x_3961_ = lean_unsigned_to_nat(0u);
v___x_3962_ = lean_float_of_nat(v___x_3961_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(lean_object* v_cls_3966_, lean_object* v_msg_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
lean_object* v_ref_3973_; lean_object* v___x_3974_; lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_4019_; 
v_ref_3973_ = lean_ctor_get(v___y_3970_, 4);
v___x_3974_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(v_msg_3967_, v___y_3968_, v___y_3969_, v___y_3970_, v___y_3971_);
v_a_3975_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_3977_ = v___x_3974_;
v_isShared_3978_ = v_isSharedCheck_4019_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3974_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_4019_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3979_; lean_object* v_traceState_3980_; lean_object* v_env_3981_; lean_object* v_nextMacroScope_3982_; lean_object* v_ngen_3983_; lean_object* v_auxDeclNGen_3984_; lean_object* v_cache_3985_; lean_object* v_messages_3986_; lean_object* v_infoState_3987_; lean_object* v_snapshotTasks_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_4018_; 
v___x_3979_ = lean_st_ref_take(v___y_3971_);
v_traceState_3980_ = lean_ctor_get(v___x_3979_, 4);
v_env_3981_ = lean_ctor_get(v___x_3979_, 0);
v_nextMacroScope_3982_ = lean_ctor_get(v___x_3979_, 1);
v_ngen_3983_ = lean_ctor_get(v___x_3979_, 2);
v_auxDeclNGen_3984_ = lean_ctor_get(v___x_3979_, 3);
v_cache_3985_ = lean_ctor_get(v___x_3979_, 5);
v_messages_3986_ = lean_ctor_get(v___x_3979_, 6);
v_infoState_3987_ = lean_ctor_get(v___x_3979_, 7);
v_snapshotTasks_3988_ = lean_ctor_get(v___x_3979_, 8);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_3990_ = v___x_3979_;
v_isShared_3991_ = v_isSharedCheck_4018_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_snapshotTasks_3988_);
lean_inc(v_infoState_3987_);
lean_inc(v_messages_3986_);
lean_inc(v_cache_3985_);
lean_inc(v_traceState_3980_);
lean_inc(v_auxDeclNGen_3984_);
lean_inc(v_ngen_3983_);
lean_inc(v_nextMacroScope_3982_);
lean_inc(v_env_3981_);
lean_dec(v___x_3979_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_4018_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
uint64_t v_tid_3992_; lean_object* v_traces_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4017_; 
v_tid_3992_ = lean_ctor_get_uint64(v_traceState_3980_, sizeof(void*)*1);
v_traces_3993_ = lean_ctor_get(v_traceState_3980_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v_traceState_3980_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_3995_ = v_traceState_3980_;
v_isShared_3996_ = v_isSharedCheck_4017_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_traces_3993_);
lean_dec(v_traceState_3980_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4017_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3997_; double v___x_3998_; uint8_t v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4007_; 
v___x_3997_ = lean_box(0);
v___x_3998_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0);
v___x_3999_ = 0;
v___x_4000_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__1));
v___x_4001_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4001_, 0, v_cls_3966_);
lean_ctor_set(v___x_4001_, 1, v___x_3997_);
lean_ctor_set(v___x_4001_, 2, v___x_4000_);
lean_ctor_set_float(v___x_4001_, sizeof(void*)*3, v___x_3998_);
lean_ctor_set_float(v___x_4001_, sizeof(void*)*3 + 8, v___x_3998_);
lean_ctor_set_uint8(v___x_4001_, sizeof(void*)*3 + 16, v___x_3999_);
v___x_4002_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__2));
v___x_4003_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4001_);
lean_ctor_set(v___x_4003_, 1, v_a_3975_);
lean_ctor_set(v___x_4003_, 2, v___x_4002_);
lean_inc(v_ref_3973_);
v___x_4004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4004_, 0, v_ref_3973_);
lean_ctor_set(v___x_4004_, 1, v___x_4003_);
v___x_4005_ = l_Lean_PersistentArray_push___redArg(v_traces_3993_, v___x_4004_);
if (v_isShared_3996_ == 0)
{
lean_ctor_set(v___x_3995_, 0, v___x_4005_);
v___x_4007_ = v___x_3995_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v___x_4005_);
lean_ctor_set_uint64(v_reuseFailAlloc_4016_, sizeof(void*)*1, v_tid_3992_);
v___x_4007_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
lean_object* v___x_4009_; 
if (v_isShared_3991_ == 0)
{
lean_ctor_set(v___x_3990_, 4, v___x_4007_);
v___x_4009_ = v___x_3990_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_env_3981_);
lean_ctor_set(v_reuseFailAlloc_4015_, 1, v_nextMacroScope_3982_);
lean_ctor_set(v_reuseFailAlloc_4015_, 2, v_ngen_3983_);
lean_ctor_set(v_reuseFailAlloc_4015_, 3, v_auxDeclNGen_3984_);
lean_ctor_set(v_reuseFailAlloc_4015_, 4, v___x_4007_);
lean_ctor_set(v_reuseFailAlloc_4015_, 5, v_cache_3985_);
lean_ctor_set(v_reuseFailAlloc_4015_, 6, v_messages_3986_);
lean_ctor_set(v_reuseFailAlloc_4015_, 7, v_infoState_3987_);
lean_ctor_set(v_reuseFailAlloc_4015_, 8, v_snapshotTasks_3988_);
v___x_4009_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4013_; 
v___x_4010_ = lean_st_ref_put(v___y_3971_, v___x_4009_);
v___x_4011_ = lean_box(0);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 0, v___x_4011_);
v___x_4013_ = v___x_3977_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v___x_4011_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___boxed(lean_object* v_cls_4020_, lean_object* v_msg_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v_cls_4020_, v_msg_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
return v_res_4027_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5(void){
_start:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
v___x_4038_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2));
v___x_4039_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4));
v___x_4040_ = l_Lean_Name_append(v___x_4039_, v___x_4038_);
return v___x_4040_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7(void){
_start:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4042_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__6));
v___x_4043_ = l_Lean_stringToMessageData(v___x_4042_);
return v___x_4043_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9(void){
_start:
{
lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4045_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__8));
v___x_4046_ = l_Lean_stringToMessageData(v___x_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(lean_object* v_e_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_){
_start:
{
lean_object* v___x_4058_; lean_object* v___x_4059_; 
lean_inc_ref(v_e_4047_);
v___x_4058_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___boxed), 6, 1);
lean_closure_set(v___x_4058_, 0, v_e_4047_);
v___x_4059_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_4058_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4118_; 
v_a_4060_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4062_ = v___x_4059_;
v_isShared_4063_ = v_isSharedCheck_4118_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4059_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4118_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
if (lean_obj_tag(v_a_4060_) == 1)
{
lean_object* v_val_4064_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v_options_4091_; uint8_t v_hasTrace_4092_; 
lean_del_object(v___x_4062_);
v_val_4064_ = lean_ctor_get(v_a_4060_, 0);
lean_inc(v_val_4064_);
lean_dec_ref_known(v_a_4060_, 1);
v_options_4091_ = lean_ctor_get(v_a_4055_, 1);
v_hasTrace_4092_ = lean_ctor_get_uint8(v_options_4091_, sizeof(void*)*1);
if (v_hasTrace_4092_ == 0)
{
lean_dec_ref(v_e_4047_);
v___y_4066_ = v_a_4051_;
v___y_4067_ = v_a_4052_;
v___y_4068_ = v_a_4053_;
v___y_4069_ = v_a_4054_;
v___y_4070_ = v_a_4055_;
v___y_4071_ = v_a_4056_;
goto v___jp_4065_;
}
else
{
lean_object* v_toCold_4093_; lean_object* v_inheritedTraceOptions_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; uint8_t v___x_4097_; 
v_toCold_4093_ = lean_ctor_get(v_a_4055_, 0);
v_inheritedTraceOptions_4094_ = lean_ctor_get(v_toCold_4093_, 4);
v___x_4095_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2));
v___x_4096_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5);
v___x_4097_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4094_, v_options_4091_, v___x_4096_);
if (v___x_4097_ == 0)
{
lean_dec_ref(v_e_4047_);
v___y_4066_ = v_a_4051_;
v___y_4067_ = v_a_4052_;
v___y_4068_ = v_a_4053_;
v___y_4069_ = v_a_4054_;
v___y_4070_ = v_a_4055_;
v___y_4071_ = v_a_4056_;
goto v___jp_4065_;
}
else
{
lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
v___x_4098_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7);
v___x_4099_ = l_Lean_indentExpr(v_e_4047_);
v___x_4100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4098_);
lean_ctor_set(v___x_4100_, 1, v___x_4099_);
v___x_4101_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9);
v___x_4102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4100_);
lean_ctor_set(v___x_4102_, 1, v___x_4101_);
lean_inc(v_val_4064_);
v___x_4103_ = l_Lean_indentExpr(v_val_4064_);
v___x_4104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4102_);
lean_ctor_set(v___x_4104_, 1, v___x_4103_);
v___x_4105_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v___x_4095_, v___x_4104_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_);
if (lean_obj_tag(v___x_4105_) == 0)
{
lean_dec_ref_known(v___x_4105_, 1);
v___y_4066_ = v_a_4051_;
v___y_4067_ = v_a_4052_;
v___y_4068_ = v_a_4053_;
v___y_4069_ = v_a_4054_;
v___y_4070_ = v_a_4055_;
v___y_4071_ = v_a_4056_;
goto v___jp_4065_;
}
else
{
lean_object* v_a_4106_; lean_object* v___x_4108_; uint8_t v_isShared_4109_; uint8_t v_isSharedCheck_4113_; 
lean_dec(v_val_4064_);
v_a_4106_ = lean_ctor_get(v___x_4105_, 0);
v_isSharedCheck_4113_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4108_ = v___x_4105_;
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
else
{
lean_inc(v_a_4106_);
lean_dec(v___x_4105_);
v___x_4108_ = lean_box(0);
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
v_resetjp_4107_:
{
lean_object* v___x_4111_; 
if (v_isShared_4109_ == 0)
{
v___x_4111_ = v___x_4108_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_a_4106_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
return v___x_4111_;
}
}
}
}
}
v___jp_4065_:
{
lean_object* v___x_4072_; 
lean_inc(v_val_4064_);
v___x_4072_ = l_Lean_Meta_Sym_mkEqRefl(v_val_4064_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4082_; 
v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4075_ = v___x_4072_;
v_isShared_4076_ = v_isSharedCheck_4082_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4072_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4082_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
uint8_t v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4080_; 
v___x_4077_ = 0;
v___x_4078_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_4078_, 0, v_val_4064_);
lean_ctor_set(v___x_4078_, 1, v_a_4073_);
lean_ctor_set_uint8(v___x_4078_, sizeof(void*)*2, v___x_4077_);
lean_ctor_set_uint8(v___x_4078_, sizeof(void*)*2 + 1, v___x_4077_);
if (v_isShared_4076_ == 0)
{
lean_ctor_set(v___x_4075_, 0, v___x_4078_);
v___x_4080_ = v___x_4075_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v___x_4078_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
}
}
}
else
{
lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4090_; 
lean_dec(v_val_4064_);
v_a_4083_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4085_ = v___x_4072_;
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4072_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4086_ == 0)
{
v___x_4088_ = v___x_4085_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
}
}
else
{
lean_object* v___x_4114_; lean_object* v___x_4116_; 
lean_dec(v_a_4060_);
lean_dec_ref(v_e_4047_);
v___x_4114_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___closed__0));
if (v_isShared_4063_ == 0)
{
lean_ctor_set(v___x_4062_, 0, v___x_4114_);
v___x_4116_ = v___x_4062_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v___x_4114_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
else
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4126_; 
lean_dec_ref(v_e_4047_);
v_a_4119_ = lean_ctor_get(v___x_4059_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4059_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_4059_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4059_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___boxed(lean_object* v_e_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_){
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_);
lean_dec(v_a_4136_);
lean_dec_ref(v_a_4135_);
lean_dec(v_a_4134_);
lean_dec_ref(v_a_4133_);
lean_dec(v_a_4132_);
lean_dec_ref(v_a_4131_);
lean_dec(v_a_4130_);
lean_dec_ref(v_a_4129_);
lean_dec(v_a_4128_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0(lean_object* v_cls_4139_, lean_object* v_msg_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
lean_object* v___x_4151_; 
v___x_4151_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v_cls_4139_, v_msg_4140_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
return v___x_4151_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___boxed(lean_object* v_cls_4152_, lean_object* v_msg_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0(v_cls_4152_, v_msg_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v___y_4156_);
lean_dec_ref(v___y_4155_);
lean_dec(v___y_4154_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec(lean_object* v_x_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_){
_start:
{
uint8_t v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4188_ = 0;
v___x_4189_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__0));
lean_inc_ref(v_x_4177_);
v___x_4190_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_x_4177_, v___x_4189_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_object* v_a_4191_; 
v_a_4191_ = lean_ctor_get(v___x_4190_, 0);
lean_inc(v_a_4191_);
if (lean_obj_tag(v_a_4191_) == 0)
{
uint8_t v_done_4192_; 
v_done_4192_ = lean_ctor_get_uint8(v_a_4191_, 0);
if (v_done_4192_ == 0)
{
lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4205_; 
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4190_);
if (v_isSharedCheck_4205_ == 0)
{
lean_object* v_unused_4206_; 
v_unused_4206_ = lean_ctor_get(v___x_4190_, 0);
lean_dec(v_unused_4206_);
v___x_4194_ = v___x_4190_;
v_isShared_4195_ = v_isSharedCheck_4205_;
goto v_resetjp_4193_;
}
else
{
lean_dec(v___x_4190_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4205_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
uint8_t v_contextDependent_4196_; lean_object* v___x_4197_; 
v_contextDependent_4196_ = lean_ctor_get_uint8(v_a_4191_, 1);
lean_dec_ref_known(v_a_4191_, 0);
v___x_4197_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_x_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v_a_4198_; uint8_t v___y_4200_; 
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
lean_inc(v_a_4198_);
if (v_contextDependent_4196_ == 0)
{
lean_dec(v_a_4198_);
lean_del_object(v___x_4194_);
return v___x_4197_;
}
else
{
lean_dec_ref_known(v___x_4197_, 1);
v___y_4200_ = v___x_4188_;
goto v___jp_4199_;
}
v___jp_4199_:
{
lean_object* v___x_4201_; lean_object* v___x_4203_; 
v___x_4201_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_4198_);
if (v_isShared_4195_ == 0)
{
lean_ctor_set(v___x_4194_, 0, v___x_4201_);
v___x_4203_ = v___x_4194_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v___x_4201_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
else
{
lean_del_object(v___x_4194_);
return v___x_4197_;
}
}
}
else
{
lean_dec_ref_known(v_a_4191_, 0);
lean_dec_ref(v_x_4177_);
return v___x_4190_;
}
}
else
{
uint8_t v_done_4207_; 
v_done_4207_ = lean_ctor_get_uint8(v_a_4191_, sizeof(void*)*2);
if (v_done_4207_ == 0)
{
lean_object* v_e_x27_4208_; lean_object* v_proof_4209_; uint8_t v_contextDependent_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4256_; 
lean_dec_ref_known(v___x_4190_, 1);
v_e_x27_4208_ = lean_ctor_get(v_a_4191_, 0);
v_proof_4209_ = lean_ctor_get(v_a_4191_, 1);
v_contextDependent_4210_ = lean_ctor_get_uint8(v_a_4191_, sizeof(void*)*2 + 1);
v_isSharedCheck_4256_ = !lean_is_exclusive(v_a_4191_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4212_ = v_a_4191_;
v_isShared_4213_ = v_isSharedCheck_4256_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_proof_4209_);
lean_inc(v_e_x27_4208_);
lean_dec(v_a_4191_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4256_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4214_; 
lean_inc_ref(v_e_x27_4208_);
v___x_4214_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_x27_4208_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v_a_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4255_; 
v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4217_ = v___x_4214_;
v_isShared_4218_ = v_isSharedCheck_4255_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_a_4215_);
lean_dec(v___x_4214_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4255_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
if (lean_obj_tag(v_a_4215_) == 0)
{
uint8_t v___y_4220_; 
lean_dec_ref_known(v_a_4215_, 0);
lean_dec_ref(v_x_4177_);
if (v_contextDependent_4210_ == 0)
{
v___y_4220_ = v___x_4188_;
goto v___jp_4219_;
}
else
{
v___y_4220_ = v_contextDependent_4210_;
goto v___jp_4219_;
}
v___jp_4219_:
{
lean_object* v___x_4222_; 
if (v_isShared_4213_ == 0)
{
v___x_4222_ = v___x_4212_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_e_x27_4208_);
lean_ctor_set(v_reuseFailAlloc_4226_, 1, v_proof_4209_);
v___x_4222_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
lean_object* v___x_4224_; 
lean_ctor_set_uint8(v___x_4222_, sizeof(void*)*2, v___x_4188_);
lean_ctor_set_uint8(v___x_4222_, sizeof(void*)*2 + 1, v___y_4220_);
if (v_isShared_4218_ == 0)
{
lean_ctor_set(v___x_4217_, 0, v___x_4222_);
v___x_4224_ = v___x_4217_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4222_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
else
{
lean_object* v_e_x27_4227_; lean_object* v_proof_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4254_; 
lean_del_object(v___x_4217_);
lean_del_object(v___x_4212_);
v_e_x27_4227_ = lean_ctor_get(v_a_4215_, 0);
v_proof_4228_ = lean_ctor_get(v_a_4215_, 1);
v_isSharedCheck_4254_ = !lean_is_exclusive(v_a_4215_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4230_ = v_a_4215_;
v_isShared_4231_ = v_isSharedCheck_4254_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_proof_4228_);
lean_inc(v_e_x27_4227_);
lean_dec(v_a_4215_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4254_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4232_; 
lean_inc_ref(v_e_x27_4227_);
v___x_4232_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_x_4177_, v_e_x27_4208_, v_proof_4209_, v_e_x27_4227_, v_proof_4228_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_);
if (lean_obj_tag(v___x_4232_) == 0)
{
lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4245_; 
v_a_4233_ = lean_ctor_get(v___x_4232_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4232_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4235_ = v___x_4232_;
v_isShared_4236_ = v_isSharedCheck_4245_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_dec(v___x_4232_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4245_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
uint8_t v___y_4238_; 
if (v_contextDependent_4210_ == 0)
{
v___y_4238_ = v___x_4188_;
goto v___jp_4237_;
}
else
{
v___y_4238_ = v_contextDependent_4210_;
goto v___jp_4237_;
}
v___jp_4237_:
{
lean_object* v___x_4240_; 
if (v_isShared_4231_ == 0)
{
lean_ctor_set(v___x_4230_, 1, v_a_4233_);
v___x_4240_ = v___x_4230_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_e_x27_4227_);
lean_ctor_set(v_reuseFailAlloc_4244_, 1, v_a_4233_);
v___x_4240_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
lean_object* v___x_4242_; 
lean_ctor_set_uint8(v___x_4240_, sizeof(void*)*2, v___x_4188_);
lean_ctor_set_uint8(v___x_4240_, sizeof(void*)*2 + 1, v___y_4238_);
if (v_isShared_4236_ == 0)
{
lean_ctor_set(v___x_4235_, 0, v___x_4240_);
v___x_4242_ = v___x_4235_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v___x_4240_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
}
}
else
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
lean_del_object(v___x_4230_);
lean_dec_ref(v_e_x27_4227_);
v_a_4246_ = lean_ctor_get(v___x_4232_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4232_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4248_ = v___x_4232_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v___x_4232_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_4212_);
lean_dec_ref(v_proof_4209_);
lean_dec_ref(v_e_x27_4208_);
lean_dec_ref(v_x_4177_);
return v___x_4214_;
}
}
}
else
{
lean_dec_ref_known(v_a_4191_, 2);
lean_dec_ref(v_x_4177_);
return v___x_4190_;
}
}
}
else
{
lean_dec_ref(v_x_4177_);
return v___x_4190_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed(lean_object* v_x_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_){
_start:
{
lean_object* v_res_4268_; 
v_res_4268_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec(v_x_4257_, v_a_4258_, v_a_4259_, v_a_4260_, v_a_4261_, v_a_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_);
lean_dec(v_a_4266_);
lean_dec_ref(v_a_4265_);
lean_dec(v_a_4264_);
lean_dec_ref(v_a_4263_);
lean_dec(v_a_4262_);
lean_dec_ref(v_a_4261_);
lean_dec(v_a_4260_);
lean_dec_ref(v_a_4259_);
lean_dec(v_a_4258_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; 
v___x_4290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_));
v___x_4291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_));
v___x_4292_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed), 11, 0);
v___x_4293_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_4290_, v___x_4291_, v___x_4292_);
return v___x_4293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17____boxed(lean_object* v_a_4294_){
_start:
{
lean_object* v_res_4295_; 
v_res_4295_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_();
return v_res_4295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_4297_; uint8_t v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; 
v___x_4297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_));
v___x_4298_ = 0;
v___x_4299_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed), 11, 0);
v___x_4300_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_4297_, v___x_4298_, v___x_4299_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_19____boxed(lean_object* v_a_4301_){
_start:
{
lean_object* v_res_4302_; 
v_res_4302_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_19_();
return v_res_4302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(lean_object* v_appFn_4304_, lean_object* v_e_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_){
_start:
{
lean_object* v___x_4316_; 
v___x_4316_ = l_Lean_Meta_Tactic_Cbv_getMatchTheorems(v_appFn_4304_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v_a_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v_a_4317_ = lean_ctor_get(v___x_4316_, 0);
lean_inc(v_a_4317_);
lean_dec_ref_known(v___x_4316_, 1);
v___x_4318_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0));
v___x_4319_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_4317_, v___x_4318_, v_e_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_);
lean_dec(v_a_4317_);
return v___x_4319_;
}
else
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
lean_dec_ref(v_e_4305_);
v_a_4320_ = lean_ctor_get(v___x_4316_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___x_4316_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4316_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4325_; 
if (v_isShared_4323_ == 0)
{
v___x_4325_ = v___x_4322_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4320_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___boxed(lean_object* v_appFn_4328_, lean_object* v_e_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_appFn_4328_, v_e_4329_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_, v_a_4337_, v_a_4338_);
lean_dec(v_a_4338_);
lean_dec_ref(v_a_4337_);
lean_dec(v_a_4336_);
lean_dec_ref(v_a_4335_);
lean_dec(v_a_4334_);
lean_dec_ref(v_a_4333_);
lean_dec(v_a_4332_);
lean_dec_ref(v_a_4331_);
lean_dec(v_a_4330_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(lean_object* v_declName_4341_, lean_object* v___y_4342_){
_start:
{
lean_object* v___x_4344_; lean_object* v_env_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
v___x_4344_ = lean_st_ref_get(v___y_4342_);
v_env_4345_ = lean_ctor_get(v___x_4344_, 0);
lean_inc_ref(v_env_4345_);
lean_dec(v___x_4344_);
v___x_4346_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_4345_, v_declName_4341_);
v___x_4347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4347_, 0, v___x_4346_);
return v___x_4347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg___boxed(lean_object* v_declName_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_){
_start:
{
lean_object* v_res_4351_; 
v_res_4351_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(v_declName_4348_, v___y_4349_);
lean_dec(v___y_4349_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(lean_object* v_declName_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
lean_object* v___x_4363_; 
v___x_4363_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(v_declName_4352_, v___y_4361_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___boxed(lean_object* v_declName_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(v_declName_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_);
lean_dec(v___y_4373_);
lean_dec_ref(v___y_4372_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
lean_dec(v___y_4367_);
lean_dec_ref(v___y_4366_);
lean_dec(v___y_4365_);
return v_res_4375_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2(void){
_start:
{
lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4382_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1));
v___x_4383_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4));
v___x_4384_ = l_Lean_Name_append(v___x_4383_, v___x_4382_);
return v___x_4384_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4(void){
_start:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; 
v___x_4386_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__3));
v___x_4387_ = l_Lean_stringToMessageData(v___x_4386_);
return v___x_4387_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6(void){
_start:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; 
v___x_4389_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__5));
v___x_4390_ = l_Lean_stringToMessageData(v___x_4389_);
return v___x_4390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher(lean_object* v_e_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_){
_start:
{
uint8_t v___x_4402_; 
v___x_4402_ = l_Lean_Expr_isApp(v_e_4391_);
if (v___x_4402_ == 0)
{
lean_object* v___x_4403_; lean_object* v___x_4404_; 
lean_dec_ref(v_e_4391_);
v___x_4403_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_4403_, 0, v___x_4402_);
lean_ctor_set_uint8(v___x_4403_, 1, v___x_4402_);
v___x_4404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4403_);
return v___x_4404_;
}
else
{
lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4405_ = l_Lean_Expr_getAppFn(v_e_4391_);
v___x_4406_ = l_Lean_Expr_constName_x3f(v___x_4405_);
lean_dec_ref(v___x_4405_);
if (lean_obj_tag(v___x_4406_) == 1)
{
lean_object* v_val_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4555_; 
v_val_4407_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4555_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4555_ == 0)
{
v___x_4409_ = v___x_4406_;
v_isShared_4410_ = v_isSharedCheck_4555_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_val_4407_);
lean_dec(v___x_4406_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4555_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v_a_4412_; lean_object* v_e_x27_4413_; lean_object* v___y_4456_; lean_object* v_a_4457_; lean_object* v___y_4460_; lean_object* v___y_4463_; lean_object* v___y_4464_; uint8_t v___y_4465_; lean_object* v___y_4469_; lean_object* v_a_4470_; lean_object* v___y_4478_; lean_object* v___x_4480_; lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4554_; 
lean_inc(v_val_4407_);
v___x_4480_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(v_val_4407_, v_a_4400_);
v_a_4481_ = lean_ctor_get(v___x_4480_, 0);
v_isSharedCheck_4554_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4554_ == 0)
{
v___x_4483_ = v___x_4480_;
v_isShared_4484_ = v_isSharedCheck_4554_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4480_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4554_;
goto v_resetjp_4482_;
}
v___jp_4411_:
{
lean_object* v_options_4414_; uint8_t v_hasTrace_4415_; 
v_options_4414_ = lean_ctor_get(v_a_4399_, 1);
v_hasTrace_4415_ = lean_ctor_get_uint8(v_options_4414_, sizeof(void*)*1);
if (v_hasTrace_4415_ == 0)
{
lean_object* v___x_4417_; 
lean_dec_ref(v_e_x27_4413_);
lean_dec(v_val_4407_);
lean_dec_ref(v_e_4391_);
if (v_isShared_4410_ == 0)
{
lean_ctor_set_tag(v___x_4409_, 0);
lean_ctor_set(v___x_4409_, 0, v_a_4412_);
v___x_4417_ = v___x_4409_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4412_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
return v___x_4417_;
}
}
else
{
lean_object* v_toCold_4419_; lean_object* v_inheritedTraceOptions_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; uint8_t v___x_4423_; 
v_toCold_4419_ = lean_ctor_get(v_a_4399_, 0);
v_inheritedTraceOptions_4420_ = lean_ctor_get(v_toCold_4419_, 4);
v___x_4421_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1));
v___x_4422_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2, &l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2);
v___x_4423_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4420_, v_options_4414_, v___x_4422_);
if (v___x_4423_ == 0)
{
lean_object* v___x_4425_; 
lean_dec_ref(v_e_x27_4413_);
lean_dec(v_val_4407_);
lean_dec_ref(v_e_4391_);
if (v_isShared_4410_ == 0)
{
lean_ctor_set_tag(v___x_4409_, 0);
lean_ctor_set(v___x_4409_, 0, v_a_4412_);
v___x_4425_ = v___x_4409_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_a_4412_);
v___x_4425_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
return v___x_4425_;
}
}
else
{
lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
lean_del_object(v___x_4409_);
v___x_4427_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4, &l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4);
v___x_4428_ = l_Lean_MessageData_ofName(v_val_4407_);
v___x_4429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4427_);
lean_ctor_set(v___x_4429_, 1, v___x_4428_);
v___x_4430_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6, &l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6);
v___x_4431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4431_, 0, v___x_4429_);
lean_ctor_set(v___x_4431_, 1, v___x_4430_);
v___x_4432_ = l_Lean_indentExpr(v_e_4391_);
v___x_4433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4433_, 0, v___x_4431_);
lean_ctor_set(v___x_4433_, 1, v___x_4432_);
v___x_4434_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9);
v___x_4435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4433_);
lean_ctor_set(v___x_4435_, 1, v___x_4434_);
v___x_4436_ = l_Lean_indentExpr(v_e_x27_4413_);
v___x_4437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4437_, 0, v___x_4435_);
lean_ctor_set(v___x_4437_, 1, v___x_4436_);
v___x_4438_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v___x_4421_, v___x_4437_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_);
if (lean_obj_tag(v___x_4438_) == 0)
{
lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4445_; 
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4445_ == 0)
{
lean_object* v_unused_4446_; 
v_unused_4446_ = lean_ctor_get(v___x_4438_, 0);
lean_dec(v_unused_4446_);
v___x_4440_ = v___x_4438_;
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
else
{
lean_dec(v___x_4438_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4443_; 
if (v_isShared_4441_ == 0)
{
lean_ctor_set(v___x_4440_, 0, v_a_4412_);
v___x_4443_ = v___x_4440_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_a_4412_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
else
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
lean_dec_ref(v_a_4412_);
v_a_4447_ = lean_ctor_get(v___x_4438_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4449_ = v___x_4438_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4438_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
}
}
}
v___jp_4455_:
{
if (lean_obj_tag(v_a_4457_) == 1)
{
lean_object* v_e_x27_4458_; 
lean_dec_ref(v___y_4456_);
v_e_x27_4458_ = lean_ctor_get(v_a_4457_, 0);
lean_inc_ref(v_e_x27_4458_);
v_a_4412_ = v_a_4457_;
v_e_x27_4413_ = v_e_x27_4458_;
goto v___jp_4411_;
}
else
{
lean_dec_ref(v_a_4457_);
lean_del_object(v___x_4409_);
lean_dec(v_val_4407_);
lean_dec_ref(v_e_4391_);
return v___y_4456_;
}
}
v___jp_4459_:
{
if (lean_obj_tag(v___y_4460_) == 0)
{
lean_object* v_a_4461_; 
v_a_4461_ = lean_ctor_get(v___y_4460_, 0);
lean_inc(v_a_4461_);
v___y_4456_ = v___y_4460_;
v_a_4457_ = v_a_4461_;
goto v___jp_4455_;
}
else
{
lean_del_object(v___x_4409_);
lean_dec(v_val_4407_);
lean_dec_ref(v_e_4391_);
return v___y_4460_;
}
}
v___jp_4462_:
{
lean_object* v___x_4466_; lean_object* v___x_4467_; 
lean_dec_ref(v___y_4464_);
v___x_4466_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_4463_);
lean_inc_ref(v___x_4466_);
v___x_4467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4467_, 0, v___x_4466_);
v___y_4456_ = v___x_4467_;
v_a_4457_ = v___x_4466_;
goto v___jp_4455_;
}
v___jp_4468_:
{
if (lean_obj_tag(v_a_4470_) == 0)
{
uint8_t v_done_4471_; 
v_done_4471_ = lean_ctor_get_uint8(v_a_4470_, 0);
if (v_done_4471_ == 0)
{
uint8_t v_contextDependent_4472_; lean_object* v___x_4473_; 
lean_dec_ref(v___y_4469_);
v_contextDependent_4472_ = lean_ctor_get_uint8(v_a_4470_, 1);
lean_dec_ref_known(v_a_4470_, 0);
lean_inc_ref(v_e_4391_);
v___x_4473_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_);
if (lean_obj_tag(v___x_4473_) == 0)
{
if (v_contextDependent_4472_ == 0)
{
v___y_4460_ = v___x_4473_;
goto v___jp_4459_;
}
else
{
lean_object* v_a_4474_; uint8_t v___x_4475_; 
v_a_4474_ = lean_ctor_get(v___x_4473_, 0);
lean_inc(v_a_4474_);
v___x_4475_ = 0;
v___y_4463_ = v_a_4474_;
v___y_4464_ = v___x_4473_;
v___y_4465_ = v___x_4475_;
goto v___jp_4462_;
}
}
else
{
v___y_4460_ = v___x_4473_;
goto v___jp_4459_;
}
}
else
{
lean_dec_ref_known(v_a_4470_, 0);
lean_del_object(v___x_4409_);
lean_dec(v_val_4407_);
lean_dec_ref(v_e_4391_);
return v___y_4469_;
}
}
else
{
lean_object* v_e_x27_4476_; 
lean_dec_ref(v___y_4469_);
v_e_x27_4476_ = lean_ctor_get(v_a_4470_, 0);
lean_inc_ref(v_e_x27_4476_);
v_a_4412_ = v_a_4470_;
v_e_x27_4413_ = v_e_x27_4476_;
goto v___jp_4411_;
}
}
v___jp_4477_:
{
if (lean_obj_tag(v___y_4478_) == 0)
{
lean_object* v_a_4479_; 
v_a_4479_ = lean_ctor_get(v___y_4478_, 0);
lean_inc(v_a_4479_);
v___y_4469_ = v___y_4478_;
v_a_4470_ = v_a_4479_;
goto v___jp_4468_;
}
else
{
lean_del_object(v___x_4409_);
lean_dec(v_val_4407_);
lean_dec_ref(v_e_4391_);
return v___y_4478_;
}
}
v_resetjp_4482_:
{
if (lean_obj_tag(v_a_4481_) == 1)
{
lean_object* v_val_4485_; lean_object* v_numParams_4486_; lean_object* v_numDiscrs_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; 
lean_del_object(v___x_4483_);
v_val_4485_ = lean_ctor_get(v_a_4481_, 0);
lean_inc(v_val_4485_);
lean_dec_ref_known(v_a_4481_, 1);
v_numParams_4486_ = lean_ctor_get(v_val_4485_, 0);
lean_inc(v_numParams_4486_);
v_numDiscrs_4487_ = lean_ctor_get(v_val_4485_, 1);
lean_inc(v_numDiscrs_4487_);
lean_dec(v_val_4485_);
v___x_4488_ = lean_unsigned_to_nat(1u);
v___x_4489_ = lean_nat_add(v_numParams_4486_, v___x_4488_);
lean_dec(v_numParams_4486_);
v___x_4490_ = lean_nat_add(v___x_4489_, v_numDiscrs_4487_);
lean_dec(v_numDiscrs_4487_);
lean_inc_ref(v_e_4391_);
v___x_4491_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_e_4391_, v___x_4489_, v___x_4490_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_);
lean_dec(v___x_4490_);
lean_dec(v___x_4489_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v_a_4492_; 
v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
lean_inc(v_a_4492_);
if (lean_obj_tag(v_a_4492_) == 0)
{
uint8_t v_done_4493_; 
v_done_4493_ = lean_ctor_get_uint8(v_a_4492_, 0);
if (v_done_4493_ == 0)
{
uint8_t v_contextDependent_4494_; lean_object* v___x_4495_; 
lean_dec_ref_known(v___x_4491_, 1);
v_contextDependent_4494_ = lean_ctor_get_uint8(v_a_4492_, 1);
lean_dec_ref_known(v_a_4492_, 0);
lean_inc_ref(v_e_4391_);
lean_inc(v_val_4407_);
v___x_4495_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_val_4407_, v_e_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_);
if (lean_obj_tag(v___x_4495_) == 0)
{
lean_object* v_a_4496_; uint8_t v___y_4498_; 
v_a_4496_ = lean_ctor_get(v___x_4495_, 0);
lean_inc(v_a_4496_);
if (v_contextDependent_4494_ == 0)
{
lean_dec(v_a_4496_);
v___y_4478_ = v___x_4495_;
goto v___jp_4477_;
}
else
{
if (lean_obj_tag(v_a_4496_) == 0)
{
uint8_t v_contextDependent_4508_; 
v_contextDependent_4508_ = lean_ctor_get_uint8(v_a_4496_, 1);
v___y_4498_ = v_contextDependent_4508_;
goto v___jp_4497_;
}
else
{
uint8_t v_contextDependent_4509_; 
v_contextDependent_4509_ = lean_ctor_get_uint8(v_a_4496_, sizeof(void*)*2 + 1);
v___y_4498_ = v_contextDependent_4509_;
goto v___jp_4497_;
}
}
v___jp_4497_:
{
if (v___y_4498_ == 0)
{
lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4506_; 
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4495_);
if (v_isSharedCheck_4506_ == 0)
{
lean_object* v_unused_4507_; 
v_unused_4507_ = lean_ctor_get(v___x_4495_, 0);
lean_dec(v_unused_4507_);
v___x_4500_ = v___x_4495_;
v_isShared_4501_ = v_isSharedCheck_4506_;
goto v_resetjp_4499_;
}
else
{
lean_dec(v___x_4495_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4506_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4502_; lean_object* v___x_4504_; 
v___x_4502_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_4496_);
lean_inc_ref(v___x_4502_);
if (v_isShared_4501_ == 0)
{
lean_ctor_set(v___x_4500_, 0, v___x_4502_);
v___x_4504_ = v___x_4500_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4502_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
v___y_4469_ = v___x_4504_;
v_a_4470_ = v___x_4502_;
goto v___jp_4468_;
}
}
}
else
{
lean_dec(v_a_4496_);
v___y_4478_ = v___x_4495_;
goto v___jp_4477_;
}
}
}
else
{
v___y_4478_ = v___x_4495_;
goto v___jp_4477_;
}
}
else
{
lean_dec_ref_known(v_a_4492_, 0);
v___y_4478_ = v___x_4491_;
goto v___jp_4477_;
}
}
else
{
uint8_t v_done_4510_; 
v_done_4510_ = lean_ctor_get_uint8(v_a_4492_, sizeof(void*)*2);
if (v_done_4510_ == 0)
{
lean_object* v_e_x27_4511_; lean_object* v_proof_4512_; uint8_t v_contextDependent_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4549_; 
lean_dec_ref_known(v___x_4491_, 1);
v_e_x27_4511_ = lean_ctor_get(v_a_4492_, 0);
v_proof_4512_ = lean_ctor_get(v_a_4492_, 1);
v_contextDependent_4513_ = lean_ctor_get_uint8(v_a_4492_, sizeof(void*)*2 + 1);
v_isSharedCheck_4549_ = !lean_is_exclusive(v_a_4492_);
if (v_isSharedCheck_4549_ == 0)
{
v___x_4515_ = v_a_4492_;
v_isShared_4516_ = v_isSharedCheck_4549_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_proof_4512_);
lean_inc(v_e_x27_4511_);
lean_dec(v_a_4492_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4549_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4517_; 
lean_inc_ref(v_e_x27_4511_);
lean_inc(v_val_4407_);
v___x_4517_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_val_4407_, v_e_x27_4511_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_a_4518_; 
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
lean_inc(v_a_4518_);
lean_dec_ref_known(v___x_4517_, 1);
if (lean_obj_tag(v_a_4518_) == 0)
{
uint8_t v_done_4519_; uint8_t v_contextDependent_4520_; uint8_t v___y_4522_; 
v_done_4519_ = lean_ctor_get_uint8(v_a_4518_, 0);
v_contextDependent_4520_ = lean_ctor_get_uint8(v_a_4518_, 1);
lean_dec_ref_known(v_a_4518_, 0);
if (v_contextDependent_4513_ == 0)
{
v___y_4522_ = v_contextDependent_4520_;
goto v___jp_4521_;
}
else
{
v___y_4522_ = v_contextDependent_4513_;
goto v___jp_4521_;
}
v___jp_4521_:
{
lean_object* v___x_4524_; 
lean_inc_ref(v_e_x27_4511_);
if (v_isShared_4516_ == 0)
{
v___x_4524_ = v___x_4515_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_e_x27_4511_);
lean_ctor_set(v_reuseFailAlloc_4525_, 1, v_proof_4512_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
lean_ctor_set_uint8(v___x_4524_, sizeof(void*)*2, v_done_4519_);
lean_ctor_set_uint8(v___x_4524_, sizeof(void*)*2 + 1, v___y_4522_);
v_a_4412_ = v___x_4524_;
v_e_x27_4413_ = v_e_x27_4511_;
goto v___jp_4411_;
}
}
}
else
{
lean_object* v_e_x27_4526_; lean_object* v_proof_4527_; uint8_t v_done_4528_; uint8_t v_contextDependent_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4548_; 
lean_del_object(v___x_4515_);
v_e_x27_4526_ = lean_ctor_get(v_a_4518_, 0);
v_proof_4527_ = lean_ctor_get(v_a_4518_, 1);
v_done_4528_ = lean_ctor_get_uint8(v_a_4518_, sizeof(void*)*2);
v_contextDependent_4529_ = lean_ctor_get_uint8(v_a_4518_, sizeof(void*)*2 + 1);
v_isSharedCheck_4548_ = !lean_is_exclusive(v_a_4518_);
if (v_isSharedCheck_4548_ == 0)
{
v___x_4531_ = v_a_4518_;
v_isShared_4532_ = v_isSharedCheck_4548_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_proof_4527_);
lean_inc(v_e_x27_4526_);
lean_dec(v_a_4518_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4548_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4533_; 
lean_inc_ref(v_e_x27_4526_);
lean_inc_ref(v_e_4391_);
v___x_4533_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_4391_, v_e_x27_4511_, v_proof_4512_, v_e_x27_4526_, v_proof_4527_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_);
if (lean_obj_tag(v___x_4533_) == 0)
{
lean_object* v_a_4534_; uint8_t v___y_4536_; 
v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
lean_inc(v_a_4534_);
lean_dec_ref_known(v___x_4533_, 1);
if (v_contextDependent_4513_ == 0)
{
v___y_4536_ = v_contextDependent_4529_;
goto v___jp_4535_;
}
else
{
v___y_4536_ = v_contextDependent_4513_;
goto v___jp_4535_;
}
v___jp_4535_:
{
lean_object* v___x_4538_; 
lean_inc_ref(v_e_x27_4526_);
if (v_isShared_4532_ == 0)
{
lean_ctor_set(v___x_4531_, 1, v_a_4534_);
v___x_4538_ = v___x_4531_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v_e_x27_4526_);
lean_ctor_set(v_reuseFailAlloc_4539_, 1, v_a_4534_);
lean_ctor_set_uint8(v_reuseFailAlloc_4539_, sizeof(void*)*2, v_done_4528_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
lean_ctor_set_uint8(v___x_4538_, sizeof(void*)*2 + 1, v___y_4536_);
v_a_4412_ = v___x_4538_;
v_e_x27_4413_ = v_e_x27_4526_;
goto v___jp_4411_;
}
}
}
else
{
lean_object* v_a_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4547_; 
lean_del_object(v___x_4531_);
lean_dec_ref(v_e_x27_4526_);
lean_del_object(v___x_4409_);
lean_dec(v_val_4407_);
lean_dec_ref(v_e_4391_);
v_a_4540_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4542_ = v___x_4533_;
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_a_4540_);
lean_dec(v___x_4533_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v___x_4545_; 
if (v_isShared_4543_ == 0)
{
v___x_4545_ = v___x_4542_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_a_4540_);
v___x_4545_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
return v___x_4545_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_4515_);
lean_dec_ref(v_proof_4512_);
lean_dec_ref(v_e_x27_4511_);
v___y_4478_ = v___x_4517_;
goto v___jp_4477_;
}
}
}
else
{
lean_dec_ref_known(v_a_4492_, 2);
v___y_4478_ = v___x_4491_;
goto v___jp_4477_;
}
}
}
else
{
v___y_4478_ = v___x_4491_;
goto v___jp_4477_;
}
}
else
{
lean_object* v___x_4550_; lean_object* v___x_4552_; 
lean_dec(v_a_4481_);
lean_del_object(v___x_4409_);
lean_dec(v_val_4407_);
lean_dec_ref(v_e_4391_);
v___x_4550_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___closed__0));
if (v_isShared_4484_ == 0)
{
lean_ctor_set(v___x_4483_, 0, v___x_4550_);
v___x_4552_ = v___x_4483_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v___x_4550_);
v___x_4552_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
return v___x_4552_;
}
}
}
}
}
else
{
lean_object* v___x_4556_; lean_object* v___x_4557_; 
lean_dec(v___x_4406_);
lean_dec_ref(v_e_4391_);
v___x_4556_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___closed__0));
v___x_4557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4556_);
return v___x_4557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___boxed(lean_object* v_e_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_){
_start:
{
lean_object* v_res_4569_; 
v_res_4569_ = l_Lean_Meta_Tactic_Cbv_tryMatcher(v_e_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
lean_dec(v_a_4565_);
lean_dec_ref(v_a_4564_);
lean_dec(v_a_4563_);
lean_dec_ref(v_a_4562_);
lean_dec(v_a_4561_);
lean_dec_ref(v_a_4560_);
lean_dec(v_a_4559_);
return v_res_4569_;
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

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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_betaRevS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppRev(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getBoundedAppFn(lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Expr_replaceFn(lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_propagateOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Cbv"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(93, 144, 236, 69, 149, 78, 215, 228)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__9_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ControlFlow"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__9_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__9_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__10_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__9_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(153, 75, 2, 199, 142, 91, 93, 201)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__10_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__10_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__11_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__10_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(252, 60, 118, 117, 62, 213, 206, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__11_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__11_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__12_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__11_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value),LEAN_SCALAR_PTR_LITERAL(157, 4, 12, 27, 152, 101, 133, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__12_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__12_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__12_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(245, 145, 82, 72, 75, 94, 216, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__14_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value),LEAN_SCALAR_PTR_LITERAL(144, 2, 145, 22, 246, 43, 198, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__14_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__14_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__15_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__15_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__15_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__14_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__15_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(124, 100, 175, 78, 162, 84, 105, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__17_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "simpIteCbv"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__17_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__17_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__17_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(74, 233, 198, 147, 223, 175, 34, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__19_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__19_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__19_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__19_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_19____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "simpDIteCbv"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(190, 122, 172, 160, 23, 10, 186, 34)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 4}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1_value),((lean_object*)(((size_t)(5) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17__value;
static const lean_array_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_19_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_19____boxed(lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14__value),LEAN_SCALAR_PTR_LITERAL(115, 206, 175, 80, 231, 183, 173, 95)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(76, 195, 71, 185, 148, 180, 220, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__value),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(30, 114, 151, 242, 65, 185, 169, 185)}};
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
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
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
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
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
lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(lean_object* v_customCanUnfoldPredicate_x3f_1_, uint8_t v_canUnfoldPredicateConfig_2_, lean_object* v_cfg_3_, lean_object* v_info_4_, lean_object* v___y_5_, lean_object* v___y_6_){
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
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_customCanUnfoldPredicate_x3f_1_ = stack[0].m_obj;
uint8_t v_canUnfoldPredicateConfig_2_ = stack[1].m_num;
lean_object* v_cfg_3_ = stack[2].m_obj;
lean_object* v_info_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v_res_25_;
v_res_25_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(v_customCanUnfoldPredicate_x3f_1_, v_canUnfoldPredicateConfig_2_, v_cfg_3_, v_info_4_, v___y_5_, v___y_6_);
stack->m_obj
 = v_res_25_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed(lean_object* v_customCanUnfoldPredicate_x3f_26_, lean_object* v_canUnfoldPredicateConfig_27_, lean_object* v_cfg_28_, lean_object* v_info_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
uint8_t v_canUnfoldPredicateConfig_boxed_33_; lean_object* v_res_34_; 
v_canUnfoldPredicateConfig_boxed_33_ = lean_unbox(v_canUnfoldPredicateConfig_27_);
v_res_34_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(v_customCanUnfoldPredicate_x3f_26_, v_canUnfoldPredicateConfig_boxed_33_, v_cfg_28_, v_info_29_, v___y_30_, v___y_31_);
lean_dec(v___y_31_);
lean_dec_ref(v___y_30_);
return v_res_34_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(lean_object* v_x_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_keyedConfig_41_; uint8_t v_trackZetaDelta_42_; lean_object* v_zetaDeltaSet_43_; lean_object* v_lctx_44_; lean_object* v_localInstances_45_; lean_object* v_defEqCtx_x3f_46_; lean_object* v_synthPendingDepth_47_; lean_object* v_customCanUnfoldPredicate_x3f_48_; uint8_t v_univApprox_49_; uint8_t v_inTypeClassResolution_50_; uint8_t v_cacheInferType_51_; lean_object* v___x_52_; uint8_t v_canUnfoldPredicateConfig_53_; lean_object* v___x_54_; lean_object* v___f_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v_keyedConfig_41_ = lean_ctor_get(v_a_36_, 0);
v_trackZetaDelta_42_ = lean_ctor_get_uint8(v_a_36_, sizeof(void*)*7);
v_zetaDeltaSet_43_ = lean_ctor_get(v_a_36_, 1);
v_lctx_44_ = lean_ctor_get(v_a_36_, 2);
v_localInstances_45_ = lean_ctor_get(v_a_36_, 3);
v_defEqCtx_x3f_46_ = lean_ctor_get(v_a_36_, 4);
v_synthPendingDepth_47_ = lean_ctor_get(v_a_36_, 5);
v_customCanUnfoldPredicate_x3f_48_ = lean_ctor_get(v_a_36_, 6);
v_univApprox_49_ = lean_ctor_get_uint8(v_a_36_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_50_ = lean_ctor_get_uint8(v_a_36_, sizeof(void*)*7 + 2);
v_cacheInferType_51_ = lean_ctor_get_uint8(v_a_36_, sizeof(void*)*7 + 3);
v___x_52_ = l_Lean_Meta_Context_config(v_a_36_);
v_canUnfoldPredicateConfig_53_ = lean_ctor_get_uint8(v___x_52_, 19);
lean_dec_ref(v___x_52_);
v___x_54_ = lean_box(v_canUnfoldPredicateConfig_53_);
lean_inc(v_customCanUnfoldPredicate_x3f_48_);
v___f_55_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_55_, 0, v_customCanUnfoldPredicate_x3f_48_);
lean_closure_set(v___f_55_, 1, v___x_54_);
v___x_56_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_56_, 0, v___f_55_);
lean_inc(v_synthPendingDepth_47_);
lean_inc(v_defEqCtx_x3f_46_);
lean_inc_ref(v_localInstances_45_);
lean_inc_ref(v_lctx_44_);
lean_inc(v_zetaDeltaSet_43_);
lean_inc_ref(v_keyedConfig_41_);
v___x_57_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_57_, 0, v_keyedConfig_41_);
lean_ctor_set(v___x_57_, 1, v_zetaDeltaSet_43_);
lean_ctor_set(v___x_57_, 2, v_lctx_44_);
lean_ctor_set(v___x_57_, 3, v_localInstances_45_);
lean_ctor_set(v___x_57_, 4, v_defEqCtx_x3f_46_);
lean_ctor_set(v___x_57_, 5, v_synthPendingDepth_47_);
lean_ctor_set(v___x_57_, 6, v___x_56_);
lean_ctor_set_uint8(v___x_57_, sizeof(void*)*7, v_trackZetaDelta_42_);
lean_ctor_set_uint8(v___x_57_, sizeof(void*)*7 + 1, v_univApprox_49_);
lean_ctor_set_uint8(v___x_57_, sizeof(void*)*7 + 2, v_inTypeClassResolution_50_);
lean_ctor_set_uint8(v___x_57_, sizeof(void*)*7 + 3, v_cacheInferType_51_);
lean_inc(v_a_39_);
lean_inc_ref(v_a_38_);
lean_inc(v_a_37_);
v___x_58_ = lean_apply_5(v_x_35_, v___x_57_, v_a_37_, v_a_38_, v_a_39_, lean_box(0));
return v___x_58_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_35_ = stack[0].m_obj;
lean_object* v_a_36_ = stack[1].m_obj;
lean_object* v_a_37_ = stack[2].m_obj;
lean_object* v_a_38_ = stack[3].m_obj;
lean_object* v_a_39_ = stack[4].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v_x_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___boxed(lean_object* v_x_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v_x_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
return v_res_66_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(lean_object* v_00_u03b1_67_, lean_object* v_x_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v_x_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
return v___x_74_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_68_ = stack[1].m_obj;
lean_object* v_a_69_ = stack[2].m_obj;
lean_object* v_a_70_ = stack[3].m_obj;
lean_object* v_a_71_ = stack[4].m_obj;
lean_object* v_a_72_ = stack[5].m_obj;
lean_object* v_res_75_;
v_res_75_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(lean_box(0), v_x_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_);
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___boxed(lean_object* v_00_u03b1_76_, lean_object* v_x_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(v_00_u03b1_76_, v_x_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
return v_res_83_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg___lam__0(lean_object* v_k_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v_b_90_, lean_object* v_c_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v___x_97_; 
lean_inc(v___y_95_);
lean_inc_ref(v___y_94_);
lean_inc(v___y_93_);
lean_inc_ref(v___y_92_);
lean_inc(v___y_89_);
lean_inc_ref(v___y_88_);
lean_inc(v___y_87_);
lean_inc_ref(v___y_86_);
lean_inc(v___y_85_);
v___x_97_ = lean_apply_12(v_k_84_, v_b_90_, v_c_91_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, lean_box(0));
return v___x_97_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_84_ = stack[0].m_obj;
lean_object* v___y_85_ = stack[1].m_obj;
lean_object* v___y_86_ = stack[2].m_obj;
lean_object* v___y_87_ = stack[3].m_obj;
lean_object* v___y_88_ = stack[4].m_obj;
lean_object* v___y_89_ = stack[5].m_obj;
lean_object* v_b_90_ = stack[6].m_obj;
lean_object* v_c_91_ = stack[7].m_obj;
lean_object* v___y_92_ = stack[8].m_obj;
lean_object* v___y_93_ = stack[9].m_obj;
lean_object* v___y_94_ = stack[10].m_obj;
lean_object* v___y_95_ = stack[11].m_obj;
lean_object* v_res_98_;
v_res_98_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg___lam__0(v_k_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v_b_90_, v_c_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
stack->m_obj
 = v_res_98_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg___lam__0___boxed(lean_object* v_k_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v_b_105_, lean_object* v_c_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg___lam__0(v_k_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v_b_105_, v_c_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
return v_res_112_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg(lean_object* v_type_113_, lean_object* v_k_114_, uint8_t v_cleanupAnnotations_115_, uint8_t v_whnfType_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v___f_127_; lean_object* v___x_128_; 
lean_inc(v___y_121_);
lean_inc_ref(v___y_120_);
lean_inc(v___y_119_);
lean_inc_ref(v___y_118_);
lean_inc(v___y_117_);
v___f_127_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg___lam__0___boxed), 13, 6);
lean_closure_set(v___f_127_, 0, v_k_114_);
lean_closure_set(v___f_127_, 1, v___y_117_);
lean_closure_set(v___f_127_, 2, v___y_118_);
lean_closure_set(v___f_127_, 3, v___y_119_);
lean_closure_set(v___f_127_, 4, v___y_120_);
lean_closure_set(v___f_127_, 5, v___y_121_);
v___x_128_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_113_, v___f_127_, v_cleanupAnnotations_115_, v_whnfType_116_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
if (lean_obj_tag(v___x_128_) == 0)
{
return v___x_128_;
}
else
{
lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_136_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_136_ == 0)
{
v___x_131_ = v___x_128_;
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v___x_128_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_134_; 
if (v_isShared_132_ == 0)
{
v___x_134_ = v___x_131_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_a_129_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_113_ = stack[0].m_obj;
lean_object* v_k_114_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_115_ = stack[2].m_num;
uint8_t v_whnfType_116_ = stack[3].m_num;
lean_object* v___y_117_ = stack[4].m_obj;
lean_object* v___y_118_ = stack[5].m_obj;
lean_object* v___y_119_ = stack[6].m_obj;
lean_object* v___y_120_ = stack[7].m_obj;
lean_object* v___y_121_ = stack[8].m_obj;
lean_object* v___y_122_ = stack[9].m_obj;
lean_object* v___y_123_ = stack[10].m_obj;
lean_object* v___y_124_ = stack[11].m_obj;
lean_object* v___y_125_ = stack[12].m_obj;
lean_object* v_res_137_;
v_res_137_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg(v_type_113_, v_k_114_, v_cleanupAnnotations_115_, v_whnfType_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
stack->m_obj
 = v_res_137_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg___boxed(lean_object* v_type_138_, lean_object* v_k_139_, lean_object* v_cleanupAnnotations_140_, lean_object* v_whnfType_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_152_; uint8_t v_whnfType_boxed_153_; lean_object* v_res_154_; 
v_cleanupAnnotations_boxed_152_ = lean_unbox(v_cleanupAnnotations_140_);
v_whnfType_boxed_153_ = lean_unbox(v_whnfType_141_);
v_res_154_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg(v_type_138_, v_k_139_, v_cleanupAnnotations_boxed_152_, v_whnfType_boxed_153_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
return v_res_154_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0(lean_object* v_00_u03b1_155_, lean_object* v_type_156_, lean_object* v_k_157_, uint8_t v_cleanupAnnotations_158_, uint8_t v_whnfType_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg(v_type_156_, v_k_157_, v_cleanupAnnotations_158_, v_whnfType_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
return v___x_170_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_156_ = stack[1].m_obj;
lean_object* v_k_157_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_158_ = stack[3].m_num;
uint8_t v_whnfType_159_ = stack[4].m_num;
lean_object* v___y_160_ = stack[5].m_obj;
lean_object* v___y_161_ = stack[6].m_obj;
lean_object* v___y_162_ = stack[7].m_obj;
lean_object* v___y_163_ = stack[8].m_obj;
lean_object* v___y_164_ = stack[9].m_obj;
lean_object* v___y_165_ = stack[10].m_obj;
lean_object* v___y_166_ = stack[11].m_obj;
lean_object* v___y_167_ = stack[12].m_obj;
lean_object* v___y_168_ = stack[13].m_obj;
lean_object* v_res_171_;
v_res_171_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0(lean_box(0), v_type_156_, v_k_157_, v_cleanupAnnotations_158_, v_whnfType_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
stack->m_obj
 = v_res_171_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___boxed(lean_object* v_00_u03b1_172_, lean_object* v_type_173_, lean_object* v_k_174_, lean_object* v_cleanupAnnotations_175_, lean_object* v_whnfType_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_187_; uint8_t v_whnfType_boxed_188_; lean_object* v_res_189_; 
v_cleanupAnnotations_boxed_187_ = lean_unbox(v_cleanupAnnotations_175_);
v_whnfType_boxed_188_ = lean_unbox(v_whnfType_176_);
v_res_189_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0(v_00_u03b1_172_, v_type_173_, v_k_174_, v_cleanupAnnotations_boxed_187_, v_whnfType_boxed_188_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
return v_res_189_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(lean_object* v_f_190_, lean_object* v_a_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v___y_200_; lean_object* v___x_203_; uint8_t v_debug_204_; 
v___x_203_ = lean_st_ref_get(v___y_193_);
v_debug_204_ = lean_ctor_get_uint8(v___x_203_, sizeof(void*)*12);
lean_dec(v___x_203_);
if (v_debug_204_ == 0)
{
v___y_200_ = v___y_193_;
goto v___jp_199_;
}
else
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_190_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v___x_206_; 
lean_dec_ref_known(v___x_205_, 1);
v___x_206_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_dec_ref_known(v___x_206_, 1);
v___y_200_ = v___y_193_;
goto v___jp_199_;
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
lean_dec_ref(v_a_191_);
lean_dec_ref(v_f_190_);
v_a_207_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_206_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_206_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
lean_dec_ref(v_a_191_);
lean_dec_ref(v_f_190_);
v_a_215_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_205_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_205_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
v___jp_199_:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = l_Lean_Expr_app___override(v_f_190_, v_a_191_);
v___x_202_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_201_, v___y_200_);
return v___x_202_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_190_ = stack[0].m_obj;
lean_object* v_a_191_ = stack[1].m_obj;
lean_object* v___y_192_ = stack[2].m_obj;
lean_object* v___y_193_ = stack[3].m_obj;
lean_object* v___y_194_ = stack[4].m_obj;
lean_object* v___y_195_ = stack[5].m_obj;
lean_object* v___y_196_ = stack[6].m_obj;
lean_object* v___y_197_ = stack[7].m_obj;
lean_object* v_res_223_;
v_res_223_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(v_f_190_, v_a_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
stack->m_obj
 = v_res_223_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_f_224_, lean_object* v_a_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(v_f_224_, v_a_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
return v_res_233_;
}
}
lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1(lean_object* v_args_234_, lean_object* v_endIdx_235_, lean_object* v_b_236_, lean_object* v_i_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
uint8_t v___x_248_; 
v___x_248_ = lean_nat_dec_le(v_endIdx_235_, v_i_237_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_249_ = l_Lean_instInhabitedExpr;
v___x_250_ = lean_array_get_borrowed(v___x_249_, v_args_234_, v_i_237_);
lean_inc(v___x_250_);
v___x_251_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(v_b_236_, v___x_250_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_a_252_);
lean_dec_ref_known(v___x_251_, 1);
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = lean_nat_add(v_i_237_, v___x_253_);
lean_dec(v_i_237_);
v_b_236_ = v_a_252_;
v_i_237_ = v___x_254_;
goto _start;
}
else
{
lean_dec(v_i_237_);
return v___x_251_;
}
}
else
{
lean_object* v___x_256_; 
lean_dec(v_i_237_);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v_b_236_);
return v___x_256_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_234_ = stack[0].m_obj;
lean_object* v_endIdx_235_ = stack[1].m_obj;
lean_object* v_b_236_ = stack[2].m_obj;
lean_object* v_i_237_ = stack[3].m_obj;
lean_object* v___y_238_ = stack[4].m_obj;
lean_object* v___y_239_ = stack[5].m_obj;
lean_object* v___y_240_ = stack[6].m_obj;
lean_object* v___y_241_ = stack[7].m_obj;
lean_object* v___y_242_ = stack[8].m_obj;
lean_object* v___y_243_ = stack[9].m_obj;
lean_object* v___y_244_ = stack[10].m_obj;
lean_object* v___y_245_ = stack[11].m_obj;
lean_object* v___y_246_ = stack[12].m_obj;
lean_object* v_res_257_;
v_res_257_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1(v_args_234_, v_endIdx_235_, v_b_236_, v_i_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
stack->m_obj
 = v_res_257_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1___boxed(lean_object* v_args_258_, lean_object* v_endIdx_259_, lean_object* v_b_260_, lean_object* v_i_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1(v_args_258_, v_endIdx_259_, v_b_260_, v_i_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec(v_endIdx_259_);
lean_dec_ref(v_args_258_);
return v_res_272_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1(lean_object* v_f_273_, lean_object* v_args_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = lean_array_get_size(v_args_274_);
v___x_287_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1(v_args_274_, v___x_286_, v_f_273_, v___x_285_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
return v___x_287_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_273_ = stack[0].m_obj;
lean_object* v_args_274_ = stack[1].m_obj;
lean_object* v___y_275_ = stack[2].m_obj;
lean_object* v___y_276_ = stack[3].m_obj;
lean_object* v___y_277_ = stack[4].m_obj;
lean_object* v___y_278_ = stack[5].m_obj;
lean_object* v___y_279_ = stack[6].m_obj;
lean_object* v___y_280_ = stack[7].m_obj;
lean_object* v___y_281_ = stack[8].m_obj;
lean_object* v___y_282_ = stack[9].m_obj;
lean_object* v___y_283_ = stack[10].m_obj;
lean_object* v_res_288_;
v_res_288_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1(v_f_273_, v_args_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
stack->m_obj
 = v_res_288_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1___boxed(lean_object* v_f_289_, lean_object* v_args_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1(v_f_289_, v_args_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v_args_290_);
return v_res_301_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0(uint8_t v___x_305_, lean_object* v_inst_306_, lean_object* v___x_307_, uint8_t v___x_308_, lean_object* v_vars_309_, lean_object* v_body_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_326_ = l_Lean_Expr_cleanupAnnotations(v_body_310_);
v___x_327_ = l_Lean_Expr_isApp(v___x_326_);
if (v___x_327_ == 0)
{
lean_dec_ref(v___x_326_);
goto v___jp_321_;
}
else
{
lean_object* v_arg_328_; lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v_arg_328_ = lean_ctor_get(v___x_326_, 1);
lean_inc_ref(v_arg_328_);
v___x_329_ = l_Lean_Expr_appFnCleanup___redArg(v___x_326_);
v___x_330_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0___closed__1));
v___x_331_ = l_Lean_Expr_isConstOf(v___x_329_, v___x_330_);
lean_dec_ref(v___x_329_);
if (v___x_331_ == 0)
{
lean_dec_ref(v_arg_328_);
goto v___jp_321_;
}
else
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = lean_array_get_size(v_vars_309_);
v___x_333_ = lean_nat_dec_eq(v___x_332_, v___x_307_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec_ref(v_arg_328_);
v___x_334_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_334_, 0, v___x_333_);
lean_ctor_set_uint8(v___x_334_, 1, v___x_333_);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v_inst_306_);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
else
{
uint8_t v___x_338_; lean_object* v___x_339_; 
lean_dec_ref(v_inst_306_);
v___x_338_ = 1;
v___x_339_ = l_Lean_Meta_mkLambdaFVars(v_vars_309_, v_arg_328_, v___x_305_, v___x_308_, v___x_305_, v___x_308_, v___x_338_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_348_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_348_ == 0)
{
v___x_342_ = v___x_339_;
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_348_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_344_, 0, v_a_340_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v___x_344_);
v___x_346_ = v___x_342_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
v_a_349_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_339_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_339_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
}
v___jp_321_:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_322_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_322_, 0, v___x_305_);
lean_ctor_set_uint8(v___x_322_, 1, v___x_305_);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v_inst_306_);
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_305_ = stack[0].m_num;
lean_object* v_inst_306_ = stack[1].m_obj;
lean_object* v___x_307_ = stack[2].m_obj;
uint8_t v___x_308_ = stack[3].m_num;
lean_object* v_vars_309_ = stack[4].m_obj;
lean_object* v_body_310_ = stack[5].m_obj;
lean_object* v___y_311_ = stack[6].m_obj;
lean_object* v___y_312_ = stack[7].m_obj;
lean_object* v___y_313_ = stack[8].m_obj;
lean_object* v___y_314_ = stack[9].m_obj;
lean_object* v___y_315_ = stack[10].m_obj;
lean_object* v___y_316_ = stack[11].m_obj;
lean_object* v___y_317_ = stack[12].m_obj;
lean_object* v___y_318_ = stack[13].m_obj;
lean_object* v___y_319_ = stack[14].m_obj;
lean_object* v_res_357_;
v_res_357_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0(v___x_305_, v_inst_306_, v___x_307_, v___x_308_, v_vars_309_, v_body_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
stack->m_obj
 = v_res_357_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0___boxed(lean_object* v___x_358_, lean_object* v_inst_359_, lean_object* v___x_360_, lean_object* v___x_361_, lean_object* v_vars_362_, lean_object* v_body_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
uint8_t v___x_17614__boxed_374_; uint8_t v___x_17616__boxed_375_; lean_object* v_res_376_; 
v___x_17614__boxed_374_ = lean_unbox(v___x_358_);
v___x_17616__boxed_375_ = lean_unbox(v___x_361_);
v_res_376_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0(v___x_17614__boxed_374_, v_inst_359_, v___x_360_, v___x_17616__boxed_375_, v_vars_362_, v_body_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v_vars_362_);
lean_dec(v___x_360_);
return v_res_376_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2(lean_object* v_inst_379_, lean_object* v_x_380_, lean_object* v_x_381_, lean_object* v_x_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
if (lean_obj_tag(v_x_380_) == 5)
{
lean_object* v_fn_393_; lean_object* v_arg_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_fn_393_ = lean_ctor_get(v_x_380_, 0);
lean_inc_ref(v_fn_393_);
v_arg_394_ = lean_ctor_get(v_x_380_, 1);
lean_inc_ref(v_arg_394_);
lean_dec_ref_known(v_x_380_, 2);
v___x_395_ = lean_array_set(v_x_381_, v_x_382_, v_arg_394_);
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_nat_sub(v_x_382_, v___x_396_);
lean_dec(v_x_382_);
v_x_380_ = v_fn_393_;
v_x_381_ = v___x_395_;
v_x_382_ = v___x_397_;
goto _start;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
lean_dec(v_x_382_);
v___x_399_ = lean_array_get_size(v_x_381_);
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = lean_nat_dec_eq(v___x_399_, v___x_400_);
if (v___x_401_ == 0)
{
uint8_t v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___f_405_; lean_object* v___x_406_; 
v___x_402_ = 1;
v___x_403_ = lean_box(v___x_401_);
v___x_404_ = lean_box(v___x_402_);
lean_inc_ref(v_inst_379_);
v___f_405_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0___boxed), 16, 4);
lean_closure_set(v___f_405_, 0, v___x_403_);
lean_closure_set(v___f_405_, 1, v_inst_379_);
lean_closure_set(v___f_405_, 2, v___x_399_);
lean_closure_set(v___f_405_, 3, v___x_404_);
lean_inc(v___y_391_);
lean_inc_ref(v___y_390_);
lean_inc(v___y_389_);
lean_inc_ref(v___y_388_);
lean_inc_ref(v_x_380_);
v___x_406_ = lean_infer_type(v_x_380_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_408_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_406_, 1);
v___x_408_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__0___redArg(v_a_407_, v___f_405_, v___x_401_, v___x_402_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_489_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_489_ == 0)
{
v___x_411_ = v___x_408_;
v_isShared_412_ = v_isSharedCheck_489_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_489_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
if (lean_obj_tag(v_a_409_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_415_; 
lean_dec_ref(v_x_381_);
lean_dec_ref(v_x_380_);
lean_dec_ref(v_inst_379_);
v_a_413_ = lean_ctor_get(v_a_409_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v_a_409_, 1);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v_a_413_);
v___x_415_ = v___x_411_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_418_; 
lean_del_object(v___x_411_);
v_a_417_ = lean_ctor_get(v_a_409_, 0);
lean_inc(v_a_417_);
lean_dec_ref_known(v_a_409_, 1);
v___x_418_ = l_Lean_Meta_Sym_shareCommon(v_a_417_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_420_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc_n(v_a_419_, 2);
lean_dec_ref_known(v___x_418_, 1);
v___x_420_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1(v_a_419_, v_x_381_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
lean_dec_ref(v_x_381_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_422_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v___x_420_, 1);
v___x_422_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_a_421_, v___x_400_, v___x_399_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_422_) == 0)
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_464_; 
v_a_423_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_464_ == 0)
{
v___x_425_ = v___x_422_;
v_isShared_426_ = v_isSharedCheck_464_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_464_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
if (lean_obj_tag(v_a_423_) == 0)
{
lean_object* v___x_427_; lean_object* v___x_429_; 
lean_dec(v_a_419_);
lean_dec_ref(v_x_380_);
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v_a_423_);
lean_ctor_set(v___x_427_, 1, v_inst_379_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_427_);
v___x_429_ = v___x_425_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
else
{
lean_object* v_e_x27_431_; lean_object* v_proof_432_; uint8_t v_done_433_; uint8_t v_contextDependent_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_463_; 
lean_del_object(v___x_425_);
lean_dec_ref(v_inst_379_);
v_e_x27_431_ = lean_ctor_get(v_a_423_, 0);
v_proof_432_ = lean_ctor_get(v_a_423_, 1);
v_done_433_ = lean_ctor_get_uint8(v_a_423_, sizeof(void*)*2);
v_contextDependent_434_ = lean_ctor_get_uint8(v_a_423_, sizeof(void*)*2 + 1);
v_isSharedCheck_463_ = !lean_is_exclusive(v_a_423_);
if (v_isSharedCheck_463_ == 0)
{
v___x_436_ = v_a_423_;
v_isShared_437_ = v_isSharedCheck_463_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_proof_432_);
lean_inc(v_e_x27_431_);
lean_dec(v_a_423_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_463_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_438_ = l_Lean_Expr_getAppNumArgs(v_e_x27_431_);
v___x_439_ = lean_mk_empty_array_with_capacity(v___x_438_);
lean_dec(v___x_438_);
v___x_440_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v_e_x27_431_, v___x_439_);
lean_inc_ref(v___x_440_);
v___x_441_ = l_Lean_Meta_Sym_betaRevS(v_a_419_, v___x_440_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_454_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_454_ == 0)
{
v___x_444_ = v___x_441_;
v_isShared_445_ = v_isSharedCheck_454_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_441_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_454_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v_a_442_);
v___x_447_ = v___x_436_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_442_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_proof_432_);
lean_ctor_set_uint8(v_reuseFailAlloc_453_, sizeof(void*)*2, v_done_433_);
lean_ctor_set_uint8(v_reuseFailAlloc_453_, sizeof(void*)*2 + 1, v_contextDependent_434_);
v___x_447_ = v_reuseFailAlloc_453_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v___x_448_ = l_Lean_mkAppRev(v_x_380_, v___x_440_);
lean_dec_ref(v___x_440_);
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_447_);
lean_ctor_set(v___x_449_, 1, v___x_448_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_449_);
v___x_451_ = v___x_444_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
lean_dec_ref(v___x_440_);
lean_del_object(v___x_436_);
lean_dec_ref(v_proof_432_);
lean_dec_ref(v_x_380_);
v_a_455_ = lean_ctor_get(v___x_441_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_441_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_441_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_441_);
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
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec(v_a_419_);
lean_dec_ref(v_x_380_);
lean_dec_ref(v_inst_379_);
v_a_465_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_422_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_422_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec(v_a_419_);
lean_dec_ref(v_x_380_);
lean_dec_ref(v_inst_379_);
v_a_473_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_420_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_420_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_dec_ref(v_x_381_);
lean_dec_ref(v_x_380_);
lean_dec_ref(v_inst_379_);
v_a_481_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_418_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_418_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec_ref(v_x_381_);
lean_dec_ref(v_x_380_);
lean_dec_ref(v_inst_379_);
v_a_490_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_408_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_408_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_dec_ref(v___f_405_);
lean_dec_ref(v_x_381_);
lean_dec_ref(v_x_380_);
lean_dec_ref(v_inst_379_);
v_a_498_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_406_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_406_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec_ref(v_x_381_);
lean_dec_ref(v_x_380_);
v___x_506_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___closed__0));
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v_inst_379_);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
return v___x_508_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_379_ = stack[0].m_obj;
lean_object* v_x_380_ = stack[1].m_obj;
lean_object* v_x_381_ = stack[2].m_obj;
lean_object* v_x_382_ = stack[3].m_obj;
lean_object* v___y_383_ = stack[4].m_obj;
lean_object* v___y_384_ = stack[5].m_obj;
lean_object* v___y_385_ = stack[6].m_obj;
lean_object* v___y_386_ = stack[7].m_obj;
lean_object* v___y_387_ = stack[8].m_obj;
lean_object* v___y_388_ = stack[9].m_obj;
lean_object* v___y_389_ = stack[10].m_obj;
lean_object* v___y_390_ = stack[11].m_obj;
lean_object* v___y_391_ = stack[12].m_obj;
lean_object* v_res_509_;
v_res_509_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2(v_inst_379_, v_x_380_, v_x_381_, v_x_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
stack->m_obj
 = v_res_509_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___boxed(lean_object* v_inst_510_, lean_object* v_x_511_, lean_object* v_x_512_, lean_object* v_x_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2(v_inst_510_, v_x_511_, v_x_512_, v_x_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
return v_res_524_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance___closed__0(void){
_start:
{
lean_object* v___x_525_; lean_object* v_dummy_526_; 
v___x_525_ = lean_box(0);
v_dummy_526_ = l_Lean_Expr_sort___override(v___x_525_);
return v_dummy_526_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance(lean_object* v_inst_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_dummy_538_; lean_object* v_nargs_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v_dummy_538_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance___closed__0, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance___closed__0_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance___closed__0);
v_nargs_539_ = l_Lean_Expr_getAppNumArgs(v_inst_527_);
lean_inc(v_nargs_539_);
v___x_540_ = lean_mk_array(v_nargs_539_, v_dummy_538_);
v___x_541_ = lean_unsigned_to_nat(1u);
v___x_542_ = lean_nat_sub(v_nargs_539_, v___x_541_);
lean_dec(v_nargs_539_);
lean_inc_ref(v_inst_527_);
v___x_543_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2(v_inst_527_, v_inst_527_, v___x_540_, v___x_542_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
return v___x_543_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_527_ = stack[0].m_obj;
lean_object* v_a_528_ = stack[1].m_obj;
lean_object* v_a_529_ = stack[2].m_obj;
lean_object* v_a_530_ = stack[3].m_obj;
lean_object* v_a_531_ = stack[4].m_obj;
lean_object* v_a_532_ = stack[5].m_obj;
lean_object* v_a_533_ = stack[6].m_obj;
lean_object* v_a_534_ = stack[7].m_obj;
lean_object* v_a_535_ = stack[8].m_obj;
lean_object* v_a_536_ = stack[9].m_obj;
lean_object* v_res_544_;
v_res_544_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance(v_inst_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
stack->m_obj
 = v_res_544_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance___boxed(lean_object* v_inst_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance(v_inst_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_);
lean_dec(v_a_554_);
lean_dec_ref(v_a_553_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
return v_res_556_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2(lean_object* v_f_557_, lean_object* v_a_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(v_f_557_, v_a_558_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
return v___x_569_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_557_ = stack[0].m_obj;
lean_object* v_a_558_ = stack[1].m_obj;
lean_object* v___y_559_ = stack[2].m_obj;
lean_object* v___y_560_ = stack[3].m_obj;
lean_object* v___y_561_ = stack[4].m_obj;
lean_object* v___y_562_ = stack[5].m_obj;
lean_object* v___y_563_ = stack[6].m_obj;
lean_object* v___y_564_ = stack[7].m_obj;
lean_object* v___y_565_ = stack[8].m_obj;
lean_object* v___y_566_ = stack[9].m_obj;
lean_object* v___y_567_ = stack[10].m_obj;
lean_object* v_res_570_;
v_res_570_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2(v_f_557_, v_a_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
stack->m_obj
 = v_res_570_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___boxed(lean_object* v_f_571_, lean_object* v_a_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2(v_f_571_, v_a_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
return v_res_583_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(lean_object* v_f_609_, lean_object* v_00_u03b1_610_, lean_object* v_c_611_, lean_object* v_inst_612_, lean_object* v_a_613_, lean_object* v_b_614_, lean_object* v_instToMatch_615_, lean_object* v_fallback_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_instToMatch_615_, v_a_623_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_628_);
lean_dec_ref_known(v___x_627_, 1);
v___x_629_ = l_Lean_Expr_cleanupAnnotations(v_a_628_);
v___x_630_ = l_Lean_Expr_isApp(v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; 
lean_dec_ref(v___x_629_);
lean_dec_ref(v_b_614_);
lean_dec_ref(v_a_613_);
lean_dec_ref(v_inst_612_);
lean_dec_ref(v_c_611_);
lean_dec_ref(v_00_u03b1_610_);
lean_inc(v_a_625_);
lean_inc_ref(v_a_624_);
lean_inc(v_a_623_);
lean_inc_ref(v_a_622_);
lean_inc(v_a_621_);
lean_inc_ref(v_a_620_);
lean_inc(v_a_619_);
lean_inc_ref(v_a_618_);
lean_inc(v_a_617_);
v___x_631_ = lean_apply_10(v_fallback_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, lean_box(0));
return v___x_631_;
}
else
{
lean_object* v_arg_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v_arg_632_ = lean_ctor_get(v___x_629_, 1);
lean_inc_ref(v_arg_632_);
v___x_633_ = l_Lean_Expr_appFnCleanup___redArg(v___x_629_);
v___x_634_ = l_Lean_Expr_isApp(v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
lean_dec_ref(v___x_633_);
lean_dec_ref(v_arg_632_);
lean_dec_ref(v_b_614_);
lean_dec_ref(v_a_613_);
lean_dec_ref(v_inst_612_);
lean_dec_ref(v_c_611_);
lean_dec_ref(v_00_u03b1_610_);
lean_inc(v_a_625_);
lean_inc_ref(v_a_624_);
lean_inc(v_a_623_);
lean_inc_ref(v_a_622_);
lean_inc(v_a_621_);
lean_inc_ref(v_a_620_);
lean_inc(v_a_619_);
lean_inc_ref(v_a_618_);
lean_inc(v_a_617_);
v___x_635_ = lean_apply_10(v_fallback_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, lean_box(0));
return v___x_635_;
}
else
{
lean_object* v_arg_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_arg_636_ = lean_ctor_get(v___x_633_, 1);
lean_inc_ref(v_arg_636_);
v___x_637_ = l_Lean_Expr_appFnCleanup___redArg(v___x_633_);
v___x_638_ = l_Lean_Expr_isApp(v___x_637_);
if (v___x_638_ == 0)
{
lean_object* v___x_639_; 
lean_dec_ref(v___x_637_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v_arg_632_);
lean_dec_ref(v_b_614_);
lean_dec_ref(v_a_613_);
lean_dec_ref(v_inst_612_);
lean_dec_ref(v_c_611_);
lean_dec_ref(v_00_u03b1_610_);
lean_inc(v_a_625_);
lean_inc_ref(v_a_624_);
lean_inc(v_a_623_);
lean_inc_ref(v_a_622_);
lean_inc(v_a_621_);
lean_inc_ref(v_a_620_);
lean_inc(v_a_619_);
lean_inc_ref(v_a_618_);
lean_inc(v_a_617_);
v___x_639_ = lean_apply_10(v_fallback_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, lean_box(0));
return v___x_639_;
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_640_ = l_Lean_Expr_appFnCleanup___redArg(v___x_637_);
v___x_641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_642_ = l_Lean_Expr_isConstOf(v___x_640_, v___x_641_);
lean_dec_ref(v___x_640_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
lean_dec_ref(v_arg_636_);
lean_dec_ref(v_arg_632_);
lean_dec_ref(v_b_614_);
lean_dec_ref(v_a_613_);
lean_dec_ref(v_inst_612_);
lean_dec_ref(v_c_611_);
lean_dec_ref(v_00_u03b1_610_);
lean_inc(v_a_625_);
lean_inc_ref(v_a_624_);
lean_inc(v_a_623_);
lean_inc_ref(v_a_622_);
lean_inc(v_a_621_);
lean_inc_ref(v_a_620_);
lean_inc(v_a_619_);
lean_inc_ref(v_a_618_);
lean_inc(v_a_617_);
v___x_643_ = lean_apply_10(v_fallback_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, lean_box(0));
return v___x_643_;
}
else
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_636_, v_a_623_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_672_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_672_ == 0)
{
v___x_647_ = v___x_644_;
v_isShared_648_ = v_isSharedCheck_672_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_672_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_649_ = l_Lean_Expr_cleanupAnnotations(v_a_645_);
v___x_650_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_651_ = l_Lean_Expr_isConstOf(v___x_649_, v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_652_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_653_ = l_Lean_Expr_isConstOf(v___x_649_, v___x_652_);
lean_dec_ref(v___x_649_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
lean_del_object(v___x_647_);
lean_dec_ref(v_arg_632_);
lean_dec_ref(v_b_614_);
lean_dec_ref(v_a_613_);
lean_dec_ref(v_inst_612_);
lean_dec_ref(v_c_611_);
lean_dec_ref(v_00_u03b1_610_);
lean_inc(v_a_625_);
lean_inc_ref(v_a_624_);
lean_inc(v_a_623_);
lean_inc_ref(v_a_622_);
lean_inc(v_a_621_);
lean_inc_ref(v_a_620_);
lean_inc(v_a_619_);
lean_inc_ref(v_a_618_);
lean_inc(v_a_617_);
v___x_654_ = lean_apply_10(v_fallback_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, lean_box(0));
return v___x_654_;
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
lean_dec_ref(v_fallback_616_);
v___x_655_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__10));
v___x_656_ = l_Lean_Expr_constLevels_x21(v_f_609_);
v___x_657_ = l_Lean_mkConst(v___x_655_, v___x_656_);
lean_inc_ref(v_a_613_);
v___x_658_ = l_Lean_mkApp6(v___x_657_, v_00_u03b1_610_, v_c_611_, v_inst_612_, v_a_613_, v_b_614_, v_arg_632_);
v___x_659_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_659_, 0, v_a_613_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*2, v___x_651_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*2 + 1, v___x_651_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_659_);
v___x_661_ = v___x_647_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
lean_dec_ref(v___x_649_);
lean_dec_ref(v_fallback_616_);
v___x_663_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__12));
v___x_664_ = l_Lean_Expr_constLevels_x21(v_f_609_);
v___x_665_ = l_Lean_mkConst(v___x_663_, v___x_664_);
lean_inc_ref(v_b_614_);
v___x_666_ = l_Lean_mkApp6(v___x_665_, v_00_u03b1_610_, v_c_611_, v_inst_612_, v_a_613_, v_b_614_, v_arg_632_);
v___x_667_ = 0;
v___x_668_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_668_, 0, v_b_614_);
lean_ctor_set(v___x_668_, 1, v___x_666_);
lean_ctor_set_uint8(v___x_668_, sizeof(void*)*2, v___x_667_);
lean_ctor_set_uint8(v___x_668_, sizeof(void*)*2 + 1, v___x_667_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_668_);
v___x_670_ = v___x_647_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_dec_ref(v_arg_632_);
lean_dec_ref(v_fallback_616_);
lean_dec_ref(v_b_614_);
lean_dec_ref(v_a_613_);
lean_dec_ref(v_inst_612_);
lean_dec_ref(v_c_611_);
lean_dec_ref(v_00_u03b1_610_);
v_a_673_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_644_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_644_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
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
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec_ref(v_fallback_616_);
lean_dec_ref(v_b_614_);
lean_dec_ref(v_a_613_);
lean_dec_ref(v_inst_612_);
lean_dec_ref(v_c_611_);
lean_dec_ref(v_00_u03b1_610_);
v_a_681_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_627_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_627_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_609_ = stack[0].m_obj;
lean_object* v_00_u03b1_610_ = stack[1].m_obj;
lean_object* v_c_611_ = stack[2].m_obj;
lean_object* v_inst_612_ = stack[3].m_obj;
lean_object* v_a_613_ = stack[4].m_obj;
lean_object* v_b_614_ = stack[5].m_obj;
lean_object* v_instToMatch_615_ = stack[6].m_obj;
lean_object* v_fallback_616_ = stack[7].m_obj;
lean_object* v_a_617_ = stack[8].m_obj;
lean_object* v_a_618_ = stack[9].m_obj;
lean_object* v_a_619_ = stack[10].m_obj;
lean_object* v_a_620_ = stack[11].m_obj;
lean_object* v_a_621_ = stack[12].m_obj;
lean_object* v_a_622_ = stack[13].m_obj;
lean_object* v_a_623_ = stack[14].m_obj;
lean_object* v_a_624_ = stack[15].m_obj;
lean_object* v_a_625_ = stack[16].m_obj;
lean_object* v_res_689_;
v_res_689_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(v_f_609_, v_00_u03b1_610_, v_c_611_, v_inst_612_, v_a_613_, v_b_614_, v_instToMatch_615_, v_fallback_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
stack->m_obj
 = v_res_689_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___boxed(lean_object** _args){
lean_object* v_f_690_ = _args[0];
lean_object* v_00_u03b1_691_ = _args[1];
lean_object* v_c_692_ = _args[2];
lean_object* v_inst_693_ = _args[3];
lean_object* v_a_694_ = _args[4];
lean_object* v_b_695_ = _args[5];
lean_object* v_instToMatch_696_ = _args[6];
lean_object* v_fallback_697_ = _args[7];
lean_object* v_a_698_ = _args[8];
lean_object* v_a_699_ = _args[9];
lean_object* v_a_700_ = _args[10];
lean_object* v_a_701_ = _args[11];
lean_object* v_a_702_ = _args[12];
lean_object* v_a_703_ = _args[13];
lean_object* v_a_704_ = _args[14];
lean_object* v_a_705_ = _args[15];
lean_object* v_a_706_ = _args[16];
lean_object* v_a_707_ = _args[17];
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(v_f_690_, v_00_u03b1_691_, v_c_692_, v_inst_693_, v_a_694_, v_b_695_, v_instToMatch_696_, v_fallback_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_f_690_);
return v_res_708_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(lean_object* v_f_719_, lean_object* v_00_u03b1_720_, lean_object* v_c_721_, lean_object* v_inst_722_, lean_object* v_a_723_, lean_object* v_b_724_, lean_object* v_c_x27_725_, lean_object* v_h_726_, lean_object* v_inst_x27_727_, lean_object* v_fallback_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_x27_727_, v_a_735_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
lean_dec_ref_known(v___x_739_, 1);
v___x_741_ = l_Lean_Expr_cleanupAnnotations(v_a_740_);
v___x_742_ = l_Lean_Expr_isApp(v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
lean_dec_ref(v___x_741_);
lean_dec_ref(v_h_726_);
lean_dec_ref(v_c_x27_725_);
lean_dec_ref(v_b_724_);
lean_dec_ref(v_a_723_);
lean_dec_ref(v_inst_722_);
lean_dec_ref(v_c_721_);
lean_dec_ref(v_00_u03b1_720_);
lean_inc(v_a_737_);
lean_inc_ref(v_a_736_);
lean_inc(v_a_735_);
lean_inc_ref(v_a_734_);
lean_inc(v_a_733_);
lean_inc_ref(v_a_732_);
lean_inc(v_a_731_);
lean_inc_ref(v_a_730_);
lean_inc(v_a_729_);
v___x_743_ = lean_apply_10(v_fallback_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, lean_box(0));
return v___x_743_;
}
else
{
lean_object* v_arg_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v_arg_744_ = lean_ctor_get(v___x_741_, 1);
lean_inc_ref(v_arg_744_);
v___x_745_ = l_Lean_Expr_appFnCleanup___redArg(v___x_741_);
v___x_746_ = l_Lean_Expr_isApp(v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; 
lean_dec_ref(v___x_745_);
lean_dec_ref(v_arg_744_);
lean_dec_ref(v_h_726_);
lean_dec_ref(v_c_x27_725_);
lean_dec_ref(v_b_724_);
lean_dec_ref(v_a_723_);
lean_dec_ref(v_inst_722_);
lean_dec_ref(v_c_721_);
lean_dec_ref(v_00_u03b1_720_);
lean_inc(v_a_737_);
lean_inc_ref(v_a_736_);
lean_inc(v_a_735_);
lean_inc_ref(v_a_734_);
lean_inc(v_a_733_);
lean_inc_ref(v_a_732_);
lean_inc(v_a_731_);
lean_inc_ref(v_a_730_);
lean_inc(v_a_729_);
v___x_747_ = lean_apply_10(v_fallback_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, lean_box(0));
return v___x_747_;
}
else
{
lean_object* v_arg_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v_arg_748_ = lean_ctor_get(v___x_745_, 1);
lean_inc_ref(v_arg_748_);
v___x_749_ = l_Lean_Expr_appFnCleanup___redArg(v___x_745_);
v___x_750_ = l_Lean_Expr_isApp(v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; 
lean_dec_ref(v___x_749_);
lean_dec_ref(v_arg_748_);
lean_dec_ref(v_arg_744_);
lean_dec_ref(v_h_726_);
lean_dec_ref(v_c_x27_725_);
lean_dec_ref(v_b_724_);
lean_dec_ref(v_a_723_);
lean_dec_ref(v_inst_722_);
lean_dec_ref(v_c_721_);
lean_dec_ref(v_00_u03b1_720_);
lean_inc(v_a_737_);
lean_inc_ref(v_a_736_);
lean_inc(v_a_735_);
lean_inc_ref(v_a_734_);
lean_inc(v_a_733_);
lean_inc_ref(v_a_732_);
lean_inc(v_a_731_);
lean_inc_ref(v_a_730_);
lean_inc(v_a_729_);
v___x_751_ = lean_apply_10(v_fallback_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, lean_box(0));
return v___x_751_;
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_752_ = l_Lean_Expr_appFnCleanup___redArg(v___x_749_);
v___x_753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_754_ = l_Lean_Expr_isConstOf(v___x_752_, v___x_753_);
lean_dec_ref(v___x_752_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; 
lean_dec_ref(v_arg_748_);
lean_dec_ref(v_arg_744_);
lean_dec_ref(v_h_726_);
lean_dec_ref(v_c_x27_725_);
lean_dec_ref(v_b_724_);
lean_dec_ref(v_a_723_);
lean_dec_ref(v_inst_722_);
lean_dec_ref(v_c_721_);
lean_dec_ref(v_00_u03b1_720_);
lean_inc(v_a_737_);
lean_inc_ref(v_a_736_);
lean_inc(v_a_735_);
lean_inc_ref(v_a_734_);
lean_inc(v_a_733_);
lean_inc_ref(v_a_732_);
lean_inc(v_a_731_);
lean_inc_ref(v_a_730_);
lean_inc(v_a_729_);
v___x_755_ = lean_apply_10(v_fallback_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, lean_box(0));
return v___x_755_;
}
else
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_748_, v_a_735_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_784_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_784_ == 0)
{
v___x_759_ = v___x_756_;
v_isShared_760_ = v_isSharedCheck_784_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_756_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_784_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_761_ = l_Lean_Expr_cleanupAnnotations(v_a_757_);
v___x_762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_763_ = l_Lean_Expr_isConstOf(v___x_761_, v___x_762_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_765_ = l_Lean_Expr_isConstOf(v___x_761_, v___x_764_);
lean_dec_ref(v___x_761_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; 
lean_del_object(v___x_759_);
lean_dec_ref(v_arg_744_);
lean_dec_ref(v_h_726_);
lean_dec_ref(v_c_x27_725_);
lean_dec_ref(v_b_724_);
lean_dec_ref(v_a_723_);
lean_dec_ref(v_inst_722_);
lean_dec_ref(v_c_721_);
lean_dec_ref(v_00_u03b1_720_);
lean_inc(v_a_737_);
lean_inc_ref(v_a_736_);
lean_inc(v_a_735_);
lean_inc_ref(v_a_734_);
lean_inc(v_a_733_);
lean_inc_ref(v_a_732_);
lean_inc(v_a_731_);
lean_inc_ref(v_a_730_);
lean_inc(v_a_729_);
v___x_766_ = lean_apply_10(v_fallback_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_, lean_box(0));
return v___x_766_;
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
lean_dec_ref(v_fallback_728_);
v___x_767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1));
v___x_768_ = l_Lean_Expr_constLevels_x21(v_f_719_);
v___x_769_ = l_Lean_mkConst(v___x_767_, v___x_768_);
lean_inc_ref(v_a_723_);
v___x_770_ = l_Lean_mkApp8(v___x_769_, v_00_u03b1_720_, v_c_721_, v_inst_722_, v_a_723_, v_b_724_, v_c_x27_725_, v_h_726_, v_arg_744_);
v___x_771_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_771_, 0, v_a_723_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
lean_ctor_set_uint8(v___x_771_, sizeof(void*)*2, v___x_763_);
lean_ctor_set_uint8(v___x_771_, sizeof(void*)*2 + 1, v___x_763_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_771_);
v___x_773_ = v___x_759_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; lean_object* v___x_780_; lean_object* v___x_782_; 
lean_dec_ref(v___x_761_);
lean_dec_ref(v_fallback_728_);
v___x_775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3));
v___x_776_ = l_Lean_Expr_constLevels_x21(v_f_719_);
v___x_777_ = l_Lean_mkConst(v___x_775_, v___x_776_);
lean_inc_ref(v_b_724_);
v___x_778_ = l_Lean_mkApp8(v___x_777_, v_00_u03b1_720_, v_c_721_, v_inst_722_, v_a_723_, v_b_724_, v_c_x27_725_, v_h_726_, v_arg_744_);
v___x_779_ = 0;
v___x_780_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_780_, 0, v_b_724_);
lean_ctor_set(v___x_780_, 1, v___x_778_);
lean_ctor_set_uint8(v___x_780_, sizeof(void*)*2, v___x_779_);
lean_ctor_set_uint8(v___x_780_, sizeof(void*)*2 + 1, v___x_779_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v___x_780_);
v___x_782_ = v___x_759_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_dec_ref(v_arg_744_);
lean_dec_ref(v_fallback_728_);
lean_dec_ref(v_h_726_);
lean_dec_ref(v_c_x27_725_);
lean_dec_ref(v_b_724_);
lean_dec_ref(v_a_723_);
lean_dec_ref(v_inst_722_);
lean_dec_ref(v_c_721_);
lean_dec_ref(v_00_u03b1_720_);
v_a_785_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_756_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_756_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
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
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_dec_ref(v_fallback_728_);
lean_dec_ref(v_h_726_);
lean_dec_ref(v_c_x27_725_);
lean_dec_ref(v_b_724_);
lean_dec_ref(v_a_723_);
lean_dec_ref(v_inst_722_);
lean_dec_ref(v_c_721_);
lean_dec_ref(v_00_u03b1_720_);
v_a_793_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_739_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_739_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_719_ = stack[0].m_obj;
lean_object* v_00_u03b1_720_ = stack[1].m_obj;
lean_object* v_c_721_ = stack[2].m_obj;
lean_object* v_inst_722_ = stack[3].m_obj;
lean_object* v_a_723_ = stack[4].m_obj;
lean_object* v_b_724_ = stack[5].m_obj;
lean_object* v_c_x27_725_ = stack[6].m_obj;
lean_object* v_h_726_ = stack[7].m_obj;
lean_object* v_inst_x27_727_ = stack[8].m_obj;
lean_object* v_fallback_728_ = stack[9].m_obj;
lean_object* v_a_729_ = stack[10].m_obj;
lean_object* v_a_730_ = stack[11].m_obj;
lean_object* v_a_731_ = stack[12].m_obj;
lean_object* v_a_732_ = stack[13].m_obj;
lean_object* v_a_733_ = stack[14].m_obj;
lean_object* v_a_734_ = stack[15].m_obj;
lean_object* v_a_735_ = stack[16].m_obj;
lean_object* v_a_736_ = stack[17].m_obj;
lean_object* v_a_737_ = stack[18].m_obj;
lean_object* v_res_801_;
v_res_801_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(v_f_719_, v_00_u03b1_720_, v_c_721_, v_inst_722_, v_a_723_, v_b_724_, v_c_x27_725_, v_h_726_, v_inst_x27_727_, v_fallback_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
stack->m_obj
 = v_res_801_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_802_ = _args[0];
lean_object* v_00_u03b1_803_ = _args[1];
lean_object* v_c_804_ = _args[2];
lean_object* v_inst_805_ = _args[3];
lean_object* v_a_806_ = _args[4];
lean_object* v_b_807_ = _args[5];
lean_object* v_c_x27_808_ = _args[6];
lean_object* v_h_809_ = _args[7];
lean_object* v_inst_x27_810_ = _args[8];
lean_object* v_fallback_811_ = _args[9];
lean_object* v_a_812_ = _args[10];
lean_object* v_a_813_ = _args[11];
lean_object* v_a_814_ = _args[12];
lean_object* v_a_815_ = _args[13];
lean_object* v_a_816_ = _args[14];
lean_object* v_a_817_ = _args[15];
lean_object* v_a_818_ = _args[16];
lean_object* v_a_819_ = _args[17];
lean_object* v_a_820_ = _args[18];
lean_object* v_a_821_ = _args[19];
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(v_f_802_, v_00_u03b1_803_, v_c_804_, v_inst_805_, v_a_806_, v_b_807_, v_c_x27_808_, v_h_809_, v_inst_x27_810_, v_fallback_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec(v_a_812_);
lean_dec_ref(v_f_802_);
return v_res_822_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0(uint8_t v___x_823_, lean_object* v_inst_824_, lean_object* v___x_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___y_832_; lean_object* v___x_849_; uint8_t v_transparency_850_; uint8_t v___x_851_; 
v___x_849_ = l_Lean_Meta_Context_config(v___y_826_);
v_transparency_850_ = lean_ctor_get_uint8(v___x_849_, 9);
lean_dec_ref(v___x_849_);
v___x_851_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_850_, v___x_823_);
if (v___x_851_ == 0)
{
lean_object* v_keyedConfig_852_; uint8_t v_trackZetaDelta_853_; lean_object* v_zetaDeltaSet_854_; lean_object* v_lctx_855_; lean_object* v_localInstances_856_; lean_object* v_defEqCtx_x3f_857_; lean_object* v_synthPendingDepth_858_; lean_object* v_customCanUnfoldPredicate_x3f_859_; uint8_t v_univApprox_860_; uint8_t v_inTypeClassResolution_861_; uint8_t v_cacheInferType_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_871_; 
v_keyedConfig_852_ = lean_ctor_get(v___y_826_, 0);
v_trackZetaDelta_853_ = lean_ctor_get_uint8(v___y_826_, sizeof(void*)*7);
v_zetaDeltaSet_854_ = lean_ctor_get(v___y_826_, 1);
v_lctx_855_ = lean_ctor_get(v___y_826_, 2);
v_localInstances_856_ = lean_ctor_get(v___y_826_, 3);
v_defEqCtx_x3f_857_ = lean_ctor_get(v___y_826_, 4);
v_synthPendingDepth_858_ = lean_ctor_get(v___y_826_, 5);
v_customCanUnfoldPredicate_x3f_859_ = lean_ctor_get(v___y_826_, 6);
v_univApprox_860_ = lean_ctor_get_uint8(v___y_826_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_861_ = lean_ctor_get_uint8(v___y_826_, sizeof(void*)*7 + 2);
v_cacheInferType_862_ = lean_ctor_get_uint8(v___y_826_, sizeof(void*)*7 + 3);
v_isSharedCheck_871_ = !lean_is_exclusive(v___y_826_);
if (v_isSharedCheck_871_ == 0)
{
v___x_864_ = v___y_826_;
v_isShared_865_ = v_isSharedCheck_871_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_859_);
lean_inc(v_synthPendingDepth_858_);
lean_inc(v_defEqCtx_x3f_857_);
lean_inc(v_localInstances_856_);
lean_inc(v_lctx_855_);
lean_inc(v_zetaDeltaSet_854_);
lean_inc(v_keyedConfig_852_);
lean_dec(v___y_826_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_871_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; lean_object* v___x_868_; 
v___x_866_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_823_, v_keyedConfig_852_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_866_);
v___x_868_ = v___x_864_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_870_, 1, v_zetaDeltaSet_854_);
lean_ctor_set(v_reuseFailAlloc_870_, 2, v_lctx_855_);
lean_ctor_set(v_reuseFailAlloc_870_, 3, v_localInstances_856_);
lean_ctor_set(v_reuseFailAlloc_870_, 4, v_defEqCtx_x3f_857_);
lean_ctor_set(v_reuseFailAlloc_870_, 5, v_synthPendingDepth_858_);
lean_ctor_set(v_reuseFailAlloc_870_, 6, v_customCanUnfoldPredicate_x3f_859_);
lean_ctor_set_uint8(v_reuseFailAlloc_870_, sizeof(void*)*7, v_trackZetaDelta_853_);
lean_ctor_set_uint8(v_reuseFailAlloc_870_, sizeof(void*)*7 + 1, v_univApprox_860_);
lean_ctor_set_uint8(v_reuseFailAlloc_870_, sizeof(void*)*7 + 2, v_inTypeClassResolution_861_);
lean_ctor_set_uint8(v_reuseFailAlloc_870_, sizeof(void*)*7 + 3, v_cacheInferType_862_);
v___x_868_ = v_reuseFailAlloc_870_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
lean_object* v___x_869_; 
v___x_869_ = l_Lean_Meta_project_x3f(v_inst_824_, v___x_825_, v___x_868_, v___y_827_, v___y_828_, v___y_829_);
lean_dec_ref(v___x_868_);
v___y_832_ = v___x_869_;
goto v___jp_831_;
}
}
}
else
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_Meta_project_x3f(v_inst_824_, v___x_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
lean_dec_ref(v___y_826_);
v___y_832_ = v___x_872_;
goto v___jp_831_;
}
v___jp_831_:
{
if (lean_obj_tag(v___y_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
v_a_833_ = lean_ctor_get(v___y_832_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___y_832_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___y_832_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___y_832_);
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
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
v_a_841_ = lean_ctor_get(v___y_832_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___y_832_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___y_832_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___y_832_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_823_ = stack[0].m_num;
lean_object* v_inst_824_ = stack[1].m_obj;
lean_object* v___x_825_ = stack[2].m_obj;
lean_object* v___y_826_ = stack[3].m_obj;
lean_object* v___y_827_ = stack[4].m_obj;
lean_object* v___y_828_ = stack[5].m_obj;
lean_object* v___y_829_ = stack[6].m_obj;
lean_object* v_res_873_;
v_res_873_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0(v___x_823_, v_inst_824_, v___x_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
stack->m_obj
 = v_res_873_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0___boxed(lean_object* v___x_874_, lean_object* v_inst_875_, lean_object* v___x_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
uint8_t v___x_15493__boxed_882_; lean_object* v_res_883_; 
v___x_15493__boxed_882_ = lean_unbox(v___x_874_);
v_res_883_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0(v___x_15493__boxed_882_, v_inst_875_, v___x_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec(v___x_876_);
return v_res_883_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_888_ = lean_box(0);
v___x_889_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__1));
v___x_890_ = l_Lean_mkConst(v___x_889_, v___x_888_);
return v___x_890_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__6(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = lean_unsigned_to_nat(1u);
v___x_897_ = l_Lean_Level_ofNat(v___x_896_);
return v___x_897_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__7(void){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = lean_box(0);
v___x_899_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__6, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__6_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__6);
v___x_900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v___x_898_);
return v___x_900_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__7, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__7);
v___x_902_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__5));
v___x_903_ = l_Lean_Expr_const___override(v___x_902_, v___x_901_);
return v___x_903_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = lean_box(0);
v___x_907_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__9));
v___x_908_ = l_Lean_mkConst(v___x_907_, v___x_906_);
return v___x_908_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(lean_object* v_f_919_, lean_object* v_00_u03b1_920_, lean_object* v_c_921_, lean_object* v_inst_922_, lean_object* v_a_923_, lean_object* v_b_924_, lean_object* v_fallback_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v___x_936_; uint8_t v___x_937_; lean_object* v___x_938_; lean_object* v___f_939_; lean_object* v___x_940_; 
v___x_936_ = lean_unsigned_to_nat(0u);
v___x_937_ = 5;
v___x_938_ = lean_box(v___x_937_);
lean_inc_ref(v_inst_922_);
v___f_939_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0___boxed), 8, 3);
lean_closure_set(v___f_939_, 0, v___x_938_);
lean_closure_set(v___f_939_, 1, v_inst_922_);
lean_closure_set(v___f_939_, 2, v___x_936_);
v___x_940_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_939_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_940_, 1);
if (lean_obj_tag(v_a_941_) == 0)
{
lean_object* v___x_942_; 
lean_inc(v_a_934_);
lean_inc_ref(v_a_933_);
lean_inc(v_a_932_);
lean_inc_ref(v_a_931_);
lean_inc(v_a_930_);
lean_inc_ref(v_a_929_);
lean_inc(v_a_928_);
lean_inc_ref(v_a_927_);
lean_inc(v_a_926_);
lean_inc_ref(v_inst_922_);
v___x_942_ = lean_sym_simp(v_inst_922_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v___x_942_, 1);
if (lean_obj_tag(v_a_943_) == 0)
{
uint8_t v_contextDependent_944_; lean_object* v___x_945_; 
v_contextDependent_944_ = lean_ctor_get_uint8(v_a_943_, 1);
lean_dec_ref_known(v_a_943_, 0);
lean_inc_ref(v_inst_922_);
v___x_945_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(v_f_919_, v_00_u03b1_920_, v_c_921_, v_inst_922_, v_a_923_, v_b_924_, v_inst_922_, v_fallback_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; uint8_t v___y_948_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
if (v_contextDependent_944_ == 0)
{
return v___x_945_;
}
else
{
if (lean_obj_tag(v_a_946_) == 0)
{
uint8_t v_contextDependent_958_; 
v_contextDependent_958_ = lean_ctor_get_uint8(v_a_946_, 1);
v___y_948_ = v_contextDependent_958_;
goto v___jp_947_;
}
else
{
uint8_t v_contextDependent_959_; 
v_contextDependent_959_ = lean_ctor_get_uint8(v_a_946_, sizeof(void*)*2 + 1);
v___y_948_ = v_contextDependent_959_;
goto v___jp_947_;
}
}
v___jp_947_:
{
if (v___y_948_ == 0)
{
lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_956_; 
lean_inc(v_a_946_);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_956_ == 0)
{
lean_object* v_unused_957_; 
v_unused_957_ = lean_ctor_get(v___x_945_, 0);
lean_dec(v_unused_957_);
v___x_950_ = v___x_945_;
v_isShared_951_ = v_isSharedCheck_956_;
goto v_resetjp_949_;
}
else
{
lean_dec(v___x_945_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_956_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v___x_954_; 
v___x_952_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_946_);
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
}
else
{
return v___x_945_;
}
}
}
else
{
return v___x_945_;
}
}
else
{
lean_object* v_e_x27_960_; uint8_t v_contextDependent_961_; lean_object* v___x_962_; 
v_e_x27_960_ = lean_ctor_get(v_a_943_, 0);
lean_inc_ref(v_e_x27_960_);
v_contextDependent_961_ = lean_ctor_get_uint8(v_a_943_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_943_, 2);
v___x_962_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(v_f_919_, v_00_u03b1_920_, v_c_921_, v_inst_922_, v_a_923_, v_b_924_, v_e_x27_960_, v_fallback_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; uint8_t v___y_965_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
if (v_contextDependent_961_ == 0)
{
return v___x_962_;
}
else
{
if (lean_obj_tag(v_a_963_) == 0)
{
uint8_t v_contextDependent_975_; 
v_contextDependent_975_ = lean_ctor_get_uint8(v_a_963_, 1);
v___y_965_ = v_contextDependent_975_;
goto v___jp_964_;
}
else
{
uint8_t v_contextDependent_976_; 
v_contextDependent_976_ = lean_ctor_get_uint8(v_a_963_, sizeof(void*)*2 + 1);
v___y_965_ = v_contextDependent_976_;
goto v___jp_964_;
}
}
v___jp_964_:
{
if (v___y_965_ == 0)
{
lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_973_; 
lean_inc(v_a_963_);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_973_ == 0)
{
lean_object* v_unused_974_; 
v_unused_974_ = lean_ctor_get(v___x_962_, 0);
lean_dec(v_unused_974_);
v___x_967_ = v___x_962_;
v_isShared_968_ = v_isSharedCheck_973_;
goto v_resetjp_966_;
}
else
{
lean_dec(v___x_962_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_973_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_969_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_963_);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 0, v___x_969_);
v___x_971_ = v___x_967_;
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
else
{
return v___x_962_;
}
}
}
else
{
return v___x_962_;
}
}
}
else
{
lean_dec_ref(v_fallback_925_);
lean_dec_ref(v_b_924_);
lean_dec_ref(v_a_923_);
lean_dec_ref(v_inst_922_);
lean_dec_ref(v_c_921_);
lean_dec_ref(v_00_u03b1_920_);
return v___x_942_;
}
}
else
{
lean_object* v_val_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_val_977_ = lean_ctor_get(v_a_941_, 0);
lean_inc(v_val_977_);
lean_dec_ref_known(v_a_941_, 1);
v___x_978_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2);
lean_inc_ref(v_inst_922_);
lean_inc_ref(v_c_921_);
v___x_979_ = l_Lean_mkAppB(v___x_978_, v_c_921_, v_inst_922_);
v___x_980_ = l_Lean_Meta_Sym_shareCommonInc(v_val_977_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
lean_inc_n(v_a_981_, 3);
lean_dec_ref_known(v___x_980_, 1);
v___x_982_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8);
v___x_983_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10);
v___x_984_ = l_Lean_mkAppB(v___x_982_, v___x_983_, v_a_981_);
lean_inc(v_a_934_);
lean_inc_ref(v_a_933_);
lean_inc(v_a_932_);
lean_inc_ref(v_a_931_);
lean_inc(v_a_930_);
lean_inc_ref(v_a_929_);
lean_inc(v_a_928_);
lean_inc_ref(v_a_927_);
lean_inc(v_a_926_);
v___x_985_ = lean_sym_simp(v_a_981_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; uint8_t v___x_987_; lean_object* v_e_x27_989_; lean_object* v_proof_990_; uint8_t v_contextDependent_991_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_a_986_);
lean_dec_ref_known(v___x_985_, 1);
v___x_987_ = 0;
if (lean_obj_tag(v_a_986_) == 0)
{
uint8_t v_contextDependent_1028_; 
lean_dec_ref(v___x_979_);
v_contextDependent_1028_ = lean_ctor_get_uint8(v_a_986_, 1);
lean_dec_ref_known(v_a_986_, 0);
v_e_x27_989_ = v_a_981_;
v_proof_990_ = v___x_984_;
v_contextDependent_991_ = v_contextDependent_1028_;
goto v___jp_988_;
}
else
{
lean_object* v_e_x27_1029_; lean_object* v_proof_1030_; uint8_t v_contextDependent_1031_; lean_object* v___x_1032_; 
v_e_x27_1029_ = lean_ctor_get(v_a_986_, 0);
lean_inc_ref_n(v_e_x27_1029_, 2);
v_proof_1030_ = lean_ctor_get(v_a_986_, 1);
lean_inc_ref(v_proof_1030_);
v_contextDependent_1031_ = lean_ctor_get_uint8(v_a_986_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_986_, 2);
v___x_1032_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___x_979_, v_a_981_, v___x_984_, v_e_x27_1029_, v_proof_1030_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v_a_1033_; 
v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_a_1033_);
lean_dec_ref_known(v___x_1032_, 1);
v_e_x27_989_ = v_e_x27_1029_;
v_proof_990_ = v_a_1033_;
v_contextDependent_991_ = v_contextDependent_1031_;
goto v___jp_988_;
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec_ref(v_e_x27_1029_);
lean_dec_ref(v_fallback_925_);
lean_dec_ref(v_b_924_);
lean_dec_ref(v_a_923_);
lean_dec_ref(v_inst_922_);
lean_dec_ref(v_c_921_);
lean_dec_ref(v_00_u03b1_920_);
v_a_1034_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1032_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1032_);
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
v___jp_988_:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_x27_989_, v_a_932_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1019_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_995_ = v___x_992_;
v_isShared_996_ = v_isSharedCheck_1019_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_992_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1019_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_997_ = l_Lean_Expr_cleanupAnnotations(v_a_993_);
v___x_998_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_999_ = l_Lean_Expr_isConstOf(v___x_997_, v___x_998_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_1000_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_1001_ = l_Lean_Expr_isConstOf(v___x_997_, v___x_1000_);
lean_dec_ref(v___x_997_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; 
lean_del_object(v___x_995_);
lean_dec_ref(v_proof_990_);
lean_dec_ref(v_b_924_);
lean_dec_ref(v_a_923_);
lean_dec_ref(v_inst_922_);
lean_dec_ref(v_c_921_);
lean_dec_ref(v_00_u03b1_920_);
lean_inc(v_a_934_);
lean_inc_ref(v_a_933_);
lean_inc(v_a_932_);
lean_inc_ref(v_a_931_);
lean_inc(v_a_930_);
lean_inc_ref(v_a_929_);
lean_inc(v_a_928_);
lean_inc_ref(v_a_927_);
lean_inc(v_a_926_);
v___x_1002_ = lean_apply_10(v_fallback_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, lean_box(0));
return v___x_1002_;
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; 
lean_dec_ref(v_fallback_925_);
v___x_1003_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__12));
v___x_1004_ = l_Lean_Expr_constLevels_x21(v_f_919_);
v___x_1005_ = l_Lean_mkConst(v___x_1003_, v___x_1004_);
lean_inc_ref(v_a_923_);
v___x_1006_ = l_Lean_mkApp6(v___x_1005_, v_00_u03b1_920_, v_c_921_, v_inst_922_, v_a_923_, v_b_924_, v_proof_990_);
v___x_1007_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1007_, 0, v_a_923_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
lean_ctor_set_uint8(v___x_1007_, sizeof(void*)*2, v___x_987_);
lean_ctor_set_uint8(v___x_1007_, sizeof(void*)*2 + 1, v_contextDependent_991_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1007_);
v___x_1009_ = v___x_995_;
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
else
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
lean_dec_ref(v___x_997_);
lean_dec_ref(v_fallback_925_);
v___x_1011_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__14));
v___x_1012_ = l_Lean_Expr_constLevels_x21(v_f_919_);
v___x_1013_ = l_Lean_mkConst(v___x_1011_, v___x_1012_);
lean_inc_ref(v_b_924_);
v___x_1014_ = l_Lean_mkApp6(v___x_1013_, v_00_u03b1_920_, v_c_921_, v_inst_922_, v_a_923_, v_b_924_, v_proof_990_);
v___x_1015_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1015_, 0, v_b_924_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
lean_ctor_set_uint8(v___x_1015_, sizeof(void*)*2, v___x_987_);
lean_ctor_set_uint8(v___x_1015_, sizeof(void*)*2 + 1, v_contextDependent_991_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 0, v___x_1015_);
v___x_1017_ = v___x_995_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
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
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_dec_ref(v_proof_990_);
lean_dec_ref(v_fallback_925_);
lean_dec_ref(v_b_924_);
lean_dec_ref(v_a_923_);
lean_dec_ref(v_inst_922_);
lean_dec_ref(v_c_921_);
lean_dec_ref(v_00_u03b1_920_);
v_a_1020_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_992_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_992_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_984_);
lean_dec(v_a_981_);
lean_dec_ref(v___x_979_);
lean_dec_ref(v_fallback_925_);
lean_dec_ref(v_b_924_);
lean_dec_ref(v_a_923_);
lean_dec_ref(v_inst_922_);
lean_dec_ref(v_c_921_);
lean_dec_ref(v_00_u03b1_920_);
return v___x_985_;
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref(v___x_979_);
lean_dec_ref(v_fallback_925_);
lean_dec_ref(v_b_924_);
lean_dec_ref(v_a_923_);
lean_dec_ref(v_inst_922_);
lean_dec_ref(v_c_921_);
lean_dec_ref(v_00_u03b1_920_);
v_a_1042_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_980_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_980_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec_ref(v_fallback_925_);
lean_dec_ref(v_b_924_);
lean_dec_ref(v_a_923_);
lean_dec_ref(v_inst_922_);
lean_dec_ref(v_c_921_);
lean_dec_ref(v_00_u03b1_920_);
v_a_1050_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_940_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_940_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_919_ = stack[0].m_obj;
lean_object* v_00_u03b1_920_ = stack[1].m_obj;
lean_object* v_c_921_ = stack[2].m_obj;
lean_object* v_inst_922_ = stack[3].m_obj;
lean_object* v_a_923_ = stack[4].m_obj;
lean_object* v_b_924_ = stack[5].m_obj;
lean_object* v_fallback_925_ = stack[6].m_obj;
lean_object* v_a_926_ = stack[7].m_obj;
lean_object* v_a_927_ = stack[8].m_obj;
lean_object* v_a_928_ = stack[9].m_obj;
lean_object* v_a_929_ = stack[10].m_obj;
lean_object* v_a_930_ = stack[11].m_obj;
lean_object* v_a_931_ = stack[12].m_obj;
lean_object* v_a_932_ = stack[13].m_obj;
lean_object* v_a_933_ = stack[14].m_obj;
lean_object* v_a_934_ = stack[15].m_obj;
lean_object* v_res_1058_;
v_res_1058_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v_f_919_, v_00_u03b1_920_, v_c_921_, v_inst_922_, v_a_923_, v_b_924_, v_fallback_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
stack->m_obj
 = v_res_1058_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___boxed(lean_object** _args){
lean_object* v_f_1059_ = _args[0];
lean_object* v_00_u03b1_1060_ = _args[1];
lean_object* v_c_1061_ = _args[2];
lean_object* v_inst_1062_ = _args[3];
lean_object* v_a_1063_ = _args[4];
lean_object* v_b_1064_ = _args[5];
lean_object* v_fallback_1065_ = _args[6];
lean_object* v_a_1066_ = _args[7];
lean_object* v_a_1067_ = _args[8];
lean_object* v_a_1068_ = _args[9];
lean_object* v_a_1069_ = _args[10];
lean_object* v_a_1070_ = _args[11];
lean_object* v_a_1071_ = _args[12];
lean_object* v_a_1072_ = _args[13];
lean_object* v_a_1073_ = _args[14];
lean_object* v_a_1074_ = _args[15];
lean_object* v_a_1075_ = _args[16];
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v_f_1059_, v_00_u03b1_1060_, v_c_1061_, v_inst_1062_, v_a_1063_, v_b_1064_, v_fallback_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec_ref(v_f_1059_);
return v_res_1076_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0(uint8_t v___x_1077_, lean_object* v_inst_x27_1078_, lean_object* v___x_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v___y_1086_; lean_object* v___x_1103_; uint8_t v_transparency_1104_; uint8_t v___x_1105_; 
v___x_1103_ = l_Lean_Meta_Context_config(v___y_1080_);
v_transparency_1104_ = lean_ctor_get_uint8(v___x_1103_, 9);
lean_dec_ref(v___x_1103_);
v___x_1105_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1104_, v___x_1077_);
if (v___x_1105_ == 0)
{
lean_object* v_keyedConfig_1106_; uint8_t v_trackZetaDelta_1107_; lean_object* v_zetaDeltaSet_1108_; lean_object* v_lctx_1109_; lean_object* v_localInstances_1110_; lean_object* v_defEqCtx_x3f_1111_; lean_object* v_synthPendingDepth_1112_; lean_object* v_customCanUnfoldPredicate_x3f_1113_; uint8_t v_univApprox_1114_; uint8_t v_inTypeClassResolution_1115_; uint8_t v_cacheInferType_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1125_; 
v_keyedConfig_1106_ = lean_ctor_get(v___y_1080_, 0);
v_trackZetaDelta_1107_ = lean_ctor_get_uint8(v___y_1080_, sizeof(void*)*7);
v_zetaDeltaSet_1108_ = lean_ctor_get(v___y_1080_, 1);
v_lctx_1109_ = lean_ctor_get(v___y_1080_, 2);
v_localInstances_1110_ = lean_ctor_get(v___y_1080_, 3);
v_defEqCtx_x3f_1111_ = lean_ctor_get(v___y_1080_, 4);
v_synthPendingDepth_1112_ = lean_ctor_get(v___y_1080_, 5);
v_customCanUnfoldPredicate_x3f_1113_ = lean_ctor_get(v___y_1080_, 6);
v_univApprox_1114_ = lean_ctor_get_uint8(v___y_1080_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1115_ = lean_ctor_get_uint8(v___y_1080_, sizeof(void*)*7 + 2);
v_cacheInferType_1116_ = lean_ctor_get_uint8(v___y_1080_, sizeof(void*)*7 + 3);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___y_1080_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1118_ = v___y_1080_;
v_isShared_1119_ = v_isSharedCheck_1125_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_1113_);
lean_inc(v_synthPendingDepth_1112_);
lean_inc(v_defEqCtx_x3f_1111_);
lean_inc(v_localInstances_1110_);
lean_inc(v_lctx_1109_);
lean_inc(v_zetaDeltaSet_1108_);
lean_inc(v_keyedConfig_1106_);
lean_dec(v___y_1080_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1125_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1120_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1077_, v_keyedConfig_1106_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 0, v___x_1120_);
v___x_1122_ = v___x_1118_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_zetaDeltaSet_1108_);
lean_ctor_set(v_reuseFailAlloc_1124_, 2, v_lctx_1109_);
lean_ctor_set(v_reuseFailAlloc_1124_, 3, v_localInstances_1110_);
lean_ctor_set(v_reuseFailAlloc_1124_, 4, v_defEqCtx_x3f_1111_);
lean_ctor_set(v_reuseFailAlloc_1124_, 5, v_synthPendingDepth_1112_);
lean_ctor_set(v_reuseFailAlloc_1124_, 6, v_customCanUnfoldPredicate_x3f_1113_);
lean_ctor_set_uint8(v_reuseFailAlloc_1124_, sizeof(void*)*7, v_trackZetaDelta_1107_);
lean_ctor_set_uint8(v_reuseFailAlloc_1124_, sizeof(void*)*7 + 1, v_univApprox_1114_);
lean_ctor_set_uint8(v_reuseFailAlloc_1124_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1115_);
lean_ctor_set_uint8(v_reuseFailAlloc_1124_, sizeof(void*)*7 + 3, v_cacheInferType_1116_);
v___x_1122_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Lean_Meta_project_x3f(v_inst_x27_1078_, v___x_1079_, v___x_1122_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec_ref(v___x_1122_);
v___y_1086_ = v___x_1123_;
goto v___jp_1085_;
}
}
}
else
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_Meta_project_x3f(v_inst_x27_1078_, v___x_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec_ref(v___y_1080_);
v___y_1086_ = v___x_1126_;
goto v___jp_1085_;
}
v___jp_1085_:
{
if (lean_obj_tag(v___y_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
v_a_1087_ = lean_ctor_get(v___y_1086_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___y_1086_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___y_1086_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___y_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_a_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_a_1095_ = lean_ctor_get(v___y_1086_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___y_1086_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___y_1086_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___y_1086_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1077_ = stack[0].m_num;
lean_object* v_inst_x27_1078_ = stack[1].m_obj;
lean_object* v___x_1079_ = stack[2].m_obj;
lean_object* v___y_1080_ = stack[3].m_obj;
lean_object* v___y_1081_ = stack[4].m_obj;
lean_object* v___y_1082_ = stack[5].m_obj;
lean_object* v___y_1083_ = stack[6].m_obj;
lean_object* v_res_1127_;
v_res_1127_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0(v___x_1077_, v_inst_x27_1078_, v___x_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
stack->m_obj
 = v_res_1127_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0___boxed(lean_object* v___x_1128_, lean_object* v_inst_x27_1129_, lean_object* v___x_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
uint8_t v___x_15493__boxed_1136_; lean_object* v_res_1137_; 
v___x_15493__boxed_1136_ = lean_unbox(v___x_1128_);
v_res_1137_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0(v___x_15493__boxed_1136_, v_inst_x27_1129_, v___x_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec(v___x_1130_);
return v_res_1137_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr(lean_object* v_f_1148_, lean_object* v_00_u03b1_1149_, lean_object* v_c_1150_, lean_object* v_inst_1151_, lean_object* v_a_1152_, lean_object* v_b_1153_, lean_object* v_c_x27_1154_, lean_object* v_h_1155_, lean_object* v_inst_x27_1156_, lean_object* v_fallback_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
lean_object* v___x_1168_; uint8_t v___x_1169_; lean_object* v___x_1170_; lean_object* v___f_1171_; lean_object* v___x_1172_; 
v___x_1168_ = lean_unsigned_to_nat(0u);
v___x_1169_ = 5;
v___x_1170_ = lean_box(v___x_1169_);
lean_inc_ref(v_inst_x27_1156_);
v___f_1171_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1171_, 0, v___x_1170_);
lean_closure_set(v___f_1171_, 1, v_inst_x27_1156_);
lean_closure_set(v___f_1171_, 2, v___x_1168_);
v___x_1172_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_1171_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___x_1172_, 1);
if (lean_obj_tag(v_a_1173_) == 0)
{
lean_object* v___x_1174_; 
lean_inc(v_a_1166_);
lean_inc_ref(v_a_1165_);
lean_inc(v_a_1164_);
lean_inc_ref(v_a_1163_);
lean_inc(v_a_1162_);
lean_inc_ref(v_a_1161_);
lean_inc(v_a_1160_);
lean_inc_ref(v_a_1159_);
lean_inc(v_a_1158_);
lean_inc_ref(v_inst_x27_1156_);
v___x_1174_ = lean_sym_simp(v_inst_x27_1156_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1174_, 1);
if (lean_obj_tag(v_a_1175_) == 0)
{
uint8_t v_contextDependent_1176_; lean_object* v___x_1177_; 
v_contextDependent_1176_ = lean_ctor_get_uint8(v_a_1175_, 1);
lean_dec_ref_known(v_a_1175_, 0);
v___x_1177_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(v_f_1148_, v_00_u03b1_1149_, v_c_1150_, v_inst_1151_, v_a_1152_, v_b_1153_, v_c_x27_1154_, v_h_1155_, v_inst_x27_1156_, v_fallback_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; uint8_t v___y_1180_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
if (v_contextDependent_1176_ == 0)
{
return v___x_1177_;
}
else
{
if (lean_obj_tag(v_a_1178_) == 0)
{
uint8_t v_contextDependent_1190_; 
v_contextDependent_1190_ = lean_ctor_get_uint8(v_a_1178_, 1);
v___y_1180_ = v_contextDependent_1190_;
goto v___jp_1179_;
}
else
{
uint8_t v_contextDependent_1191_; 
v_contextDependent_1191_ = lean_ctor_get_uint8(v_a_1178_, sizeof(void*)*2 + 1);
v___y_1180_ = v_contextDependent_1191_;
goto v___jp_1179_;
}
}
v___jp_1179_:
{
if (v___y_1180_ == 0)
{
lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1188_; 
lean_inc(v_a_1178_);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1188_ == 0)
{
lean_object* v_unused_1189_; 
v_unused_1189_ = lean_ctor_get(v___x_1177_, 0);
lean_dec(v_unused_1189_);
v___x_1182_ = v___x_1177_;
v_isShared_1183_ = v_isSharedCheck_1188_;
goto v_resetjp_1181_;
}
else
{
lean_dec(v___x_1177_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1188_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1184_; lean_object* v___x_1186_; 
v___x_1184_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1178_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1184_);
v___x_1186_ = v___x_1182_;
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
else
{
return v___x_1177_;
}
}
}
else
{
return v___x_1177_;
}
}
else
{
lean_object* v_e_x27_1192_; uint8_t v_contextDependent_1193_; lean_object* v___x_1194_; 
lean_dec_ref(v_inst_x27_1156_);
v_e_x27_1192_ = lean_ctor_get(v_a_1175_, 0);
lean_inc_ref(v_e_x27_1192_);
v_contextDependent_1193_ = lean_ctor_get_uint8(v_a_1175_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1175_, 2);
v___x_1194_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(v_f_1148_, v_00_u03b1_1149_, v_c_1150_, v_inst_1151_, v_a_1152_, v_b_1153_, v_c_x27_1154_, v_h_1155_, v_e_x27_1192_, v_fallback_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; uint8_t v___y_1197_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
if (v_contextDependent_1193_ == 0)
{
return v___x_1194_;
}
else
{
if (lean_obj_tag(v_a_1195_) == 0)
{
uint8_t v_contextDependent_1207_; 
v_contextDependent_1207_ = lean_ctor_get_uint8(v_a_1195_, 1);
v___y_1197_ = v_contextDependent_1207_;
goto v___jp_1196_;
}
else
{
uint8_t v_contextDependent_1208_; 
v_contextDependent_1208_ = lean_ctor_get_uint8(v_a_1195_, sizeof(void*)*2 + 1);
v___y_1197_ = v_contextDependent_1208_;
goto v___jp_1196_;
}
}
v___jp_1196_:
{
if (v___y_1197_ == 0)
{
lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1205_; 
lean_inc(v_a_1195_);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1205_ == 0)
{
lean_object* v_unused_1206_; 
v_unused_1206_ = lean_ctor_get(v___x_1194_, 0);
lean_dec(v_unused_1206_);
v___x_1199_ = v___x_1194_;
v_isShared_1200_ = v_isSharedCheck_1205_;
goto v_resetjp_1198_;
}
else
{
lean_dec(v___x_1194_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1205_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1201_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1195_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 0, v___x_1201_);
v___x_1203_ = v___x_1199_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
else
{
return v___x_1194_;
}
}
}
else
{
return v___x_1194_;
}
}
}
else
{
lean_dec_ref(v_fallback_1157_);
lean_dec_ref(v_inst_x27_1156_);
lean_dec_ref(v_h_1155_);
lean_dec_ref(v_c_x27_1154_);
lean_dec_ref(v_b_1153_);
lean_dec_ref(v_a_1152_);
lean_dec_ref(v_inst_1151_);
lean_dec_ref(v_c_1150_);
lean_dec_ref(v_00_u03b1_1149_);
return v___x_1174_;
}
}
else
{
lean_object* v_val_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v_val_1209_ = lean_ctor_get(v_a_1173_, 0);
lean_inc(v_val_1209_);
lean_dec_ref_known(v_a_1173_, 1);
v___x_1210_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2);
lean_inc_ref(v_inst_x27_1156_);
lean_inc_ref(v_c_x27_1154_);
v___x_1211_ = l_Lean_mkAppB(v___x_1210_, v_c_x27_1154_, v_inst_x27_1156_);
v___x_1212_ = l_Lean_Meta_Sym_shareCommonInc(v_val_1209_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc_n(v_a_1213_, 3);
lean_dec_ref_known(v___x_1212_, 1);
v___x_1214_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8);
v___x_1215_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10);
v___x_1216_ = l_Lean_mkAppB(v___x_1214_, v___x_1215_, v_a_1213_);
lean_inc(v_a_1166_);
lean_inc_ref(v_a_1165_);
lean_inc(v_a_1164_);
lean_inc_ref(v_a_1163_);
lean_inc(v_a_1162_);
lean_inc_ref(v_a_1161_);
lean_inc(v_a_1160_);
lean_inc_ref(v_a_1159_);
lean_inc(v_a_1158_);
v___x_1217_ = lean_sym_simp(v_a_1213_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; uint8_t v___x_1219_; lean_object* v_e_x27_1221_; lean_object* v_proof_1222_; uint8_t v_contextDependent_1223_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref_known(v___x_1217_, 1);
v___x_1219_ = 0;
if (lean_obj_tag(v_a_1218_) == 0)
{
uint8_t v_contextDependent_1260_; 
lean_dec_ref(v___x_1211_);
v_contextDependent_1260_ = lean_ctor_get_uint8(v_a_1218_, 1);
lean_dec_ref_known(v_a_1218_, 0);
v_e_x27_1221_ = v_a_1213_;
v_proof_1222_ = v___x_1216_;
v_contextDependent_1223_ = v_contextDependent_1260_;
goto v___jp_1220_;
}
else
{
lean_object* v_e_x27_1261_; lean_object* v_proof_1262_; uint8_t v_contextDependent_1263_; lean_object* v___x_1264_; 
v_e_x27_1261_ = lean_ctor_get(v_a_1218_, 0);
lean_inc_ref_n(v_e_x27_1261_, 2);
v_proof_1262_ = lean_ctor_get(v_a_1218_, 1);
lean_inc_ref(v_proof_1262_);
v_contextDependent_1263_ = lean_ctor_get_uint8(v_a_1218_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1218_, 2);
v___x_1264_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___x_1211_, v_a_1213_, v___x_1216_, v_e_x27_1261_, v_proof_1262_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_a_1265_);
lean_dec_ref_known(v___x_1264_, 1);
v_e_x27_1221_ = v_e_x27_1261_;
v_proof_1222_ = v_a_1265_;
v_contextDependent_1223_ = v_contextDependent_1263_;
goto v___jp_1220_;
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v_e_x27_1261_);
lean_dec_ref(v_fallback_1157_);
lean_dec_ref(v_inst_x27_1156_);
lean_dec_ref(v_h_1155_);
lean_dec_ref(v_c_x27_1154_);
lean_dec_ref(v_b_1153_);
lean_dec_ref(v_a_1152_);
lean_dec_ref(v_inst_1151_);
lean_dec_ref(v_c_1150_);
lean_dec_ref(v_00_u03b1_1149_);
v_a_1266_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1264_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1264_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
v___jp_1220_:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_x27_1221_, v_a_1164_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1251_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1251_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1251_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; uint8_t v___x_1231_; 
v___x_1229_ = l_Lean_Expr_cleanupAnnotations(v_a_1225_);
v___x_1230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_1231_ = l_Lean_Expr_isConstOf(v___x_1229_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_1233_ = l_Lean_Expr_isConstOf(v___x_1229_, v___x_1232_);
lean_dec_ref(v___x_1229_);
if (v___x_1233_ == 0)
{
lean_object* v___x_1234_; 
lean_del_object(v___x_1227_);
lean_dec_ref(v_proof_1222_);
lean_dec_ref(v_inst_x27_1156_);
lean_dec_ref(v_h_1155_);
lean_dec_ref(v_c_x27_1154_);
lean_dec_ref(v_b_1153_);
lean_dec_ref(v_a_1152_);
lean_dec_ref(v_inst_1151_);
lean_dec_ref(v_c_1150_);
lean_dec_ref(v_00_u03b1_1149_);
lean_inc(v_a_1166_);
lean_inc_ref(v_a_1165_);
lean_inc(v_a_1164_);
lean_inc_ref(v_a_1163_);
lean_inc(v_a_1162_);
lean_inc_ref(v_a_1161_);
lean_inc(v_a_1160_);
lean_inc_ref(v_a_1159_);
lean_inc(v_a_1158_);
v___x_1234_ = lean_apply_10(v_fallback_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, lean_box(0));
return v___x_1234_;
}
else
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; 
lean_dec_ref(v_fallback_1157_);
v___x_1235_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__1));
v___x_1236_ = l_Lean_Expr_constLevels_x21(v_f_1148_);
v___x_1237_ = l_Lean_mkConst(v___x_1235_, v___x_1236_);
lean_inc_ref(v_a_1152_);
v___x_1238_ = l_Lean_mkApp9(v___x_1237_, v_00_u03b1_1149_, v_c_1150_, v_inst_1151_, v_a_1152_, v_b_1153_, v_c_x27_1154_, v_h_1155_, v_inst_x27_1156_, v_proof_1222_);
v___x_1239_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1239_, 0, v_a_1152_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
lean_ctor_set_uint8(v___x_1239_, sizeof(void*)*2, v___x_1219_);
lean_ctor_set_uint8(v___x_1239_, sizeof(void*)*2 + 1, v_contextDependent_1223_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1239_);
v___x_1241_ = v___x_1227_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1239_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
lean_dec_ref(v___x_1229_);
lean_dec_ref(v_fallback_1157_);
v___x_1243_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___closed__3));
v___x_1244_ = l_Lean_Expr_constLevels_x21(v_f_1148_);
v___x_1245_ = l_Lean_mkConst(v___x_1243_, v___x_1244_);
lean_inc_ref(v_b_1153_);
v___x_1246_ = l_Lean_mkApp9(v___x_1245_, v_00_u03b1_1149_, v_c_1150_, v_inst_1151_, v_a_1152_, v_b_1153_, v_c_x27_1154_, v_h_1155_, v_inst_x27_1156_, v_proof_1222_);
v___x_1247_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1247_, 0, v_b_1153_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
lean_ctor_set_uint8(v___x_1247_, sizeof(void*)*2, v___x_1219_);
lean_ctor_set_uint8(v___x_1247_, sizeof(void*)*2 + 1, v_contextDependent_1223_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1247_);
v___x_1249_ = v___x_1227_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec_ref(v_proof_1222_);
lean_dec_ref(v_fallback_1157_);
lean_dec_ref(v_inst_x27_1156_);
lean_dec_ref(v_h_1155_);
lean_dec_ref(v_c_x27_1154_);
lean_dec_ref(v_b_1153_);
lean_dec_ref(v_a_1152_);
lean_dec_ref(v_inst_1151_);
lean_dec_ref(v_c_1150_);
lean_dec_ref(v_00_u03b1_1149_);
v_a_1252_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1224_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1224_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1216_);
lean_dec(v_a_1213_);
lean_dec_ref(v___x_1211_);
lean_dec_ref(v_fallback_1157_);
lean_dec_ref(v_inst_x27_1156_);
lean_dec_ref(v_h_1155_);
lean_dec_ref(v_c_x27_1154_);
lean_dec_ref(v_b_1153_);
lean_dec_ref(v_a_1152_);
lean_dec_ref(v_inst_1151_);
lean_dec_ref(v_c_1150_);
lean_dec_ref(v_00_u03b1_1149_);
return v___x_1217_;
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_dec_ref(v___x_1211_);
lean_dec_ref(v_fallback_1157_);
lean_dec_ref(v_inst_x27_1156_);
lean_dec_ref(v_h_1155_);
lean_dec_ref(v_c_x27_1154_);
lean_dec_ref(v_b_1153_);
lean_dec_ref(v_a_1152_);
lean_dec_ref(v_inst_1151_);
lean_dec_ref(v_c_1150_);
lean_dec_ref(v_00_u03b1_1149_);
v_a_1274_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1212_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1212_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec_ref(v_fallback_1157_);
lean_dec_ref(v_inst_x27_1156_);
lean_dec_ref(v_h_1155_);
lean_dec_ref(v_c_x27_1154_);
lean_dec_ref(v_b_1153_);
lean_dec_ref(v_a_1152_);
lean_dec_ref(v_inst_1151_);
lean_dec_ref(v_c_1150_);
lean_dec_ref(v_00_u03b1_1149_);
v_a_1282_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1172_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1172_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1148_ = stack[0].m_obj;
lean_object* v_00_u03b1_1149_ = stack[1].m_obj;
lean_object* v_c_1150_ = stack[2].m_obj;
lean_object* v_inst_1151_ = stack[3].m_obj;
lean_object* v_a_1152_ = stack[4].m_obj;
lean_object* v_b_1153_ = stack[5].m_obj;
lean_object* v_c_x27_1154_ = stack[6].m_obj;
lean_object* v_h_1155_ = stack[7].m_obj;
lean_object* v_inst_x27_1156_ = stack[8].m_obj;
lean_object* v_fallback_1157_ = stack[9].m_obj;
lean_object* v_a_1158_ = stack[10].m_obj;
lean_object* v_a_1159_ = stack[11].m_obj;
lean_object* v_a_1160_ = stack[12].m_obj;
lean_object* v_a_1161_ = stack[13].m_obj;
lean_object* v_a_1162_ = stack[14].m_obj;
lean_object* v_a_1163_ = stack[15].m_obj;
lean_object* v_a_1164_ = stack[16].m_obj;
lean_object* v_a_1165_ = stack[17].m_obj;
lean_object* v_a_1166_ = stack[18].m_obj;
lean_object* v_res_1290_;
v_res_1290_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr(v_f_1148_, v_00_u03b1_1149_, v_c_1150_, v_inst_1151_, v_a_1152_, v_b_1153_, v_c_x27_1154_, v_h_1155_, v_inst_x27_1156_, v_fallback_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_);
stack->m_obj
 = v_res_1290_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_1291_ = _args[0];
lean_object* v_00_u03b1_1292_ = _args[1];
lean_object* v_c_1293_ = _args[2];
lean_object* v_inst_1294_ = _args[3];
lean_object* v_a_1295_ = _args[4];
lean_object* v_b_1296_ = _args[5];
lean_object* v_c_x27_1297_ = _args[6];
lean_object* v_h_1298_ = _args[7];
lean_object* v_inst_x27_1299_ = _args[8];
lean_object* v_fallback_1300_ = _args[9];
lean_object* v_a_1301_ = _args[10];
lean_object* v_a_1302_ = _args[11];
lean_object* v_a_1303_ = _args[12];
lean_object* v_a_1304_ = _args[13];
lean_object* v_a_1305_ = _args[14];
lean_object* v_a_1306_ = _args[15];
lean_object* v_a_1307_ = _args[16];
lean_object* v_a_1308_ = _args[17];
lean_object* v_a_1309_ = _args[18];
lean_object* v_a_1310_ = _args[19];
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr(v_f_1291_, v_00_u03b1_1292_, v_c_1293_, v_inst_1294_, v_a_1295_, v_b_1296_, v_c_x27_1297_, v_h_1298_, v_inst_x27_1299_, v_fallback_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v_a_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec_ref(v_f_1291_);
return v_res_1311_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0(lean_object* v___x_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1312_);
return v___x_1323_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1312_ = stack[0].m_obj;
lean_object* v___y_1313_ = stack[1].m_obj;
lean_object* v___y_1314_ = stack[2].m_obj;
lean_object* v___y_1315_ = stack[3].m_obj;
lean_object* v___y_1316_ = stack[4].m_obj;
lean_object* v___y_1317_ = stack[5].m_obj;
lean_object* v___y_1318_ = stack[6].m_obj;
lean_object* v___y_1319_ = stack[7].m_obj;
lean_object* v___y_1320_ = stack[8].m_obj;
lean_object* v___y_1321_ = stack[9].m_obj;
lean_object* v_res_1324_;
v_res_1324_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0(v___x_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
stack->m_obj
 = v_res_1324_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed(lean_object* v___x_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0(v___x_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
return v_res_1336_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg(lean_object* v_f_1337_, lean_object* v_a_u2081_1338_, lean_object* v_a_u2082_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(v_f_1337_, v_a_u2081_1338_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1349_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1347_, 1);
v___x_1349_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(v_a_1348_, v_a_u2082_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
return v___x_1349_;
}
else
{
lean_dec_ref(v_a_u2082_1339_);
return v___x_1347_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1337_ = stack[0].m_obj;
lean_object* v_a_u2081_1338_ = stack[1].m_obj;
lean_object* v_a_u2082_1339_ = stack[2].m_obj;
lean_object* v___y_1340_ = stack[3].m_obj;
lean_object* v___y_1341_ = stack[4].m_obj;
lean_object* v___y_1342_ = stack[5].m_obj;
lean_object* v___y_1343_ = stack[6].m_obj;
lean_object* v___y_1344_ = stack[7].m_obj;
lean_object* v___y_1345_ = stack[8].m_obj;
lean_object* v_res_1350_;
v_res_1350_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg(v_f_1337_, v_a_u2081_1338_, v_a_u2082_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
stack->m_obj
 = v_res_1350_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_1351_, lean_object* v_a_u2081_1352_, lean_object* v_a_u2082_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg(v_f_1351_, v_a_u2081_1352_, v_a_u2082_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
return v_res_1361_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(lean_object* v_f_1362_, lean_object* v_a_u2081_1363_, lean_object* v_a_u2082_1364_, lean_object* v_a_u2083_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg(v_f_1362_, v_a_u2081_1363_, v_a_u2082_1364_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1378_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
v___x_1378_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(v_a_1377_, v_a_u2083_1365_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
return v___x_1378_;
}
else
{
lean_dec_ref(v_a_u2083_1365_);
return v___x_1376_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1362_ = stack[0].m_obj;
lean_object* v_a_u2081_1363_ = stack[1].m_obj;
lean_object* v_a_u2082_1364_ = stack[2].m_obj;
lean_object* v_a_u2083_1365_ = stack[3].m_obj;
lean_object* v___y_1366_ = stack[4].m_obj;
lean_object* v___y_1367_ = stack[5].m_obj;
lean_object* v___y_1368_ = stack[6].m_obj;
lean_object* v___y_1369_ = stack[7].m_obj;
lean_object* v___y_1370_ = stack[8].m_obj;
lean_object* v___y_1371_ = stack[9].m_obj;
lean_object* v___y_1372_ = stack[10].m_obj;
lean_object* v___y_1373_ = stack[11].m_obj;
lean_object* v___y_1374_ = stack[12].m_obj;
lean_object* v_res_1379_;
v_res_1379_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(v_f_1362_, v_a_u2081_1363_, v_a_u2082_1364_, v_a_u2083_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
stack->m_obj
 = v_res_1379_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___boxed(lean_object* v_f_1380_, lean_object* v_a_u2081_1381_, lean_object* v_a_u2082_1382_, lean_object* v_a_u2083_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(v_f_1380_, v_a_u2081_1381_, v_a_u2082_1382_, v_a_u2083_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
return v_res_1394_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(lean_object* v_f_1395_, lean_object* v_a_u2081_1396_, lean_object* v_a_u2082_1397_, lean_object* v_a_u2083_1398_, lean_object* v_a_u2084_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(v_f_1395_, v_a_u2081_1396_, v_a_u2082_1397_, v_a_u2083_1398_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1412_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1411_);
lean_dec_ref_known(v___x_1410_, 1);
v___x_1412_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__1_spec__1_spec__2___redArg(v_a_1411_, v_a_u2084_1399_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
return v___x_1412_;
}
else
{
lean_dec_ref(v_a_u2084_1399_);
return v___x_1410_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1395_ = stack[0].m_obj;
lean_object* v_a_u2081_1396_ = stack[1].m_obj;
lean_object* v_a_u2082_1397_ = stack[2].m_obj;
lean_object* v_a_u2083_1398_ = stack[3].m_obj;
lean_object* v_a_u2084_1399_ = stack[4].m_obj;
lean_object* v___y_1400_ = stack[5].m_obj;
lean_object* v___y_1401_ = stack[6].m_obj;
lean_object* v___y_1402_ = stack[7].m_obj;
lean_object* v___y_1403_ = stack[8].m_obj;
lean_object* v___y_1404_ = stack[9].m_obj;
lean_object* v___y_1405_ = stack[10].m_obj;
lean_object* v___y_1406_ = stack[11].m_obj;
lean_object* v___y_1407_ = stack[12].m_obj;
lean_object* v___y_1408_ = stack[13].m_obj;
lean_object* v_res_1413_;
v_res_1413_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v_f_1395_, v_a_u2081_1396_, v_a_u2082_1397_, v_a_u2083_1398_, v_a_u2084_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
stack->m_obj
 = v_res_1413_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0___boxed(lean_object* v_f_1414_, lean_object* v_a_u2081_1415_, lean_object* v_a_u2082_1416_, lean_object* v_a_u2083_1417_, lean_object* v_a_u2084_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v_f_1414_, v_a_u2081_1415_, v_a_u2082_1416_, v_a_u2083_1417_, v_a_u2084_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
return v_res_1429_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2(lean_object* v___x_1435_, lean_object* v_e_x27_1436_, lean_object* v_snd_1437_, lean_object* v_arg_1438_, lean_object* v_arg_1439_, lean_object* v_e_1440_, lean_object* v_proof_1441_, uint8_t v___x_1442_, uint8_t v_contextDependent_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v___x_1454_; 
lean_inc_ref(v_snd_1437_);
lean_inc_ref(v_e_x27_1436_);
v___x_1454_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v___x_1435_, v_e_x27_1436_, v_snd_1437_, v_arg_1438_, v_arg_1439_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1466_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1466_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1466_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; 
v___x_1459_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1));
v___x_1460_ = l_Lean_Expr_replaceFn(v_e_1440_, v___x_1459_);
v___x_1461_ = l_Lean_mkApp3(v___x_1460_, v_e_x27_1436_, v_snd_1437_, v_proof_1441_);
v___x_1462_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1462_, 0, v_a_1455_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
lean_ctor_set_uint8(v___x_1462_, sizeof(void*)*2, v___x_1442_);
lean_ctor_set_uint8(v___x_1462_, sizeof(void*)*2 + 1, v_contextDependent_1443_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v___x_1462_);
v___x_1464_ = v___x_1457_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec_ref(v_proof_1441_);
lean_dec_ref(v_e_1440_);
lean_dec_ref(v_snd_1437_);
lean_dec_ref(v_e_x27_1436_);
v_a_1467_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1454_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1454_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1435_ = stack[0].m_obj;
lean_object* v_e_x27_1436_ = stack[1].m_obj;
lean_object* v_snd_1437_ = stack[2].m_obj;
lean_object* v_arg_1438_ = stack[3].m_obj;
lean_object* v_arg_1439_ = stack[4].m_obj;
lean_object* v_e_1440_ = stack[5].m_obj;
lean_object* v_proof_1441_ = stack[6].m_obj;
uint8_t v___x_1442_ = stack[7].m_num;
uint8_t v_contextDependent_1443_ = stack[8].m_num;
lean_object* v___y_1444_ = stack[9].m_obj;
lean_object* v___y_1445_ = stack[10].m_obj;
lean_object* v___y_1446_ = stack[11].m_obj;
lean_object* v___y_1447_ = stack[12].m_obj;
lean_object* v___y_1448_ = stack[13].m_obj;
lean_object* v___y_1449_ = stack[14].m_obj;
lean_object* v___y_1450_ = stack[15].m_obj;
lean_object* v___y_1451_ = stack[16].m_obj;
lean_object* v___y_1452_ = stack[17].m_obj;
lean_object* v_res_1475_;
v_res_1475_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2(v___x_1435_, v_e_x27_1436_, v_snd_1437_, v_arg_1438_, v_arg_1439_, v_e_1440_, v_proof_1441_, v___x_1442_, v_contextDependent_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
stack->m_obj
 = v_res_1475_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___boxed(lean_object** _args){
lean_object* v___x_1476_ = _args[0];
lean_object* v_e_x27_1477_ = _args[1];
lean_object* v_snd_1478_ = _args[2];
lean_object* v_arg_1479_ = _args[3];
lean_object* v_arg_1480_ = _args[4];
lean_object* v_e_1481_ = _args[5];
lean_object* v_proof_1482_ = _args[6];
lean_object* v___x_1483_ = _args[7];
lean_object* v_contextDependent_1484_ = _args[8];
lean_object* v___y_1485_ = _args[9];
lean_object* v___y_1486_ = _args[10];
lean_object* v___y_1487_ = _args[11];
lean_object* v___y_1488_ = _args[12];
lean_object* v___y_1489_ = _args[13];
lean_object* v___y_1490_ = _args[14];
lean_object* v___y_1491_ = _args[15];
lean_object* v___y_1492_ = _args[16];
lean_object* v___y_1493_ = _args[17];
lean_object* v___y_1494_ = _args[18];
_start:
{
uint8_t v___x_14874__boxed_1495_; uint8_t v_contextDependent_14875__boxed_1496_; lean_object* v_res_1497_; 
v___x_14874__boxed_1495_ = lean_unbox(v___x_1483_);
v_contextDependent_14875__boxed_1496_ = lean_unbox(v_contextDependent_1484_);
v_res_1497_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2(v___x_1476_, v_e_x27_1477_, v_snd_1478_, v_arg_1479_, v_arg_1480_, v_e_1481_, v_proof_1482_, v___x_14874__boxed_1495_, v_contextDependent_14875__boxed_1496_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
return v_res_1497_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1(uint8_t v___x_1511_, lean_object* v_e_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v___x_1526_; uint8_t v___x_1527_; 
lean_inc_ref(v_e_1512_);
v___x_1526_ = l_Lean_Expr_cleanupAnnotations(v_e_1512_);
v___x_1527_ = l_Lean_Expr_isApp(v___x_1526_);
if (v___x_1527_ == 0)
{
lean_dec_ref(v___x_1526_);
lean_dec_ref(v_e_1512_);
goto v___jp_1523_;
}
else
{
lean_object* v_arg_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v_arg_1528_ = lean_ctor_get(v___x_1526_, 1);
lean_inc_ref(v_arg_1528_);
v___x_1529_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1526_);
v___x_1530_ = l_Lean_Expr_isApp(v___x_1529_);
if (v___x_1530_ == 0)
{
lean_dec_ref(v___x_1529_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_e_1512_);
goto v___jp_1523_;
}
else
{
lean_object* v_arg_1531_; lean_object* v___x_1532_; uint8_t v___x_1533_; 
v_arg_1531_ = lean_ctor_get(v___x_1529_, 1);
lean_inc_ref(v_arg_1531_);
v___x_1532_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1529_);
v___x_1533_ = l_Lean_Expr_isApp(v___x_1532_);
if (v___x_1533_ == 0)
{
lean_dec_ref(v___x_1532_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_e_1512_);
goto v___jp_1523_;
}
else
{
lean_object* v_arg_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v_arg_1534_ = lean_ctor_get(v___x_1532_, 1);
lean_inc_ref(v_arg_1534_);
v___x_1535_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1532_);
v___x_1536_ = l_Lean_Expr_isApp(v___x_1535_);
if (v___x_1536_ == 0)
{
lean_dec_ref(v___x_1535_);
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_e_1512_);
goto v___jp_1523_;
}
else
{
lean_object* v_arg_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
v_arg_1537_ = lean_ctor_get(v___x_1535_, 1);
lean_inc_ref(v_arg_1537_);
v___x_1538_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1535_);
v___x_1539_ = l_Lean_Expr_isApp(v___x_1538_);
if (v___x_1539_ == 0)
{
lean_dec_ref(v___x_1538_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_e_1512_);
goto v___jp_1523_;
}
else
{
lean_object* v_arg_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v_arg_1540_ = lean_ctor_get(v___x_1538_, 1);
lean_inc_ref(v_arg_1540_);
v___x_1541_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1538_);
v___x_1542_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1));
v___x_1543_ = l_Lean_Expr_isConstOf(v___x_1541_, v___x_1542_);
if (v___x_1543_ == 0)
{
lean_dec_ref(v___x_1541_);
lean_dec_ref(v_arg_1540_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_e_1512_);
goto v___jp_1523_;
}
else
{
lean_object* v___x_1544_; 
lean_inc(v___y_1521_);
lean_inc_ref(v___y_1520_);
lean_inc(v___y_1519_);
lean_inc_ref(v___y_1518_);
lean_inc(v___y_1517_);
lean_inc_ref(v___y_1516_);
lean_inc(v___y_1515_);
lean_inc_ref(v___y_1514_);
lean_inc(v___y_1513_);
lean_inc_ref(v_arg_1537_);
v___x_1544_ = lean_sym_simp(v_arg_1537_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1544_, 1);
if (lean_obj_tag(v_a_1545_) == 0)
{
uint8_t v_contextDependent_1546_; lean_object* v___x_1547_; 
lean_dec_ref(v_e_1512_);
v_contextDependent_1546_ = lean_ctor_get_uint8(v_a_1545_, 1);
lean_dec_ref_known(v_a_1545_, 0);
v___x_1547_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_1537_, v___y_1516_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1588_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1588_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1588_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
uint8_t v___x_1552_; 
v___x_1552_ = lean_unbox(v_a_1548_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
lean_del_object(v___x_1550_);
v___x_1553_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_1537_, v___y_1516_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1571_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1556_ = v___x_1553_;
v_isShared_1557_ = v_isSharedCheck_1571_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1553_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1571_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
uint8_t v___x_1558_; 
v___x_1558_ = lean_unbox(v_a_1554_);
lean_dec(v_a_1554_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; lean_object* v___f_1560_; lean_object* v___x_1561_; 
lean_del_object(v___x_1556_);
lean_dec(v_a_1548_);
v___x_1559_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_1543_, v_contextDependent_1546_);
v___f_1560_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1560_, 0, v___x_1559_);
v___x_1561_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v___x_1541_, v_arg_1540_, v_arg_1537_, v_arg_1534_, v_arg_1531_, v_arg_1528_, v___f_1560_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec_ref(v___x_1541_);
return v___x_1561_;
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; lean_object* v___x_1569_; 
lean_dec_ref(v_arg_1537_);
v___x_1562_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__2));
v___x_1563_ = l_Lean_Expr_constLevels_x21(v___x_1541_);
lean_dec_ref(v___x_1541_);
v___x_1564_ = l_Lean_mkConst(v___x_1562_, v___x_1563_);
lean_inc_ref(v_arg_1528_);
v___x_1565_ = l_Lean_mkApp4(v___x_1564_, v_arg_1540_, v_arg_1534_, v_arg_1531_, v_arg_1528_);
v___x_1566_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1566_, 0, v_arg_1528_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = lean_unbox(v_a_1548_);
lean_dec(v_a_1548_);
lean_ctor_set_uint8(v___x_1566_, sizeof(void*)*2, v___x_1567_);
lean_ctor_set_uint8(v___x_1566_, sizeof(void*)*2 + 1, v_contextDependent_1546_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1566_);
v___x_1569_ = v___x_1556_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1566_);
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
lean_dec(v_a_1548_);
lean_dec_ref(v___x_1541_);
lean_dec_ref(v_arg_1540_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_arg_1528_);
v_a_1572_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1553_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1553_);
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
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1586_; 
lean_dec(v_a_1548_);
lean_dec_ref(v_arg_1537_);
v___x_1580_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__3));
v___x_1581_ = l_Lean_Expr_constLevels_x21(v___x_1541_);
lean_dec_ref(v___x_1541_);
v___x_1582_ = l_Lean_mkConst(v___x_1580_, v___x_1581_);
lean_inc_ref(v_arg_1531_);
v___x_1583_ = l_Lean_mkApp4(v___x_1582_, v_arg_1540_, v_arg_1534_, v_arg_1531_, v_arg_1528_);
v___x_1584_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1584_, 0, v_arg_1531_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
lean_ctor_set_uint8(v___x_1584_, sizeof(void*)*2, v___x_1511_);
lean_ctor_set_uint8(v___x_1584_, sizeof(void*)*2 + 1, v_contextDependent_1546_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1584_);
v___x_1586_ = v___x_1550_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1584_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
else
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec_ref(v___x_1541_);
lean_dec_ref(v_arg_1540_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_arg_1528_);
v_a_1589_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1547_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1547_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
else
{
lean_object* v_e_x27_1597_; lean_object* v_proof_1598_; uint8_t v_contextDependent_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1677_; 
v_e_x27_1597_ = lean_ctor_get(v_a_1545_, 0);
v_proof_1598_ = lean_ctor_get(v_a_1545_, 1);
v_contextDependent_1599_ = lean_ctor_get_uint8(v_a_1545_, sizeof(void*)*2 + 1);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_a_1545_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1601_ = v_a_1545_;
v_isShared_1602_ = v_isSharedCheck_1677_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_proof_1598_);
lean_inc(v_e_x27_1597_);
lean_dec(v_a_1545_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1677_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_1597_, v___y_1516_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1668_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1668_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1668_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
uint8_t v___x_1608_; 
v___x_1608_ = lean_unbox(v_a_1604_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; 
lean_del_object(v___x_1606_);
v___x_1609_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_1597_, v___y_1516_);
lean_dec_ref(v_e_x27_1597_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1650_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1612_ = v___x_1609_;
v_isShared_1613_ = v_isSharedCheck_1650_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1609_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1650_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
uint8_t v___x_1614_; 
v___x_1614_ = lean_unbox(v_a_1610_);
lean_dec(v_a_1610_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; 
lean_del_object(v___x_1612_);
lean_dec(v_a_1604_);
lean_del_object(v___x_1601_);
lean_dec_ref(v_proof_1598_);
lean_inc_ref(v_arg_1534_);
v___x_1615_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance(v_arg_1534_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v_fst_1617_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref_known(v___x_1615_, 1);
v_fst_1617_ = lean_ctor_get(v_a_1616_, 0);
lean_inc(v_fst_1617_);
if (lean_obj_tag(v_fst_1617_) == 0)
{
uint8_t v_contextDependent_1618_; lean_object* v___x_1619_; lean_object* v___f_1620_; lean_object* v___x_1621_; 
lean_dec(v_a_1616_);
lean_dec_ref(v_e_1512_);
v_contextDependent_1618_ = lean_ctor_get_uint8(v_fst_1617_, 1);
lean_dec_ref_known(v_fst_1617_, 0);
v___x_1619_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_1543_, v_contextDependent_1618_);
v___f_1620_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1620_, 0, v___x_1619_);
v___x_1621_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v___x_1541_, v_arg_1540_, v_arg_1537_, v_arg_1534_, v_arg_1531_, v_arg_1528_, v___f_1620_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec_ref(v___x_1541_);
return v___x_1621_;
}
else
{
lean_object* v_snd_1622_; lean_object* v_e_x27_1623_; lean_object* v_proof_1624_; uint8_t v_contextDependent_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___f_1630_; lean_object* v___x_1631_; 
v_snd_1622_ = lean_ctor_get(v_a_1616_, 1);
lean_inc_n(v_snd_1622_, 2);
lean_dec(v_a_1616_);
v_e_x27_1623_ = lean_ctor_get(v_fst_1617_, 0);
lean_inc_ref_n(v_e_x27_1623_, 2);
v_proof_1624_ = lean_ctor_get(v_fst_1617_, 1);
lean_inc_ref_n(v_proof_1624_, 2);
v_contextDependent_1625_ = lean_ctor_get_uint8(v_fst_1617_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_1617_, 2);
v___x_1626_ = lean_unsigned_to_nat(4u);
v___x_1627_ = l_Lean_Expr_getBoundedAppFn(v___x_1626_, v_e_1512_);
v___x_1628_ = lean_box(v___x_1543_);
v___x_1629_ = lean_box(v_contextDependent_1625_);
lean_inc_ref(v_arg_1528_);
lean_inc_ref(v_arg_1531_);
v___f_1630_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___boxed), 19, 9);
lean_closure_set(v___f_1630_, 0, v___x_1627_);
lean_closure_set(v___f_1630_, 1, v_e_x27_1623_);
lean_closure_set(v___f_1630_, 2, v_snd_1622_);
lean_closure_set(v___f_1630_, 3, v_arg_1531_);
lean_closure_set(v___f_1630_, 4, v_arg_1528_);
lean_closure_set(v___f_1630_, 5, v_e_1512_);
lean_closure_set(v___f_1630_, 6, v_proof_1624_);
lean_closure_set(v___f_1630_, 7, v___x_1628_);
lean_closure_set(v___f_1630_, 8, v___x_1629_);
v___x_1631_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr(v___x_1541_, v_arg_1540_, v_arg_1537_, v_arg_1534_, v_arg_1531_, v_arg_1528_, v_e_x27_1623_, v_proof_1624_, v_snd_1622_, v___f_1630_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec_ref(v___x_1541_);
return v___x_1631_;
}
}
else
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
lean_dec_ref(v___x_1541_);
lean_dec_ref(v_arg_1540_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_e_1512_);
v_a_1632_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1634_ = v___x_1615_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1615_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1632_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
lean_dec_ref(v___x_1541_);
lean_dec_ref(v_arg_1540_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1531_);
v___x_1640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__5));
v___x_1641_ = l_Lean_Expr_replaceFn(v_e_1512_, v___x_1640_);
v___x_1642_ = l_Lean_Expr_app___override(v___x_1641_, v_proof_1598_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 1, v___x_1642_);
lean_ctor_set(v___x_1601_, 0, v_arg_1528_);
v___x_1644_ = v___x_1601_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_arg_1528_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
uint8_t v___x_1645_; lean_object* v___x_1647_; 
v___x_1645_ = lean_unbox(v_a_1604_);
lean_dec(v_a_1604_);
lean_ctor_set_uint8(v___x_1644_, sizeof(void*)*2, v___x_1645_);
lean_ctor_set_uint8(v___x_1644_, sizeof(void*)*2 + 1, v_contextDependent_1599_);
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 0, v___x_1644_);
v___x_1647_ = v___x_1612_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1644_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
lean_dec(v_a_1604_);
lean_del_object(v___x_1601_);
lean_dec_ref(v_proof_1598_);
lean_dec_ref(v___x_1541_);
lean_dec_ref(v_arg_1540_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_e_1512_);
v_a_1651_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1609_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1609_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1663_; 
lean_dec(v_a_1604_);
lean_dec_ref(v_e_x27_1597_);
lean_dec_ref(v___x_1541_);
lean_dec_ref(v_arg_1540_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1528_);
v___x_1659_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__7));
v___x_1660_ = l_Lean_Expr_replaceFn(v_e_1512_, v___x_1659_);
v___x_1661_ = l_Lean_Expr_app___override(v___x_1660_, v_proof_1598_);
if (v_isShared_1602_ == 0)
{
lean_ctor_set(v___x_1601_, 1, v___x_1661_);
lean_ctor_set(v___x_1601_, 0, v_arg_1531_);
v___x_1663_ = v___x_1601_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_arg_1531_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v___x_1661_);
lean_ctor_set_uint8(v_reuseFailAlloc_1667_, sizeof(void*)*2 + 1, v_contextDependent_1599_);
v___x_1663_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1665_; 
lean_ctor_set_uint8(v___x_1663_, sizeof(void*)*2, v___x_1511_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1663_);
v___x_1665_ = v___x_1606_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1663_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_del_object(v___x_1601_);
lean_dec_ref(v_proof_1598_);
lean_dec_ref(v_e_x27_1597_);
lean_dec_ref(v___x_1541_);
lean_dec_ref(v_arg_1540_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_e_1512_);
v_a_1669_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1603_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1603_);
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
}
else
{
lean_dec_ref(v___x_1541_);
lean_dec_ref(v_arg_1540_);
lean_dec_ref(v_arg_1537_);
lean_dec_ref(v_arg_1534_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_arg_1528_);
lean_dec_ref(v_e_1512_);
return v___x_1544_;
}
}
}
}
}
}
}
v___jp_1523_:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1524_, 0, v___x_1511_);
lean_ctor_set_uint8(v___x_1524_, 1, v___x_1511_);
v___x_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
return v___x_1525_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1511_ = stack[0].m_num;
lean_object* v_e_1512_ = stack[1].m_obj;
lean_object* v___y_1513_ = stack[2].m_obj;
lean_object* v___y_1514_ = stack[3].m_obj;
lean_object* v___y_1515_ = stack[4].m_obj;
lean_object* v___y_1516_ = stack[5].m_obj;
lean_object* v___y_1517_ = stack[6].m_obj;
lean_object* v___y_1518_ = stack[7].m_obj;
lean_object* v___y_1519_ = stack[8].m_obj;
lean_object* v___y_1520_ = stack[9].m_obj;
lean_object* v___y_1521_ = stack[10].m_obj;
lean_object* v_res_1678_;
v_res_1678_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1(v___x_1511_, v_e_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
stack->m_obj
 = v_res_1678_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___boxed(lean_object* v___x_1679_, lean_object* v_e_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
uint8_t v___x_15059__boxed_1691_; lean_object* v_res_1692_; 
v___x_15059__boxed_1691_ = lean_unbox(v___x_1679_);
v_res_1692_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1(v___x_15059__boxed_1691_, v_e_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
return v_res_1692_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv(lean_object* v_e_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v_numArgs_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; 
v_numArgs_1704_ = l_Lean_Expr_getAppNumArgs(v_e_1693_);
v___x_1705_ = lean_unsigned_to_nat(5u);
v___x_1706_ = lean_nat_dec_lt(v_numArgs_1704_, v___x_1705_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; lean_object* v___f_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1707_ = lean_box(v___x_1706_);
v___f_1708_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___boxed), 12, 1);
lean_closure_set(v___f_1708_, 0, v___x_1707_);
v___x_1709_ = lean_nat_sub(v_numArgs_1704_, v___x_1705_);
lean_dec(v_numArgs_1704_);
v___x_1710_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_1693_, v___x_1709_, v___f_1708_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
lean_dec(v___x_1709_);
return v___x_1710_;
}
else
{
uint8_t v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_dec(v_numArgs_1704_);
lean_dec_ref(v_e_1693_);
v___x_1711_ = 0;
v___x_1712_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1712_, 0, v___x_1706_);
lean_ctor_set_uint8(v___x_1712_, 1, v___x_1711_);
v___x_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
return v___x_1713_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1693_ = stack[0].m_obj;
lean_object* v_a_1694_ = stack[1].m_obj;
lean_object* v_a_1695_ = stack[2].m_obj;
lean_object* v_a_1696_ = stack[3].m_obj;
lean_object* v_a_1697_ = stack[4].m_obj;
lean_object* v_a_1698_ = stack[5].m_obj;
lean_object* v_a_1699_ = stack[6].m_obj;
lean_object* v_a_1700_ = stack[7].m_obj;
lean_object* v_a_1701_ = stack[8].m_obj;
lean_object* v_a_1702_ = stack[9].m_obj;
lean_object* v_res_1714_;
v_res_1714_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv(v_e_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
stack->m_obj
 = v_res_1714_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed(lean_object* v_e_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv(v_e_1715_, v_a_1716_, v_a_1717_, v_a_1718_, v_a_1719_, v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_);
lean_dec(v_a_1724_);
lean_dec_ref(v_a_1723_);
lean_dec(v_a_1722_);
lean_dec_ref(v_a_1721_);
lean_dec(v_a_1720_);
lean_dec_ref(v_a_1719_);
lean_dec(v_a_1718_);
lean_dec_ref(v_a_1717_);
lean_dec(v_a_1716_);
return v_res_1726_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(lean_object* v_f_1727_, lean_object* v_a_u2081_1728_, lean_object* v_a_u2082_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg(v_f_1727_, v_a_u2081_1728_, v_a_u2082_1729_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1727_ = stack[0].m_obj;
lean_object* v_a_u2081_1728_ = stack[1].m_obj;
lean_object* v_a_u2082_1729_ = stack[2].m_obj;
lean_object* v___y_1730_ = stack[3].m_obj;
lean_object* v___y_1731_ = stack[4].m_obj;
lean_object* v___y_1732_ = stack[5].m_obj;
lean_object* v___y_1733_ = stack[6].m_obj;
lean_object* v___y_1734_ = stack[7].m_obj;
lean_object* v___y_1735_ = stack[8].m_obj;
lean_object* v___y_1736_ = stack[9].m_obj;
lean_object* v___y_1737_ = stack[10].m_obj;
lean_object* v___y_1738_ = stack[11].m_obj;
lean_object* v_res_1741_;
v_res_1741_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(v_f_1727_, v_a_u2081_1728_, v_a_u2082_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
stack->m_obj
 = v_res_1741_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___boxed(lean_object* v_f_1742_, lean_object* v_a_u2081_1743_, lean_object* v_a_u2082_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(v_f_1742_, v_a_u2081_1743_, v_a_u2082_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
return v_res_1755_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1813_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_));
v___x_1814_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_));
v___x_1815_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed), 11, 0);
v___x_1816_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_1813_, v___x_1814_, v___x_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1817_;
v_res_1817_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_();
stack->m_obj
 = v_res_1817_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17____boxed(lean_object* v_a_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_();
return v_res_1819_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_1821_; uint8_t v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_));
v___x_1822_ = 0;
v___x_1823_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed), 11, 0);
v___x_1824_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_1821_, v___x_1822_, v___x_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_19__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1825_;
v_res_1825_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_19_();
stack->m_obj
 = v_res_1825_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_19____boxed(lean_object* v_a_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_19_();
return v_res_1827_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(lean_object* v_f_1838_, lean_object* v_00_u03b1_1839_, lean_object* v_c_1840_, lean_object* v_inst_1841_, lean_object* v_a_1842_, lean_object* v_b_1843_, lean_object* v_instToMatch_1844_, lean_object* v_fallback_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_instToMatch_1844_, v_a_1852_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1857_);
lean_dec_ref_known(v___x_1856_, 1);
v___x_1858_ = l_Lean_Expr_cleanupAnnotations(v_a_1857_);
v___x_1859_ = l_Lean_Expr_isApp(v___x_1858_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; 
lean_dec_ref(v___x_1858_);
lean_dec_ref(v_b_1843_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_inst_1841_);
lean_dec_ref(v_c_1840_);
lean_dec_ref(v_00_u03b1_1839_);
lean_inc(v_a_1854_);
lean_inc_ref(v_a_1853_);
lean_inc(v_a_1852_);
lean_inc_ref(v_a_1851_);
lean_inc(v_a_1850_);
lean_inc_ref(v_a_1849_);
lean_inc(v_a_1848_);
lean_inc_ref(v_a_1847_);
lean_inc(v_a_1846_);
v___x_1860_ = lean_apply_10(v_fallback_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, lean_box(0));
return v___x_1860_;
}
else
{
lean_object* v_arg_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v_arg_1861_ = lean_ctor_get(v___x_1858_, 1);
lean_inc_ref(v_arg_1861_);
v___x_1862_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1858_);
v___x_1863_ = l_Lean_Expr_isApp(v___x_1862_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; 
lean_dec_ref(v___x_1862_);
lean_dec_ref(v_arg_1861_);
lean_dec_ref(v_b_1843_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_inst_1841_);
lean_dec_ref(v_c_1840_);
lean_dec_ref(v_00_u03b1_1839_);
lean_inc(v_a_1854_);
lean_inc_ref(v_a_1853_);
lean_inc(v_a_1852_);
lean_inc_ref(v_a_1851_);
lean_inc(v_a_1850_);
lean_inc_ref(v_a_1849_);
lean_inc(v_a_1848_);
lean_inc_ref(v_a_1847_);
lean_inc(v_a_1846_);
v___x_1864_ = lean_apply_10(v_fallback_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, lean_box(0));
return v___x_1864_;
}
else
{
lean_object* v_arg_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v_arg_1865_ = lean_ctor_get(v___x_1862_, 1);
lean_inc_ref(v_arg_1865_);
v___x_1866_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1862_);
v___x_1867_ = l_Lean_Expr_isApp(v___x_1866_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; 
lean_dec_ref(v___x_1866_);
lean_dec_ref(v_arg_1865_);
lean_dec_ref(v_arg_1861_);
lean_dec_ref(v_b_1843_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_inst_1841_);
lean_dec_ref(v_c_1840_);
lean_dec_ref(v_00_u03b1_1839_);
lean_inc(v_a_1854_);
lean_inc_ref(v_a_1853_);
lean_inc(v_a_1852_);
lean_inc_ref(v_a_1851_);
lean_inc(v_a_1850_);
lean_inc_ref(v_a_1849_);
lean_inc(v_a_1848_);
lean_inc_ref(v_a_1847_);
lean_inc(v_a_1846_);
v___x_1868_ = lean_apply_10(v_fallback_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, lean_box(0));
return v___x_1868_;
}
else
{
lean_object* v___x_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1869_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1866_);
v___x_1870_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_1871_ = l_Lean_Expr_isConstOf(v___x_1869_, v___x_1870_);
lean_dec_ref(v___x_1869_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; 
lean_dec_ref(v_arg_1865_);
lean_dec_ref(v_arg_1861_);
lean_dec_ref(v_b_1843_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_inst_1841_);
lean_dec_ref(v_c_1840_);
lean_dec_ref(v_00_u03b1_1839_);
lean_inc(v_a_1854_);
lean_inc_ref(v_a_1853_);
lean_inc(v_a_1852_);
lean_inc_ref(v_a_1851_);
lean_inc(v_a_1850_);
lean_inc_ref(v_a_1849_);
lean_inc(v_a_1848_);
lean_inc_ref(v_a_1847_);
lean_inc(v_a_1846_);
v___x_1872_ = lean_apply_10(v_fallback_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, lean_box(0));
return v___x_1872_;
}
else
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1865_, v_a_1852_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_a_1874_);
lean_dec_ref_known(v___x_1873_, 1);
v___x_1875_ = l_Lean_Expr_cleanupAnnotations(v_a_1874_);
v___x_1876_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_1877_ = l_Lean_Expr_isConstOf(v___x_1875_, v___x_1876_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; uint8_t v___x_1879_; 
v___x_1878_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_1879_ = l_Lean_Expr_isConstOf(v___x_1875_, v___x_1878_);
lean_dec_ref(v___x_1875_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; 
lean_dec_ref(v_arg_1861_);
lean_dec_ref(v_b_1843_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_inst_1841_);
lean_dec_ref(v_c_1840_);
lean_dec_ref(v_00_u03b1_1839_);
lean_inc(v_a_1854_);
lean_inc_ref(v_a_1853_);
lean_inc(v_a_1852_);
lean_inc_ref(v_a_1851_);
lean_inc(v_a_1850_);
lean_inc_ref(v_a_1849_);
lean_inc(v_a_1848_);
lean_inc_ref(v_a_1847_);
lean_inc(v_a_1846_);
v___x_1880_ = lean_apply_10(v_fallback_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, lean_box(0));
return v___x_1880_;
}
else
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_dec_ref(v_fallback_1845_);
v___x_1881_ = lean_unsigned_to_nat(1u);
v___x_1882_ = lean_mk_empty_array_with_capacity(v___x_1881_);
lean_inc_ref(v_arg_1861_);
v___x_1883_ = lean_array_push(v___x_1882_, v_arg_1861_);
lean_inc_ref(v_a_1842_);
v___x_1884_ = l_Lean_Expr_betaRev(v_a_1842_, v___x_1883_, v___x_1877_, v___x_1877_);
lean_dec_ref(v___x_1883_);
v___x_1885_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1884_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1898_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1888_ = v___x_1885_;
v_isShared_1889_ = v_isSharedCheck_1898_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1885_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1898_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1890_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1));
v___x_1891_ = l_Lean_Expr_constLevels_x21(v_f_1838_);
v___x_1892_ = l_Lean_mkConst(v___x_1890_, v___x_1891_);
v___x_1893_ = l_Lean_mkApp6(v___x_1892_, v_00_u03b1_1839_, v_c_1840_, v_inst_1841_, v_a_1842_, v_b_1843_, v_arg_1861_);
v___x_1894_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1894_, 0, v_a_1886_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
lean_ctor_set_uint8(v___x_1894_, sizeof(void*)*2, v___x_1877_);
lean_ctor_set_uint8(v___x_1894_, sizeof(void*)*2 + 1, v___x_1877_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1894_);
v___x_1896_ = v___x_1888_;
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
}
else
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1906_; 
lean_dec_ref(v_arg_1861_);
lean_dec_ref(v_b_1843_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_inst_1841_);
lean_dec_ref(v_c_1840_);
lean_dec_ref(v_00_u03b1_1839_);
v_a_1899_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1901_ = v___x_1885_;
v_isShared_1902_ = v_isSharedCheck_1906_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1885_);
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
lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
lean_dec_ref(v___x_1875_);
lean_dec_ref(v_fallback_1845_);
v___x_1907_ = lean_unsigned_to_nat(1u);
v___x_1908_ = lean_mk_empty_array_with_capacity(v___x_1907_);
lean_inc_ref(v_arg_1861_);
v___x_1909_ = lean_array_push(v___x_1908_, v_arg_1861_);
v___x_1910_ = 0;
lean_inc_ref(v_b_1843_);
v___x_1911_ = l_Lean_Expr_betaRev(v_b_1843_, v___x_1909_, v___x_1910_, v___x_1910_);
lean_dec_ref(v___x_1909_);
v___x_1912_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1911_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1925_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1915_ = v___x_1912_;
v_isShared_1916_ = v_isSharedCheck_1925_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1912_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1925_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1917_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3));
v___x_1918_ = l_Lean_Expr_constLevels_x21(v_f_1838_);
v___x_1919_ = l_Lean_mkConst(v___x_1917_, v___x_1918_);
v___x_1920_ = l_Lean_mkApp6(v___x_1919_, v_00_u03b1_1839_, v_c_1840_, v_inst_1841_, v_a_1842_, v_b_1843_, v_arg_1861_);
v___x_1921_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1921_, 0, v_a_1913_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
lean_ctor_set_uint8(v___x_1921_, sizeof(void*)*2, v___x_1910_);
lean_ctor_set_uint8(v___x_1921_, sizeof(void*)*2 + 1, v___x_1910_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 0, v___x_1921_);
v___x_1923_ = v___x_1915_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
else
{
lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec_ref(v_arg_1861_);
lean_dec_ref(v_b_1843_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_inst_1841_);
lean_dec_ref(v_c_1840_);
lean_dec_ref(v_00_u03b1_1839_);
v_a_1926_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v___x_1912_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1912_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec_ref(v_arg_1861_);
lean_dec_ref(v_fallback_1845_);
lean_dec_ref(v_b_1843_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_inst_1841_);
lean_dec_ref(v_c_1840_);
lean_dec_ref(v_00_u03b1_1839_);
v_a_1934_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1873_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1873_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
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
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_dec_ref(v_fallback_1845_);
lean_dec_ref(v_b_1843_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_inst_1841_);
lean_dec_ref(v_c_1840_);
lean_dec_ref(v_00_u03b1_1839_);
v_a_1942_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1856_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1856_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1838_ = stack[0].m_obj;
lean_object* v_00_u03b1_1839_ = stack[1].m_obj;
lean_object* v_c_1840_ = stack[2].m_obj;
lean_object* v_inst_1841_ = stack[3].m_obj;
lean_object* v_a_1842_ = stack[4].m_obj;
lean_object* v_b_1843_ = stack[5].m_obj;
lean_object* v_instToMatch_1844_ = stack[6].m_obj;
lean_object* v_fallback_1845_ = stack[7].m_obj;
lean_object* v_a_1846_ = stack[8].m_obj;
lean_object* v_a_1847_ = stack[9].m_obj;
lean_object* v_a_1848_ = stack[10].m_obj;
lean_object* v_a_1849_ = stack[11].m_obj;
lean_object* v_a_1850_ = stack[12].m_obj;
lean_object* v_a_1851_ = stack[13].m_obj;
lean_object* v_a_1852_ = stack[14].m_obj;
lean_object* v_a_1853_ = stack[15].m_obj;
lean_object* v_a_1854_ = stack[16].m_obj;
lean_object* v_res_1950_;
v_res_1950_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_1838_, v_00_u03b1_1839_, v_c_1840_, v_inst_1841_, v_a_1842_, v_b_1843_, v_instToMatch_1844_, v_fallback_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
stack->m_obj
 = v_res_1950_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___boxed(lean_object** _args){
lean_object* v_f_1951_ = _args[0];
lean_object* v_00_u03b1_1952_ = _args[1];
lean_object* v_c_1953_ = _args[2];
lean_object* v_inst_1954_ = _args[3];
lean_object* v_a_1955_ = _args[4];
lean_object* v_b_1956_ = _args[5];
lean_object* v_instToMatch_1957_ = _args[6];
lean_object* v_fallback_1958_ = _args[7];
lean_object* v_a_1959_ = _args[8];
lean_object* v_a_1960_ = _args[9];
lean_object* v_a_1961_ = _args[10];
lean_object* v_a_1962_ = _args[11];
lean_object* v_a_1963_ = _args[12];
lean_object* v_a_1964_ = _args[13];
lean_object* v_a_1965_ = _args[14];
lean_object* v_a_1966_ = _args[15];
lean_object* v_a_1967_ = _args[16];
lean_object* v_a_1968_ = _args[17];
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_1951_, v_00_u03b1_1952_, v_c_1953_, v_inst_1954_, v_a_1955_, v_b_1956_, v_instToMatch_1957_, v_fallback_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
lean_dec(v_a_1967_);
lean_dec_ref(v_a_1966_);
lean_dec(v_a_1965_);
lean_dec_ref(v_a_1964_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1960_);
lean_dec(v_a_1959_);
lean_dec_ref(v_f_1951_);
return v_res_1969_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2(void){
_start:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1974_ = lean_box(0);
v___x_1975_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__1));
v___x_1976_ = l_Lean_mkConst(v___x_1975_, v___x_1974_);
return v___x_1976_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7(void){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1986_ = lean_box(0);
v___x_1987_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__6));
v___x_1988_ = l_Lean_mkConst(v___x_1987_, v___x_1986_);
return v___x_1988_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(lean_object* v_f_1994_, lean_object* v_00_u03b1_1995_, lean_object* v_c_1996_, lean_object* v_inst_1997_, lean_object* v_a_1998_, lean_object* v_b_1999_, lean_object* v_c_x27_2000_, lean_object* v_h_2001_, lean_object* v_inst_x27_2002_, lean_object* v_fallback_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_x27_2002_, v_a_2010_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
v___x_2016_ = l_Lean_Expr_cleanupAnnotations(v_a_2015_);
v___x_2017_ = l_Lean_Expr_isApp(v___x_2016_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; 
lean_dec_ref(v___x_2016_);
lean_dec_ref(v_h_2001_);
lean_dec_ref(v_c_x27_2000_);
lean_dec_ref(v_b_1999_);
lean_dec_ref(v_a_1998_);
lean_dec_ref(v_inst_1997_);
lean_dec_ref(v_c_1996_);
lean_dec_ref(v_00_u03b1_1995_);
lean_inc(v_a_2012_);
lean_inc_ref(v_a_2011_);
lean_inc(v_a_2010_);
lean_inc_ref(v_a_2009_);
lean_inc(v_a_2008_);
lean_inc_ref(v_a_2007_);
lean_inc(v_a_2006_);
lean_inc_ref(v_a_2005_);
lean_inc(v_a_2004_);
v___x_2018_ = lean_apply_10(v_fallback_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, lean_box(0));
return v___x_2018_;
}
else
{
lean_object* v_arg_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
v_arg_2019_ = lean_ctor_get(v___x_2016_, 1);
lean_inc_ref(v_arg_2019_);
v___x_2020_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2016_);
v___x_2021_ = l_Lean_Expr_isApp(v___x_2020_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; 
lean_dec_ref(v___x_2020_);
lean_dec_ref(v_arg_2019_);
lean_dec_ref(v_h_2001_);
lean_dec_ref(v_c_x27_2000_);
lean_dec_ref(v_b_1999_);
lean_dec_ref(v_a_1998_);
lean_dec_ref(v_inst_1997_);
lean_dec_ref(v_c_1996_);
lean_dec_ref(v_00_u03b1_1995_);
lean_inc(v_a_2012_);
lean_inc_ref(v_a_2011_);
lean_inc(v_a_2010_);
lean_inc_ref(v_a_2009_);
lean_inc(v_a_2008_);
lean_inc_ref(v_a_2007_);
lean_inc(v_a_2006_);
lean_inc_ref(v_a_2005_);
lean_inc(v_a_2004_);
v___x_2022_ = lean_apply_10(v_fallback_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, lean_box(0));
return v___x_2022_;
}
else
{
lean_object* v_arg_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; 
v_arg_2023_ = lean_ctor_get(v___x_2020_, 1);
lean_inc_ref(v_arg_2023_);
v___x_2024_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2020_);
v___x_2025_ = l_Lean_Expr_isApp(v___x_2024_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; 
lean_dec_ref(v___x_2024_);
lean_dec_ref(v_arg_2023_);
lean_dec_ref(v_arg_2019_);
lean_dec_ref(v_h_2001_);
lean_dec_ref(v_c_x27_2000_);
lean_dec_ref(v_b_1999_);
lean_dec_ref(v_a_1998_);
lean_dec_ref(v_inst_1997_);
lean_dec_ref(v_c_1996_);
lean_dec_ref(v_00_u03b1_1995_);
lean_inc(v_a_2012_);
lean_inc_ref(v_a_2011_);
lean_inc(v_a_2010_);
lean_inc_ref(v_a_2009_);
lean_inc(v_a_2008_);
lean_inc_ref(v_a_2007_);
lean_inc(v_a_2006_);
lean_inc_ref(v_a_2005_);
lean_inc(v_a_2004_);
v___x_2026_ = lean_apply_10(v_fallback_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, lean_box(0));
return v___x_2026_;
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2028_; uint8_t v___x_2029_; 
v___x_2027_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2024_);
v___x_2028_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_2029_ = l_Lean_Expr_isConstOf(v___x_2027_, v___x_2028_);
lean_dec_ref(v___x_2027_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; 
lean_dec_ref(v_arg_2023_);
lean_dec_ref(v_arg_2019_);
lean_dec_ref(v_h_2001_);
lean_dec_ref(v_c_x27_2000_);
lean_dec_ref(v_b_1999_);
lean_dec_ref(v_a_1998_);
lean_dec_ref(v_inst_1997_);
lean_dec_ref(v_c_1996_);
lean_dec_ref(v_00_u03b1_1995_);
lean_inc(v_a_2012_);
lean_inc_ref(v_a_2011_);
lean_inc(v_a_2010_);
lean_inc_ref(v_a_2009_);
lean_inc(v_a_2008_);
lean_inc_ref(v_a_2007_);
lean_inc(v_a_2006_);
lean_inc_ref(v_a_2005_);
lean_inc(v_a_2004_);
v___x_2030_ = lean_apply_10(v_fallback_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, lean_box(0));
return v___x_2030_;
}
else
{
lean_object* v___x_2031_; 
v___x_2031_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_2023_, v_a_2010_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2031_, 1);
v___x_2033_ = l_Lean_Expr_cleanupAnnotations(v_a_2032_);
v___x_2034_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_2035_ = l_Lean_Expr_isConstOf(v___x_2033_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2036_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_2037_ = l_Lean_Expr_isConstOf(v___x_2033_, v___x_2036_);
lean_dec_ref(v___x_2033_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; 
lean_dec_ref(v_arg_2019_);
lean_dec_ref(v_h_2001_);
lean_dec_ref(v_c_x27_2000_);
lean_dec_ref(v_b_1999_);
lean_dec_ref(v_a_1998_);
lean_dec_ref(v_inst_1997_);
lean_dec_ref(v_c_1996_);
lean_dec_ref(v_00_u03b1_1995_);
lean_inc(v_a_2012_);
lean_inc_ref(v_a_2011_);
lean_inc(v_a_2010_);
lean_inc_ref(v_a_2009_);
lean_inc(v_a_2008_);
lean_inc_ref(v_a_2007_);
lean_inc(v_a_2006_);
lean_inc_ref(v_a_2005_);
lean_inc(v_a_2004_);
v___x_2038_ = lean_apply_10(v_fallback_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, lean_box(0));
return v___x_2038_;
}
else
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
lean_dec_ref(v_fallback_2003_);
v___x_2039_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2);
lean_inc_ref(v_arg_2019_);
lean_inc_ref(v_h_2001_);
lean_inc_ref(v_c_x27_2000_);
lean_inc_ref(v_c_1996_);
v___x_2040_ = l_Lean_mkApp4(v___x_2039_, v_c_1996_, v_c_x27_2000_, v_h_2001_, v_arg_2019_);
v___x_2041_ = lean_unsigned_to_nat(1u);
v___x_2042_ = lean_mk_empty_array_with_capacity(v___x_2041_);
v___x_2043_ = lean_array_push(v___x_2042_, v___x_2040_);
lean_inc_ref(v_a_1998_);
v___x_2044_ = l_Lean_Expr_betaRev(v_a_1998_, v___x_2043_, v___x_2035_, v___x_2035_);
lean_dec_ref(v___x_2043_);
v___x_2045_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2044_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2058_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2048_ = v___x_2045_;
v_isShared_2049_ = v_isSharedCheck_2058_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2058_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2056_; 
v___x_2050_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4));
v___x_2051_ = l_Lean_Expr_constLevels_x21(v_f_1994_);
v___x_2052_ = l_Lean_mkConst(v___x_2050_, v___x_2051_);
v___x_2053_ = l_Lean_mkApp8(v___x_2052_, v_00_u03b1_1995_, v_c_1996_, v_inst_1997_, v_a_1998_, v_b_1999_, v_c_x27_2000_, v_h_2001_, v_arg_2019_);
v___x_2054_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2054_, 0, v_a_2046_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*2, v___x_2035_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*2 + 1, v___x_2035_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v___x_2054_);
v___x_2056_ = v___x_2048_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec_ref(v_arg_2019_);
lean_dec_ref(v_h_2001_);
lean_dec_ref(v_c_x27_2000_);
lean_dec_ref(v_b_1999_);
lean_dec_ref(v_a_1998_);
lean_dec_ref(v_inst_1997_);
lean_dec_ref(v_c_1996_);
lean_dec_ref(v_00_u03b1_1995_);
v_a_2059_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2045_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2045_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
else
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
lean_dec_ref(v___x_2033_);
lean_dec_ref(v_fallback_2003_);
v___x_2067_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7);
lean_inc_ref(v_arg_2019_);
lean_inc_ref(v_h_2001_);
lean_inc_ref(v_c_x27_2000_);
lean_inc_ref(v_c_1996_);
v___x_2068_ = l_Lean_mkApp4(v___x_2067_, v_c_1996_, v_c_x27_2000_, v_h_2001_, v_arg_2019_);
v___x_2069_ = lean_unsigned_to_nat(1u);
v___x_2070_ = lean_mk_empty_array_with_capacity(v___x_2069_);
v___x_2071_ = lean_array_push(v___x_2070_, v___x_2068_);
v___x_2072_ = 0;
lean_inc_ref(v_b_1999_);
v___x_2073_ = l_Lean_Expr_betaRev(v_b_1999_, v___x_2071_, v___x_2072_, v___x_2072_);
lean_dec_ref(v___x_2071_);
v___x_2074_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2073_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2087_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2077_ = v___x_2074_;
v_isShared_2078_ = v_isSharedCheck_2087_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2087_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2079_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9));
v___x_2080_ = l_Lean_Expr_constLevels_x21(v_f_1994_);
v___x_2081_ = l_Lean_mkConst(v___x_2079_, v___x_2080_);
v___x_2082_ = l_Lean_mkApp8(v___x_2081_, v_00_u03b1_1995_, v_c_1996_, v_inst_1997_, v_a_1998_, v_b_1999_, v_c_x27_2000_, v_h_2001_, v_arg_2019_);
v___x_2083_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2083_, 0, v_a_2075_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
lean_ctor_set_uint8(v___x_2083_, sizeof(void*)*2, v___x_2072_);
lean_ctor_set_uint8(v___x_2083_, sizeof(void*)*2 + 1, v___x_2072_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2083_);
v___x_2085_ = v___x_2077_;
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
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec_ref(v_arg_2019_);
lean_dec_ref(v_h_2001_);
lean_dec_ref(v_c_x27_2000_);
lean_dec_ref(v_b_1999_);
lean_dec_ref(v_a_1998_);
lean_dec_ref(v_inst_1997_);
lean_dec_ref(v_c_1996_);
lean_dec_ref(v_00_u03b1_1995_);
v_a_2088_ = lean_ctor_get(v___x_2074_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2074_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2074_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2074_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec_ref(v_arg_2019_);
lean_dec_ref(v_fallback_2003_);
lean_dec_ref(v_h_2001_);
lean_dec_ref(v_c_x27_2000_);
lean_dec_ref(v_b_1999_);
lean_dec_ref(v_a_1998_);
lean_dec_ref(v_inst_1997_);
lean_dec_ref(v_c_1996_);
lean_dec_ref(v_00_u03b1_1995_);
v_a_2096_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2031_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2031_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
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
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec_ref(v_fallback_2003_);
lean_dec_ref(v_h_2001_);
lean_dec_ref(v_c_x27_2000_);
lean_dec_ref(v_b_1999_);
lean_dec_ref(v_a_1998_);
lean_dec_ref(v_inst_1997_);
lean_dec_ref(v_c_1996_);
lean_dec_ref(v_00_u03b1_1995_);
v_a_2104_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2014_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2014_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1994_ = stack[0].m_obj;
lean_object* v_00_u03b1_1995_ = stack[1].m_obj;
lean_object* v_c_1996_ = stack[2].m_obj;
lean_object* v_inst_1997_ = stack[3].m_obj;
lean_object* v_a_1998_ = stack[4].m_obj;
lean_object* v_b_1999_ = stack[5].m_obj;
lean_object* v_c_x27_2000_ = stack[6].m_obj;
lean_object* v_h_2001_ = stack[7].m_obj;
lean_object* v_inst_x27_2002_ = stack[8].m_obj;
lean_object* v_fallback_2003_ = stack[9].m_obj;
lean_object* v_a_2004_ = stack[10].m_obj;
lean_object* v_a_2005_ = stack[11].m_obj;
lean_object* v_a_2006_ = stack[12].m_obj;
lean_object* v_a_2007_ = stack[13].m_obj;
lean_object* v_a_2008_ = stack[14].m_obj;
lean_object* v_a_2009_ = stack[15].m_obj;
lean_object* v_a_2010_ = stack[16].m_obj;
lean_object* v_a_2011_ = stack[17].m_obj;
lean_object* v_a_2012_ = stack[18].m_obj;
lean_object* v_res_2112_;
v_res_2112_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(v_f_1994_, v_00_u03b1_1995_, v_c_1996_, v_inst_1997_, v_a_1998_, v_b_1999_, v_c_x27_2000_, v_h_2001_, v_inst_x27_2002_, v_fallback_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_);
stack->m_obj
 = v_res_2112_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_2113_ = _args[0];
lean_object* v_00_u03b1_2114_ = _args[1];
lean_object* v_c_2115_ = _args[2];
lean_object* v_inst_2116_ = _args[3];
lean_object* v_a_2117_ = _args[4];
lean_object* v_b_2118_ = _args[5];
lean_object* v_c_x27_2119_ = _args[6];
lean_object* v_h_2120_ = _args[7];
lean_object* v_inst_x27_2121_ = _args[8];
lean_object* v_fallback_2122_ = _args[9];
lean_object* v_a_2123_ = _args[10];
lean_object* v_a_2124_ = _args[11];
lean_object* v_a_2125_ = _args[12];
lean_object* v_a_2126_ = _args[13];
lean_object* v_a_2127_ = _args[14];
lean_object* v_a_2128_ = _args[15];
lean_object* v_a_2129_ = _args[16];
lean_object* v_a_2130_ = _args[17];
lean_object* v_a_2131_ = _args[18];
lean_object* v_a_2132_ = _args[19];
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(v_f_2113_, v_00_u03b1_2114_, v_c_2115_, v_inst_2116_, v_a_2117_, v_b_2118_, v_c_x27_2119_, v_h_2120_, v_inst_x27_2121_, v_fallback_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
lean_dec(v_a_2131_);
lean_dec_ref(v_a_2130_);
lean_dec(v_a_2129_);
lean_dec_ref(v_a_2128_);
lean_dec(v_a_2127_);
lean_dec_ref(v_a_2126_);
lean_dec(v_a_2125_);
lean_dec_ref(v_a_2124_);
lean_dec(v_a_2123_);
lean_dec_ref(v_f_2113_);
return v_res_2133_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2137_ = lean_box(0);
v___x_2138_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__1));
v___x_2139_ = l_Lean_mkConst(v___x_2138_, v___x_2137_);
return v___x_2139_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5(void){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2143_ = lean_box(0);
v___x_2144_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__4));
v___x_2145_ = l_Lean_mkConst(v___x_2144_, v___x_2143_);
return v___x_2145_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(lean_object* v_f_2146_, lean_object* v_00_u03b1_2147_, lean_object* v_c_2148_, lean_object* v_inst_2149_, lean_object* v_a_2150_, lean_object* v_b_2151_, lean_object* v_fallback_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v___x_2163_; uint8_t v___x_2164_; lean_object* v___x_2165_; lean_object* v___f_2166_; lean_object* v___x_2167_; 
v___x_2163_ = lean_unsigned_to_nat(0u);
v___x_2164_ = 5;
v___x_2165_ = lean_box(v___x_2164_);
lean_inc_ref(v_inst_2149_);
v___f_2166_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2166_, 0, v___x_2165_);
lean_closure_set(v___f_2166_, 1, v_inst_2149_);
lean_closure_set(v___f_2166_, 2, v___x_2163_);
v___x_2167_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2166_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref_known(v___x_2167_, 1);
if (lean_obj_tag(v_a_2168_) == 0)
{
lean_object* v___x_2169_; 
lean_inc(v_a_2161_);
lean_inc_ref(v_a_2160_);
lean_inc(v_a_2159_);
lean_inc_ref(v_a_2158_);
lean_inc(v_a_2157_);
lean_inc_ref(v_a_2156_);
lean_inc(v_a_2155_);
lean_inc_ref(v_a_2154_);
lean_inc(v_a_2153_);
lean_inc_ref(v_inst_2149_);
v___x_2169_ = lean_sym_simp(v_inst_2149_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_a_2170_; 
v_a_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref_known(v___x_2169_, 1);
if (lean_obj_tag(v_a_2170_) == 0)
{
uint8_t v_contextDependent_2171_; lean_object* v___x_2172_; 
v_contextDependent_2171_ = lean_ctor_get_uint8(v_a_2170_, 1);
lean_dec_ref_known(v_a_2170_, 0);
lean_inc_ref(v_inst_2149_);
v___x_2172_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_2146_, v_00_u03b1_2147_, v_c_2148_, v_inst_2149_, v_a_2150_, v_b_2151_, v_inst_2149_, v_fallback_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; uint8_t v___y_2175_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
if (v_contextDependent_2171_ == 0)
{
return v___x_2172_;
}
else
{
if (lean_obj_tag(v_a_2173_) == 0)
{
uint8_t v_contextDependent_2185_; 
v_contextDependent_2185_ = lean_ctor_get_uint8(v_a_2173_, 1);
v___y_2175_ = v_contextDependent_2185_;
goto v___jp_2174_;
}
else
{
uint8_t v_contextDependent_2186_; 
v_contextDependent_2186_ = lean_ctor_get_uint8(v_a_2173_, sizeof(void*)*2 + 1);
v___y_2175_ = v_contextDependent_2186_;
goto v___jp_2174_;
}
}
v___jp_2174_:
{
if (v___y_2175_ == 0)
{
lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2183_; 
lean_inc(v_a_2173_);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2183_ == 0)
{
lean_object* v_unused_2184_; 
v_unused_2184_ = lean_ctor_get(v___x_2172_, 0);
lean_dec(v_unused_2184_);
v___x_2177_ = v___x_2172_;
v_isShared_2178_ = v_isSharedCheck_2183_;
goto v_resetjp_2176_;
}
else
{
lean_dec(v___x_2172_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2183_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2179_; lean_object* v___x_2181_; 
v___x_2179_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2173_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2179_);
v___x_2181_ = v___x_2177_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
else
{
return v___x_2172_;
}
}
}
else
{
return v___x_2172_;
}
}
else
{
lean_object* v_e_x27_2187_; uint8_t v_contextDependent_2188_; lean_object* v___x_2189_; 
v_e_x27_2187_ = lean_ctor_get(v_a_2170_, 0);
lean_inc_ref(v_e_x27_2187_);
v_contextDependent_2188_ = lean_ctor_get_uint8(v_a_2170_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2170_, 2);
v___x_2189_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_2146_, v_00_u03b1_2147_, v_c_2148_, v_inst_2149_, v_a_2150_, v_b_2151_, v_e_x27_2187_, v_fallback_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; uint8_t v___y_2192_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
if (v_contextDependent_2188_ == 0)
{
return v___x_2189_;
}
else
{
if (lean_obj_tag(v_a_2190_) == 0)
{
uint8_t v_contextDependent_2202_; 
v_contextDependent_2202_ = lean_ctor_get_uint8(v_a_2190_, 1);
v___y_2192_ = v_contextDependent_2202_;
goto v___jp_2191_;
}
else
{
uint8_t v_contextDependent_2203_; 
v_contextDependent_2203_ = lean_ctor_get_uint8(v_a_2190_, sizeof(void*)*2 + 1);
v___y_2192_ = v_contextDependent_2203_;
goto v___jp_2191_;
}
}
v___jp_2191_:
{
if (v___y_2192_ == 0)
{
lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2200_; 
lean_inc(v_a_2190_);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2200_ == 0)
{
lean_object* v_unused_2201_; 
v_unused_2201_ = lean_ctor_get(v___x_2189_, 0);
lean_dec(v_unused_2201_);
v___x_2194_ = v___x_2189_;
v_isShared_2195_ = v_isSharedCheck_2200_;
goto v_resetjp_2193_;
}
else
{
lean_dec(v___x_2189_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2200_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2196_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2190_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v___x_2196_);
v___x_2198_ = v___x_2194_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
else
{
return v___x_2189_;
}
}
}
else
{
return v___x_2189_;
}
}
}
else
{
lean_dec_ref(v_fallback_2152_);
lean_dec_ref(v_b_2151_);
lean_dec_ref(v_a_2150_);
lean_dec_ref(v_inst_2149_);
lean_dec_ref(v_c_2148_);
lean_dec_ref(v_00_u03b1_2147_);
return v___x_2169_;
}
}
else
{
lean_object* v_val_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v_val_2204_ = lean_ctor_get(v_a_2168_, 0);
lean_inc(v_val_2204_);
lean_dec_ref_known(v_a_2168_, 1);
v___x_2205_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2);
lean_inc_ref(v_inst_2149_);
lean_inc_ref(v_c_2148_);
v___x_2206_ = l_Lean_mkAppB(v___x_2205_, v_c_2148_, v_inst_2149_);
v___x_2207_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2204_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc_n(v_a_2208_, 3);
lean_dec_ref_known(v___x_2207_, 1);
v___x_2209_ = lean_unsigned_to_nat(1u);
v___x_2210_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8);
v___x_2211_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10);
v___x_2212_ = l_Lean_mkAppB(v___x_2210_, v___x_2211_, v_a_2208_);
lean_inc(v_a_2161_);
lean_inc_ref(v_a_2160_);
lean_inc(v_a_2159_);
lean_inc_ref(v_a_2158_);
lean_inc(v_a_2157_);
lean_inc_ref(v_a_2156_);
lean_inc(v_a_2155_);
lean_inc_ref(v_a_2154_);
lean_inc(v_a_2153_);
v___x_2213_ = lean_sym_simp(v_a_2208_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; uint8_t v___x_2215_; lean_object* v_e_x27_2217_; lean_object* v_proof_2218_; uint8_t v_contextDependent_2219_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_a_2214_);
lean_dec_ref_known(v___x_2213_, 1);
v___x_2215_ = 0;
if (lean_obj_tag(v_a_2214_) == 0)
{
uint8_t v_contextDependent_2310_; 
lean_dec_ref(v___x_2206_);
v_contextDependent_2310_ = lean_ctor_get_uint8(v_a_2214_, 1);
lean_dec_ref_known(v_a_2214_, 0);
v_e_x27_2217_ = v_a_2208_;
v_proof_2218_ = v___x_2212_;
v_contextDependent_2219_ = v_contextDependent_2310_;
goto v___jp_2216_;
}
else
{
lean_object* v_e_x27_2311_; lean_object* v_proof_2312_; uint8_t v_contextDependent_2313_; lean_object* v___x_2314_; 
v_e_x27_2311_ = lean_ctor_get(v_a_2214_, 0);
lean_inc_ref_n(v_e_x27_2311_, 2);
v_proof_2312_ = lean_ctor_get(v_a_2214_, 1);
lean_inc_ref(v_proof_2312_);
v_contextDependent_2313_ = lean_ctor_get_uint8(v_a_2214_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2214_, 2);
v___x_2314_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___x_2206_, v_a_2208_, v___x_2212_, v_e_x27_2311_, v_proof_2312_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref_known(v___x_2314_, 1);
v_e_x27_2217_ = v_e_x27_2311_;
v_proof_2218_ = v_a_2315_;
v_contextDependent_2219_ = v_contextDependent_2313_;
goto v___jp_2216_;
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec_ref(v_e_x27_2311_);
lean_dec_ref(v_fallback_2152_);
lean_dec_ref(v_b_2151_);
lean_dec_ref(v_a_2150_);
lean_dec_ref(v_inst_2149_);
lean_dec_ref(v_c_2148_);
lean_dec_ref(v_00_u03b1_2147_);
v_a_2316_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2314_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2314_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
v___jp_2216_:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_x27_2217_, v_a_2159_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; uint8_t v___x_2224_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
lean_dec_ref_known(v___x_2220_, 1);
v___x_2222_ = l_Lean_Expr_cleanupAnnotations(v_a_2221_);
v___x_2223_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_2224_ = l_Lean_Expr_isConstOf(v___x_2222_, v___x_2223_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; uint8_t v___x_2226_; 
v___x_2225_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_2226_ = l_Lean_Expr_isConstOf(v___x_2222_, v___x_2225_);
lean_dec_ref(v___x_2222_);
if (v___x_2226_ == 0)
{
lean_object* v___x_2227_; 
lean_dec_ref(v_proof_2218_);
lean_dec_ref(v_b_2151_);
lean_dec_ref(v_a_2150_);
lean_dec_ref(v_inst_2149_);
lean_dec_ref(v_c_2148_);
lean_dec_ref(v_00_u03b1_2147_);
lean_inc(v_a_2161_);
lean_inc_ref(v_a_2160_);
lean_inc(v_a_2159_);
lean_inc_ref(v_a_2158_);
lean_inc(v_a_2157_);
lean_inc_ref(v_a_2156_);
lean_inc(v_a_2155_);
lean_inc_ref(v_a_2154_);
lean_inc(v_a_2153_);
v___x_2227_ = lean_apply_10(v_fallback_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, lean_box(0));
return v___x_2227_;
}
else
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
lean_dec_ref(v_fallback_2152_);
v___x_2228_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2);
lean_inc_ref(v_inst_2149_);
lean_inc_ref(v_c_2148_);
v___x_2229_ = l_Lean_mkApp3(v___x_2228_, v_c_2148_, v_inst_2149_, v_proof_2218_);
v___x_2230_ = l_Lean_Meta_Sym_shareCommon(v___x_2229_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc_n(v_a_2231_, 2);
lean_dec_ref_known(v___x_2230_, 1);
v___x_2232_ = lean_mk_empty_array_with_capacity(v___x_2209_);
v___x_2233_ = lean_array_push(v___x_2232_, v_a_2231_);
lean_inc_ref(v_a_2150_);
v___x_2234_ = l_Lean_Expr_betaRev(v_a_2150_, v___x_2233_, v___x_2215_, v___x_2215_);
lean_dec_ref(v___x_2233_);
v___x_2235_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2234_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2248_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2238_ = v___x_2235_;
v_isShared_2239_ = v_isSharedCheck_2248_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2248_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2246_; 
v___x_2240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1));
v___x_2241_ = l_Lean_Expr_constLevels_x21(v_f_2146_);
v___x_2242_ = l_Lean_mkConst(v___x_2240_, v___x_2241_);
v___x_2243_ = l_Lean_mkApp6(v___x_2242_, v_00_u03b1_2147_, v_c_2148_, v_inst_2149_, v_a_2150_, v_b_2151_, v_a_2231_);
v___x_2244_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2244_, 0, v_a_2236_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
lean_ctor_set_uint8(v___x_2244_, sizeof(void*)*2, v___x_2215_);
lean_ctor_set_uint8(v___x_2244_, sizeof(void*)*2 + 1, v_contextDependent_2219_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2244_);
v___x_2246_ = v___x_2238_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2244_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_dec(v_a_2231_);
lean_dec_ref(v_b_2151_);
lean_dec_ref(v_a_2150_);
lean_dec_ref(v_inst_2149_);
lean_dec_ref(v_c_2148_);
lean_dec_ref(v_00_u03b1_2147_);
v_a_2249_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2235_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2235_);
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
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec_ref(v_b_2151_);
lean_dec_ref(v_a_2150_);
lean_dec_ref(v_inst_2149_);
lean_dec_ref(v_c_2148_);
lean_dec_ref(v_00_u03b1_2147_);
v_a_2257_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2230_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2230_);
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
else
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_dec_ref(v___x_2222_);
lean_dec_ref(v_fallback_2152_);
v___x_2265_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5);
lean_inc_ref(v_inst_2149_);
lean_inc_ref(v_c_2148_);
v___x_2266_ = l_Lean_mkApp3(v___x_2265_, v_c_2148_, v_inst_2149_, v_proof_2218_);
v___x_2267_ = l_Lean_Meta_Sym_shareCommon(v___x_2266_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc_n(v_a_2268_, 2);
lean_dec_ref_known(v___x_2267_, 1);
v___x_2269_ = lean_mk_empty_array_with_capacity(v___x_2209_);
v___x_2270_ = lean_array_push(v___x_2269_, v_a_2268_);
lean_inc_ref(v_b_2151_);
v___x_2271_ = l_Lean_Expr_betaRev(v_b_2151_, v___x_2270_, v___x_2215_, v___x_2215_);
lean_dec_ref(v___x_2270_);
v___x_2272_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2271_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2285_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2275_ = v___x_2272_;
v_isShared_2276_ = v_isSharedCheck_2285_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2272_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2285_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2277_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3));
v___x_2278_ = l_Lean_Expr_constLevels_x21(v_f_2146_);
v___x_2279_ = l_Lean_mkConst(v___x_2277_, v___x_2278_);
v___x_2280_ = l_Lean_mkApp6(v___x_2279_, v_00_u03b1_2147_, v_c_2148_, v_inst_2149_, v_a_2150_, v_b_2151_, v_a_2268_);
v___x_2281_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2281_, 0, v_a_2273_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
lean_ctor_set_uint8(v___x_2281_, sizeof(void*)*2, v___x_2215_);
lean_ctor_set_uint8(v___x_2281_, sizeof(void*)*2 + 1, v_contextDependent_2219_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 0, v___x_2281_);
v___x_2283_ = v___x_2275_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___x_2281_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec(v_a_2268_);
lean_dec_ref(v_b_2151_);
lean_dec_ref(v_a_2150_);
lean_dec_ref(v_inst_2149_);
lean_dec_ref(v_c_2148_);
lean_dec_ref(v_00_u03b1_2147_);
v_a_2286_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2272_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2272_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec_ref(v_b_2151_);
lean_dec_ref(v_a_2150_);
lean_dec_ref(v_inst_2149_);
lean_dec_ref(v_c_2148_);
lean_dec_ref(v_00_u03b1_2147_);
v_a_2294_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2267_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2267_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_dec_ref(v_proof_2218_);
lean_dec_ref(v_fallback_2152_);
lean_dec_ref(v_b_2151_);
lean_dec_ref(v_a_2150_);
lean_dec_ref(v_inst_2149_);
lean_dec_ref(v_c_2148_);
lean_dec_ref(v_00_u03b1_2147_);
v_a_2302_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2220_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2220_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2212_);
lean_dec(v_a_2208_);
lean_dec_ref(v___x_2206_);
lean_dec_ref(v_fallback_2152_);
lean_dec_ref(v_b_2151_);
lean_dec_ref(v_a_2150_);
lean_dec_ref(v_inst_2149_);
lean_dec_ref(v_c_2148_);
lean_dec_ref(v_00_u03b1_2147_);
return v___x_2213_;
}
}
else
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec_ref(v___x_2206_);
lean_dec_ref(v_fallback_2152_);
lean_dec_ref(v_b_2151_);
lean_dec_ref(v_a_2150_);
lean_dec_ref(v_inst_2149_);
lean_dec_ref(v_c_2148_);
lean_dec_ref(v_00_u03b1_2147_);
v_a_2324_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2207_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2207_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_a_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec_ref(v_fallback_2152_);
lean_dec_ref(v_b_2151_);
lean_dec_ref(v_a_2150_);
lean_dec_ref(v_inst_2149_);
lean_dec_ref(v_c_2148_);
lean_dec_ref(v_00_u03b1_2147_);
v_a_2332_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2167_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2167_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2146_ = stack[0].m_obj;
lean_object* v_00_u03b1_2147_ = stack[1].m_obj;
lean_object* v_c_2148_ = stack[2].m_obj;
lean_object* v_inst_2149_ = stack[3].m_obj;
lean_object* v_a_2150_ = stack[4].m_obj;
lean_object* v_b_2151_ = stack[5].m_obj;
lean_object* v_fallback_2152_ = stack[6].m_obj;
lean_object* v_a_2153_ = stack[7].m_obj;
lean_object* v_a_2154_ = stack[8].m_obj;
lean_object* v_a_2155_ = stack[9].m_obj;
lean_object* v_a_2156_ = stack[10].m_obj;
lean_object* v_a_2157_ = stack[11].m_obj;
lean_object* v_a_2158_ = stack[12].m_obj;
lean_object* v_a_2159_ = stack[13].m_obj;
lean_object* v_a_2160_ = stack[14].m_obj;
lean_object* v_a_2161_ = stack[15].m_obj;
lean_object* v_res_2340_;
v_res_2340_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v_f_2146_, v_00_u03b1_2147_, v_c_2148_, v_inst_2149_, v_a_2150_, v_b_2151_, v_fallback_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
stack->m_obj
 = v_res_2340_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___boxed(lean_object** _args){
lean_object* v_f_2341_ = _args[0];
lean_object* v_00_u03b1_2342_ = _args[1];
lean_object* v_c_2343_ = _args[2];
lean_object* v_inst_2344_ = _args[3];
lean_object* v_a_2345_ = _args[4];
lean_object* v_b_2346_ = _args[5];
lean_object* v_fallback_2347_ = _args[6];
lean_object* v_a_2348_ = _args[7];
lean_object* v_a_2349_ = _args[8];
lean_object* v_a_2350_ = _args[9];
lean_object* v_a_2351_ = _args[10];
lean_object* v_a_2352_ = _args[11];
lean_object* v_a_2353_ = _args[12];
lean_object* v_a_2354_ = _args[13];
lean_object* v_a_2355_ = _args[14];
lean_object* v_a_2356_ = _args[15];
lean_object* v_a_2357_ = _args[16];
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v_f_2341_, v_00_u03b1_2342_, v_c_2343_, v_inst_2344_, v_a_2345_, v_b_2346_, v_fallback_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_);
lean_dec(v_a_2356_);
lean_dec_ref(v_a_2355_);
lean_dec(v_a_2354_);
lean_dec_ref(v_a_2353_);
lean_dec(v_a_2352_);
lean_dec_ref(v_a_2351_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
lean_dec(v_a_2348_);
lean_dec_ref(v_f_2341_);
return v_res_2358_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr(lean_object* v_f_2359_, lean_object* v_00_u03b1_2360_, lean_object* v_c_2361_, lean_object* v_inst_2362_, lean_object* v_a_2363_, lean_object* v_b_2364_, lean_object* v_c_x27_2365_, lean_object* v_h_2366_, lean_object* v_inst_x27_2367_, lean_object* v_fallback_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v___x_2379_; uint8_t v___x_2380_; lean_object* v___x_2381_; lean_object* v___f_2382_; lean_object* v___x_2383_; 
v___x_2379_ = lean_unsigned_to_nat(0u);
v___x_2380_ = 5;
v___x_2381_ = lean_box(v___x_2380_);
lean_inc_ref(v_inst_x27_2367_);
v___f_2382_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0___boxed), 8, 3);
lean_closure_set(v___f_2382_, 0, v___x_2381_);
lean_closure_set(v___f_2382_, 1, v_inst_x27_2367_);
lean_closure_set(v___f_2382_, 2, v___x_2379_);
v___x_2383_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2382_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref_known(v___x_2383_, 1);
if (lean_obj_tag(v_a_2384_) == 0)
{
lean_object* v___x_2385_; 
lean_inc(v_a_2377_);
lean_inc_ref(v_a_2376_);
lean_inc(v_a_2375_);
lean_inc_ref(v_a_2374_);
lean_inc(v_a_2373_);
lean_inc_ref(v_a_2372_);
lean_inc(v_a_2371_);
lean_inc_ref(v_a_2370_);
lean_inc(v_a_2369_);
lean_inc_ref(v_inst_x27_2367_);
v___x_2385_ = lean_sym_simp(v_inst_x27_2367_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_a_2386_);
lean_dec_ref_known(v___x_2385_, 1);
if (lean_obj_tag(v_a_2386_) == 0)
{
uint8_t v_contextDependent_2387_; lean_object* v___x_2388_; 
v_contextDependent_2387_ = lean_ctor_get_uint8(v_a_2386_, 1);
lean_dec_ref_known(v_a_2386_, 0);
v___x_2388_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(v_f_2359_, v_00_u03b1_2360_, v_c_2361_, v_inst_2362_, v_a_2363_, v_b_2364_, v_c_x27_2365_, v_h_2366_, v_inst_x27_2367_, v_fallback_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; uint8_t v___y_2391_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
if (v_contextDependent_2387_ == 0)
{
return v___x_2388_;
}
else
{
if (lean_obj_tag(v_a_2389_) == 0)
{
uint8_t v_contextDependent_2401_; 
v_contextDependent_2401_ = lean_ctor_get_uint8(v_a_2389_, 1);
v___y_2391_ = v_contextDependent_2401_;
goto v___jp_2390_;
}
else
{
uint8_t v_contextDependent_2402_; 
v_contextDependent_2402_ = lean_ctor_get_uint8(v_a_2389_, sizeof(void*)*2 + 1);
v___y_2391_ = v_contextDependent_2402_;
goto v___jp_2390_;
}
}
v___jp_2390_:
{
if (v___y_2391_ == 0)
{
lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2399_; 
lean_inc(v_a_2389_);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2399_ == 0)
{
lean_object* v_unused_2400_; 
v_unused_2400_ = lean_ctor_get(v___x_2388_, 0);
lean_dec(v_unused_2400_);
v___x_2393_ = v___x_2388_;
v_isShared_2394_ = v_isSharedCheck_2399_;
goto v_resetjp_2392_;
}
else
{
lean_dec(v___x_2388_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2399_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; lean_object* v___x_2397_; 
v___x_2395_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2389_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v___x_2395_);
v___x_2397_ = v___x_2393_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
else
{
return v___x_2388_;
}
}
}
else
{
return v___x_2388_;
}
}
else
{
lean_object* v_e_x27_2403_; uint8_t v_contextDependent_2404_; lean_object* v___x_2405_; 
lean_dec_ref(v_inst_x27_2367_);
v_e_x27_2403_ = lean_ctor_get(v_a_2386_, 0);
lean_inc_ref(v_e_x27_2403_);
v_contextDependent_2404_ = lean_ctor_get_uint8(v_a_2386_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2386_, 2);
v___x_2405_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(v_f_2359_, v_00_u03b1_2360_, v_c_2361_, v_inst_2362_, v_a_2363_, v_b_2364_, v_c_x27_2365_, v_h_2366_, v_e_x27_2403_, v_fallback_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; uint8_t v___y_2408_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
if (v_contextDependent_2404_ == 0)
{
return v___x_2405_;
}
else
{
if (lean_obj_tag(v_a_2406_) == 0)
{
uint8_t v_contextDependent_2418_; 
v_contextDependent_2418_ = lean_ctor_get_uint8(v_a_2406_, 1);
v___y_2408_ = v_contextDependent_2418_;
goto v___jp_2407_;
}
else
{
uint8_t v_contextDependent_2419_; 
v_contextDependent_2419_ = lean_ctor_get_uint8(v_a_2406_, sizeof(void*)*2 + 1);
v___y_2408_ = v_contextDependent_2419_;
goto v___jp_2407_;
}
}
v___jp_2407_:
{
if (v___y_2408_ == 0)
{
lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2416_; 
lean_inc(v_a_2406_);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2416_ == 0)
{
lean_object* v_unused_2417_; 
v_unused_2417_ = lean_ctor_get(v___x_2405_, 0);
lean_dec(v_unused_2417_);
v___x_2410_ = v___x_2405_;
v_isShared_2411_ = v_isSharedCheck_2416_;
goto v_resetjp_2409_;
}
else
{
lean_dec(v___x_2405_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2416_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2412_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2406_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v___x_2412_);
v___x_2414_ = v___x_2410_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
else
{
return v___x_2405_;
}
}
}
else
{
return v___x_2405_;
}
}
}
else
{
lean_dec_ref(v_fallback_2368_);
lean_dec_ref(v_inst_x27_2367_);
lean_dec_ref(v_h_2366_);
lean_dec_ref(v_c_x27_2365_);
lean_dec_ref(v_b_2364_);
lean_dec_ref(v_a_2363_);
lean_dec_ref(v_inst_2362_);
lean_dec_ref(v_c_2361_);
lean_dec_ref(v_00_u03b1_2360_);
return v___x_2385_;
}
}
else
{
lean_object* v_val_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v_val_2420_ = lean_ctor_get(v_a_2384_, 0);
lean_inc(v_val_2420_);
lean_dec_ref_known(v_a_2384_, 1);
v___x_2421_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2);
lean_inc_ref(v_inst_x27_2367_);
lean_inc_ref(v_c_x27_2365_);
v___x_2422_ = l_Lean_mkAppB(v___x_2421_, v_c_x27_2365_, v_inst_x27_2367_);
v___x_2423_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2420_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc_n(v_a_2424_, 3);
lean_dec_ref_known(v___x_2423_, 1);
v___x_2425_ = lean_unsigned_to_nat(1u);
v___x_2426_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8);
v___x_2427_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10);
v___x_2428_ = l_Lean_mkAppB(v___x_2426_, v___x_2427_, v_a_2424_);
lean_inc(v_a_2377_);
lean_inc_ref(v_a_2376_);
lean_inc(v_a_2375_);
lean_inc_ref(v_a_2374_);
lean_inc(v_a_2373_);
lean_inc_ref(v_a_2372_);
lean_inc(v_a_2371_);
lean_inc_ref(v_a_2370_);
lean_inc(v_a_2369_);
v___x_2429_ = lean_sym_simp(v_a_2424_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; uint8_t v___x_2431_; lean_object* v_e_x27_2433_; lean_object* v_proof_2434_; uint8_t v_contextDependent_2435_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2429_, 1);
v___x_2431_ = 0;
if (lean_obj_tag(v_a_2430_) == 0)
{
uint8_t v_contextDependent_2530_; 
lean_dec_ref(v___x_2422_);
v_contextDependent_2530_ = lean_ctor_get_uint8(v_a_2430_, 1);
lean_dec_ref_known(v_a_2430_, 0);
v_e_x27_2433_ = v_a_2424_;
v_proof_2434_ = v___x_2428_;
v_contextDependent_2435_ = v_contextDependent_2530_;
goto v___jp_2432_;
}
else
{
lean_object* v_e_x27_2531_; lean_object* v_proof_2532_; uint8_t v_contextDependent_2533_; lean_object* v___x_2534_; 
v_e_x27_2531_ = lean_ctor_get(v_a_2430_, 0);
lean_inc_ref_n(v_e_x27_2531_, 2);
v_proof_2532_ = lean_ctor_get(v_a_2430_, 1);
lean_inc_ref(v_proof_2532_);
v_contextDependent_2533_ = lean_ctor_get_uint8(v_a_2430_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2430_, 2);
v___x_2534_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___x_2422_, v_a_2424_, v___x_2428_, v_e_x27_2531_, v_proof_2532_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_a_2535_);
lean_dec_ref_known(v___x_2534_, 1);
v_e_x27_2433_ = v_e_x27_2531_;
v_proof_2434_ = v_a_2535_;
v_contextDependent_2435_ = v_contextDependent_2533_;
goto v___jp_2432_;
}
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec_ref(v_e_x27_2531_);
lean_dec_ref(v_fallback_2368_);
lean_dec_ref(v_inst_x27_2367_);
lean_dec_ref(v_h_2366_);
lean_dec_ref(v_c_x27_2365_);
lean_dec_ref(v_b_2364_);
lean_dec_ref(v_a_2363_);
lean_dec_ref(v_inst_2362_);
lean_dec_ref(v_c_2361_);
lean_dec_ref(v_00_u03b1_2360_);
v_a_2536_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2534_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2534_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
v___jp_2432_:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_x27_2433_, v_a_2375_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; 
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
lean_inc(v_a_2437_);
lean_dec_ref_known(v___x_2436_, 1);
v___x_2438_ = l_Lean_Expr_cleanupAnnotations(v_a_2437_);
v___x_2439_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_2440_ = l_Lean_Expr_isConstOf(v___x_2438_, v___x_2439_);
if (v___x_2440_ == 0)
{
lean_object* v___x_2441_; uint8_t v___x_2442_; 
v___x_2441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_2442_ = l_Lean_Expr_isConstOf(v___x_2438_, v___x_2441_);
lean_dec_ref(v___x_2438_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; 
lean_dec_ref(v_proof_2434_);
lean_dec_ref(v_inst_x27_2367_);
lean_dec_ref(v_h_2366_);
lean_dec_ref(v_c_x27_2365_);
lean_dec_ref(v_b_2364_);
lean_dec_ref(v_a_2363_);
lean_dec_ref(v_inst_2362_);
lean_dec_ref(v_c_2361_);
lean_dec_ref(v_00_u03b1_2360_);
lean_inc(v_a_2377_);
lean_inc_ref(v_a_2376_);
lean_inc(v_a_2375_);
lean_inc_ref(v_a_2374_);
lean_inc(v_a_2373_);
lean_inc_ref(v_a_2372_);
lean_inc(v_a_2371_);
lean_inc_ref(v_a_2370_);
lean_inc(v_a_2369_);
v___x_2443_ = lean_apply_10(v_fallback_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, lean_box(0));
return v___x_2443_;
}
else
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
lean_dec_ref(v_fallback_2368_);
v___x_2444_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__2);
lean_inc_ref(v_c_x27_2365_);
v___x_2445_ = l_Lean_mkApp3(v___x_2444_, v_c_x27_2365_, v_inst_x27_2367_, v_proof_2434_);
v___x_2446_ = l_Lean_Meta_Sym_shareCommon(v___x_2445_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc_n(v_a_2447_, 2);
lean_dec_ref_known(v___x_2446_, 1);
v___x_2448_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2);
lean_inc_ref(v_h_2366_);
lean_inc_ref(v_c_x27_2365_);
lean_inc_ref(v_c_2361_);
v___x_2449_ = l_Lean_mkApp4(v___x_2448_, v_c_2361_, v_c_x27_2365_, v_h_2366_, v_a_2447_);
v___x_2450_ = lean_mk_empty_array_with_capacity(v___x_2425_);
v___x_2451_ = lean_array_push(v___x_2450_, v___x_2449_);
lean_inc_ref(v_a_2363_);
v___x_2452_ = l_Lean_Expr_betaRev(v_a_2363_, v___x_2451_, v___x_2431_, v___x_2431_);
lean_dec_ref(v___x_2451_);
v___x_2453_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2452_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2466_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2456_ = v___x_2453_;
v_isShared_2457_ = v_isSharedCheck_2466_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2453_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2466_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2464_; 
v___x_2458_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4));
v___x_2459_ = l_Lean_Expr_constLevels_x21(v_f_2359_);
v___x_2460_ = l_Lean_mkConst(v___x_2458_, v___x_2459_);
v___x_2461_ = l_Lean_mkApp8(v___x_2460_, v_00_u03b1_2360_, v_c_2361_, v_inst_2362_, v_a_2363_, v_b_2364_, v_c_x27_2365_, v_h_2366_, v_a_2447_);
v___x_2462_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2462_, 0, v_a_2454_);
lean_ctor_set(v___x_2462_, 1, v___x_2461_);
lean_ctor_set_uint8(v___x_2462_, sizeof(void*)*2, v___x_2431_);
lean_ctor_set_uint8(v___x_2462_, sizeof(void*)*2 + 1, v_contextDependent_2435_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v___x_2462_);
v___x_2464_ = v___x_2456_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec(v_a_2447_);
lean_dec_ref(v_h_2366_);
lean_dec_ref(v_c_x27_2365_);
lean_dec_ref(v_b_2364_);
lean_dec_ref(v_a_2363_);
lean_dec_ref(v_inst_2362_);
lean_dec_ref(v_c_2361_);
lean_dec_ref(v_00_u03b1_2360_);
v_a_2467_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2453_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2453_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec_ref(v_h_2366_);
lean_dec_ref(v_c_x27_2365_);
lean_dec_ref(v_b_2364_);
lean_dec_ref(v_a_2363_);
lean_dec_ref(v_inst_2362_);
lean_dec_ref(v_c_2361_);
lean_dec_ref(v_00_u03b1_2360_);
v_a_2475_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2446_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2446_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
}
else
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
lean_dec_ref(v___x_2438_);
lean_dec_ref(v_fallback_2368_);
v___x_2483_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___closed__5);
lean_inc_ref(v_c_x27_2365_);
v___x_2484_ = l_Lean_mkApp3(v___x_2483_, v_c_x27_2365_, v_inst_x27_2367_, v_proof_2434_);
v___x_2485_ = l_Lean_Meta_Sym_shareCommon(v___x_2484_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc_n(v_a_2486_, 2);
lean_dec_ref_known(v___x_2485_, 1);
v___x_2487_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7);
lean_inc_ref(v_h_2366_);
lean_inc_ref(v_c_x27_2365_);
lean_inc_ref(v_c_2361_);
v___x_2488_ = l_Lean_mkApp4(v___x_2487_, v_c_2361_, v_c_x27_2365_, v_h_2366_, v_a_2486_);
v___x_2489_ = lean_mk_empty_array_with_capacity(v___x_2425_);
v___x_2490_ = lean_array_push(v___x_2489_, v___x_2488_);
lean_inc_ref(v_b_2364_);
v___x_2491_ = l_Lean_Expr_betaRev(v_b_2364_, v___x_2490_, v___x_2431_, v___x_2431_);
lean_dec_ref(v___x_2490_);
v___x_2492_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2491_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2505_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2495_ = v___x_2492_;
v_isShared_2496_ = v_isSharedCheck_2505_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_a_2493_);
lean_dec(v___x_2492_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2505_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2503_; 
v___x_2497_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9));
v___x_2498_ = l_Lean_Expr_constLevels_x21(v_f_2359_);
v___x_2499_ = l_Lean_mkConst(v___x_2497_, v___x_2498_);
v___x_2500_ = l_Lean_mkApp8(v___x_2499_, v_00_u03b1_2360_, v_c_2361_, v_inst_2362_, v_a_2363_, v_b_2364_, v_c_x27_2365_, v_h_2366_, v_a_2486_);
v___x_2501_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2501_, 0, v_a_2493_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
lean_ctor_set_uint8(v___x_2501_, sizeof(void*)*2, v___x_2431_);
lean_ctor_set_uint8(v___x_2501_, sizeof(void*)*2 + 1, v_contextDependent_2435_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 0, v___x_2501_);
v___x_2503_ = v___x_2495_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2501_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v_a_2486_);
lean_dec_ref(v_h_2366_);
lean_dec_ref(v_c_x27_2365_);
lean_dec_ref(v_b_2364_);
lean_dec_ref(v_a_2363_);
lean_dec_ref(v_inst_2362_);
lean_dec_ref(v_c_2361_);
lean_dec_ref(v_00_u03b1_2360_);
v_a_2506_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2492_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2492_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec_ref(v_h_2366_);
lean_dec_ref(v_c_x27_2365_);
lean_dec_ref(v_b_2364_);
lean_dec_ref(v_a_2363_);
lean_dec_ref(v_inst_2362_);
lean_dec_ref(v_c_2361_);
lean_dec_ref(v_00_u03b1_2360_);
v_a_2514_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2485_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2485_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_dec_ref(v_proof_2434_);
lean_dec_ref(v_fallback_2368_);
lean_dec_ref(v_inst_x27_2367_);
lean_dec_ref(v_h_2366_);
lean_dec_ref(v_c_x27_2365_);
lean_dec_ref(v_b_2364_);
lean_dec_ref(v_a_2363_);
lean_dec_ref(v_inst_2362_);
lean_dec_ref(v_c_2361_);
lean_dec_ref(v_00_u03b1_2360_);
v_a_2522_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2436_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2436_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_2428_);
lean_dec(v_a_2424_);
lean_dec_ref(v___x_2422_);
lean_dec_ref(v_fallback_2368_);
lean_dec_ref(v_inst_x27_2367_);
lean_dec_ref(v_h_2366_);
lean_dec_ref(v_c_x27_2365_);
lean_dec_ref(v_b_2364_);
lean_dec_ref(v_a_2363_);
lean_dec_ref(v_inst_2362_);
lean_dec_ref(v_c_2361_);
lean_dec_ref(v_00_u03b1_2360_);
return v___x_2429_;
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec_ref(v___x_2422_);
lean_dec_ref(v_fallback_2368_);
lean_dec_ref(v_inst_x27_2367_);
lean_dec_ref(v_h_2366_);
lean_dec_ref(v_c_x27_2365_);
lean_dec_ref(v_b_2364_);
lean_dec_ref(v_a_2363_);
lean_dec_ref(v_inst_2362_);
lean_dec_ref(v_c_2361_);
lean_dec_ref(v_00_u03b1_2360_);
v_a_2544_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2423_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2423_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_dec_ref(v_fallback_2368_);
lean_dec_ref(v_inst_x27_2367_);
lean_dec_ref(v_h_2366_);
lean_dec_ref(v_c_x27_2365_);
lean_dec_ref(v_b_2364_);
lean_dec_ref(v_a_2363_);
lean_dec_ref(v_inst_2362_);
lean_dec_ref(v_c_2361_);
lean_dec_ref(v_00_u03b1_2360_);
v_a_2552_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2383_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2383_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2359_ = stack[0].m_obj;
lean_object* v_00_u03b1_2360_ = stack[1].m_obj;
lean_object* v_c_2361_ = stack[2].m_obj;
lean_object* v_inst_2362_ = stack[3].m_obj;
lean_object* v_a_2363_ = stack[4].m_obj;
lean_object* v_b_2364_ = stack[5].m_obj;
lean_object* v_c_x27_2365_ = stack[6].m_obj;
lean_object* v_h_2366_ = stack[7].m_obj;
lean_object* v_inst_x27_2367_ = stack[8].m_obj;
lean_object* v_fallback_2368_ = stack[9].m_obj;
lean_object* v_a_2369_ = stack[10].m_obj;
lean_object* v_a_2370_ = stack[11].m_obj;
lean_object* v_a_2371_ = stack[12].m_obj;
lean_object* v_a_2372_ = stack[13].m_obj;
lean_object* v_a_2373_ = stack[14].m_obj;
lean_object* v_a_2374_ = stack[15].m_obj;
lean_object* v_a_2375_ = stack[16].m_obj;
lean_object* v_a_2376_ = stack[17].m_obj;
lean_object* v_a_2377_ = stack[18].m_obj;
lean_object* v_res_2560_;
v_res_2560_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr(v_f_2359_, v_00_u03b1_2360_, v_c_2361_, v_inst_2362_, v_a_2363_, v_b_2364_, v_c_x27_2365_, v_h_2366_, v_inst_x27_2367_, v_fallback_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
stack->m_obj
 = v_res_2560_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr___boxed(lean_object** _args){
lean_object* v_f_2561_ = _args[0];
lean_object* v_00_u03b1_2562_ = _args[1];
lean_object* v_c_2563_ = _args[2];
lean_object* v_inst_2564_ = _args[3];
lean_object* v_a_2565_ = _args[4];
lean_object* v_b_2566_ = _args[5];
lean_object* v_c_x27_2567_ = _args[6];
lean_object* v_h_2568_ = _args[7];
lean_object* v_inst_x27_2569_ = _args[8];
lean_object* v_fallback_2570_ = _args[9];
lean_object* v_a_2571_ = _args[10];
lean_object* v_a_2572_ = _args[11];
lean_object* v_a_2573_ = _args[12];
lean_object* v_a_2574_ = _args[13];
lean_object* v_a_2575_ = _args[14];
lean_object* v_a_2576_ = _args[15];
lean_object* v_a_2577_ = _args[16];
lean_object* v_a_2578_ = _args[17];
lean_object* v_a_2579_ = _args[18];
lean_object* v_a_2580_ = _args[19];
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr(v_f_2561_, v_00_u03b1_2562_, v_c_2563_, v_inst_2564_, v_a_2565_, v_b_2566_, v_c_x27_2567_, v_h_2568_, v_inst_x27_2569_, v_fallback_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
lean_dec(v_a_2571_);
lean_dec_ref(v_f_2561_);
return v_res_2581_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__2(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = lean_unsigned_to_nat(0u);
v___x_2586_ = l_Lean_mkBVar(v___x_2585_);
return v___x_2586_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2(lean_object* v_proof_2592_, lean_object* v_arg_2593_, lean_object* v_e_x27_2594_, lean_object* v_arg_2595_, uint8_t v_a_2596_, lean_object* v_arg_2597_, lean_object* v___x_2598_, lean_object* v_snd_2599_, lean_object* v_e_2600_, uint8_t v___x_2601_, uint8_t v_contextDependent_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v___x_2613_; 
v___x_2613_ = l_Lean_Meta_Sym_shareCommon(v_proof_2592_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2615_; uint8_t v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc_n(v_a_2614_, 2);
lean_dec_ref_known(v___x_2613_, 1);
v___x_2615_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__1));
v___x_2616_ = 0;
v___x_2617_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2);
v___x_2618_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__2);
lean_inc_ref_n(v_e_x27_2594_, 2);
lean_inc_ref(v_arg_2593_);
v___x_2619_ = l_Lean_mkApp4(v___x_2617_, v_arg_2593_, v_e_x27_2594_, v_a_2614_, v___x_2618_);
v___x_2620_ = lean_unsigned_to_nat(1u);
v___x_2621_ = lean_mk_empty_array_with_capacity(v___x_2620_);
lean_inc_ref(v___x_2621_);
v___x_2622_ = lean_array_push(v___x_2621_, v___x_2619_);
v___x_2623_ = l_Lean_Expr_betaRev(v_arg_2595_, v___x_2622_, v_a_2596_, v_a_2596_);
lean_dec_ref(v___x_2622_);
v___x_2624_ = l_Lean_mkLambda(v___x_2615_, v___x_2616_, v_e_x27_2594_, v___x_2623_);
v___x_2625_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2624_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_a_2626_);
lean_dec_ref_known(v___x_2625_, 1);
lean_inc_ref_n(v_e_x27_2594_, 2);
v___x_2627_ = l_Lean_mkNot(v_e_x27_2594_);
v___x_2628_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7);
lean_inc(v_a_2614_);
v___x_2629_ = l_Lean_mkApp4(v___x_2628_, v_arg_2593_, v_e_x27_2594_, v_a_2614_, v___x_2618_);
v___x_2630_ = lean_array_push(v___x_2621_, v___x_2629_);
v___x_2631_ = l_Lean_Expr_betaRev(v_arg_2597_, v___x_2630_, v_a_2596_, v_a_2596_);
lean_dec_ref(v___x_2630_);
v___x_2632_ = l_Lean_mkLambda(v___x_2615_, v___x_2616_, v___x_2627_, v___x_2631_);
v___x_2633_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2632_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2635_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
lean_dec_ref_known(v___x_2633_, 1);
lean_inc_ref(v_snd_2599_);
lean_inc_ref(v_e_x27_2594_);
v___x_2635_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v___x_2598_, v_e_x27_2594_, v_snd_2599_, v_a_2626_, v_a_2634_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2647_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2638_ = v___x_2635_;
v_isShared_2639_ = v_isSharedCheck_2647_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2635_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2647_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2645_; 
v___x_2640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___closed__4));
v___x_2641_ = l_Lean_Expr_replaceFn(v_e_2600_, v___x_2640_);
v___x_2642_ = l_Lean_mkApp3(v___x_2641_, v_e_x27_2594_, v_snd_2599_, v_a_2614_);
v___x_2643_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2643_, 0, v_a_2636_);
lean_ctor_set(v___x_2643_, 1, v___x_2642_);
lean_ctor_set_uint8(v___x_2643_, sizeof(void*)*2, v___x_2601_);
lean_ctor_set_uint8(v___x_2643_, sizeof(void*)*2 + 1, v_contextDependent_2602_);
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v___x_2643_);
v___x_2645_ = v___x_2638_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2643_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
else
{
lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
lean_dec(v_a_2614_);
lean_dec_ref(v_e_2600_);
lean_dec_ref(v_snd_2599_);
lean_dec_ref(v_e_x27_2594_);
v_a_2648_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2650_ = v___x_2635_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_dec(v___x_2635_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2648_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
lean_dec(v_a_2626_);
lean_dec(v_a_2614_);
lean_dec_ref(v_e_2600_);
lean_dec_ref(v_snd_2599_);
lean_dec_ref(v___x_2598_);
lean_dec_ref(v_e_x27_2594_);
v_a_2656_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2633_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2633_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
else
{
lean_object* v_a_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2671_; 
lean_dec_ref(v___x_2621_);
lean_dec(v_a_2614_);
lean_dec_ref(v_e_2600_);
lean_dec_ref(v_snd_2599_);
lean_dec_ref(v___x_2598_);
lean_dec_ref(v_arg_2597_);
lean_dec_ref(v_e_x27_2594_);
lean_dec_ref(v_arg_2593_);
v_a_2664_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2666_ = v___x_2625_;
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_a_2664_);
lean_dec(v___x_2625_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2671_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2669_; 
if (v_isShared_2667_ == 0)
{
v___x_2669_ = v___x_2666_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_a_2664_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
else
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
lean_dec_ref(v_e_2600_);
lean_dec_ref(v_snd_2599_);
lean_dec_ref(v___x_2598_);
lean_dec_ref(v_arg_2597_);
lean_dec_ref(v_arg_2595_);
lean_dec_ref(v_e_x27_2594_);
lean_dec_ref(v_arg_2593_);
v_a_2672_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___x_2613_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2613_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_proof_2592_ = stack[0].m_obj;
lean_object* v_arg_2593_ = stack[1].m_obj;
lean_object* v_e_x27_2594_ = stack[2].m_obj;
lean_object* v_arg_2595_ = stack[3].m_obj;
uint8_t v_a_2596_ = stack[4].m_num;
lean_object* v_arg_2597_ = stack[5].m_obj;
lean_object* v___x_2598_ = stack[6].m_obj;
lean_object* v_snd_2599_ = stack[7].m_obj;
lean_object* v_e_2600_ = stack[8].m_obj;
uint8_t v___x_2601_ = stack[9].m_num;
uint8_t v_contextDependent_2602_ = stack[10].m_num;
lean_object* v___y_2603_ = stack[11].m_obj;
lean_object* v___y_2604_ = stack[12].m_obj;
lean_object* v___y_2605_ = stack[13].m_obj;
lean_object* v___y_2606_ = stack[14].m_obj;
lean_object* v___y_2607_ = stack[15].m_obj;
lean_object* v___y_2608_ = stack[16].m_obj;
lean_object* v___y_2609_ = stack[17].m_obj;
lean_object* v___y_2610_ = stack[18].m_obj;
lean_object* v___y_2611_ = stack[19].m_obj;
lean_object* v_res_2680_;
v_res_2680_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2(v_proof_2592_, v_arg_2593_, v_e_x27_2594_, v_arg_2595_, v_a_2596_, v_arg_2597_, v___x_2598_, v_snd_2599_, v_e_2600_, v___x_2601_, v_contextDependent_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
stack->m_obj
 = v_res_2680_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___boxed(lean_object** _args){
lean_object* v_proof_2681_ = _args[0];
lean_object* v_arg_2682_ = _args[1];
lean_object* v_e_x27_2683_ = _args[2];
lean_object* v_arg_2684_ = _args[3];
lean_object* v_a_2685_ = _args[4];
lean_object* v_arg_2686_ = _args[5];
lean_object* v___x_2687_ = _args[6];
lean_object* v_snd_2688_ = _args[7];
lean_object* v_e_2689_ = _args[8];
lean_object* v___x_2690_ = _args[9];
lean_object* v_contextDependent_2691_ = _args[10];
lean_object* v___y_2692_ = _args[11];
lean_object* v___y_2693_ = _args[12];
lean_object* v___y_2694_ = _args[13];
lean_object* v___y_2695_ = _args[14];
lean_object* v___y_2696_ = _args[15];
lean_object* v___y_2697_ = _args[16];
lean_object* v___y_2698_ = _args[17];
lean_object* v___y_2699_ = _args[18];
lean_object* v___y_2700_ = _args[19];
lean_object* v___y_2701_ = _args[20];
_start:
{
uint8_t v_a_30542__boxed_2702_; uint8_t v___x_30546__boxed_2703_; uint8_t v_contextDependent_30547__boxed_2704_; lean_object* v_res_2705_; 
v_a_30542__boxed_2702_ = lean_unbox(v_a_2685_);
v___x_30546__boxed_2703_ = lean_unbox(v___x_2690_);
v_contextDependent_30547__boxed_2704_ = lean_unbox(v_contextDependent_2691_);
v_res_2705_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2(v_proof_2681_, v_arg_2682_, v_e_x27_2683_, v_arg_2684_, v_a_30542__boxed_2702_, v_arg_2686_, v___x_2687_, v_snd_2688_, v_e_2689_, v___x_30546__boxed_2703_, v_contextDependent_30547__boxed_2704_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
return v_res_2705_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2712_ = lean_box(0);
v___x_2713_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3));
v___x_2714_ = l_Lean_mkConst(v___x_2713_, v___x_2712_);
return v___x_2714_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2715_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4);
v___x_2716_ = lean_unsigned_to_nat(1u);
v___x_2717_ = lean_mk_empty_array_with_capacity(v___x_2716_);
v___x_2718_ = lean_array_push(v___x_2717_, v___x_2715_);
return v___x_2718_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2725_ = lean_box(0);
v___x_2726_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8));
v___x_2727_ = l_Lean_mkConst(v___x_2726_, v___x_2725_);
return v___x_2727_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2728_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9);
v___x_2729_ = lean_unsigned_to_nat(1u);
v___x_2730_ = lean_mk_empty_array_with_capacity(v___x_2729_);
v___x_2731_ = lean_array_push(v___x_2730_, v___x_2728_);
return v___x_2731_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(uint8_t v___x_2740_, lean_object* v_e_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v___x_2755_; uint8_t v___x_2756_; 
lean_inc_ref(v_e_2741_);
v___x_2755_ = l_Lean_Expr_cleanupAnnotations(v_e_2741_);
v___x_2756_ = l_Lean_Expr_isApp(v___x_2755_);
if (v___x_2756_ == 0)
{
lean_dec_ref(v___x_2755_);
lean_dec_ref(v_e_2741_);
goto v___jp_2752_;
}
else
{
lean_object* v_arg_2757_; lean_object* v___x_2758_; uint8_t v___x_2759_; 
v_arg_2757_ = lean_ctor_get(v___x_2755_, 1);
lean_inc_ref(v_arg_2757_);
v___x_2758_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2755_);
v___x_2759_ = l_Lean_Expr_isApp(v___x_2758_);
if (v___x_2759_ == 0)
{
lean_dec_ref(v___x_2758_);
lean_dec_ref(v_arg_2757_);
lean_dec_ref(v_e_2741_);
goto v___jp_2752_;
}
else
{
lean_object* v_arg_2760_; lean_object* v___x_2761_; uint8_t v___x_2762_; 
v_arg_2760_ = lean_ctor_get(v___x_2758_, 1);
lean_inc_ref(v_arg_2760_);
v___x_2761_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2758_);
v___x_2762_ = l_Lean_Expr_isApp(v___x_2761_);
if (v___x_2762_ == 0)
{
lean_dec_ref(v___x_2761_);
lean_dec_ref(v_arg_2760_);
lean_dec_ref(v_arg_2757_);
lean_dec_ref(v_e_2741_);
goto v___jp_2752_;
}
else
{
lean_object* v_arg_2763_; lean_object* v___x_2764_; uint8_t v___x_2765_; 
v_arg_2763_ = lean_ctor_get(v___x_2761_, 1);
lean_inc_ref(v_arg_2763_);
v___x_2764_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2761_);
v___x_2765_ = l_Lean_Expr_isApp(v___x_2764_);
if (v___x_2765_ == 0)
{
lean_dec_ref(v___x_2764_);
lean_dec_ref(v_arg_2763_);
lean_dec_ref(v_arg_2760_);
lean_dec_ref(v_arg_2757_);
lean_dec_ref(v_e_2741_);
goto v___jp_2752_;
}
else
{
lean_object* v_arg_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
v_arg_2766_ = lean_ctor_get(v___x_2764_, 1);
lean_inc_ref(v_arg_2766_);
v___x_2767_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2764_);
v___x_2768_ = l_Lean_Expr_isApp(v___x_2767_);
if (v___x_2768_ == 0)
{
lean_dec_ref(v___x_2767_);
lean_dec_ref(v_arg_2766_);
lean_dec_ref(v_arg_2763_);
lean_dec_ref(v_arg_2760_);
lean_dec_ref(v_arg_2757_);
lean_dec_ref(v_e_2741_);
goto v___jp_2752_;
}
else
{
lean_object* v_arg_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; uint8_t v___x_2772_; 
v_arg_2769_ = lean_ctor_get(v___x_2767_, 1);
lean_inc_ref(v_arg_2769_);
v___x_2770_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2767_);
v___x_2771_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1));
v___x_2772_ = l_Lean_Expr_isConstOf(v___x_2770_, v___x_2771_);
if (v___x_2772_ == 0)
{
lean_dec_ref(v___x_2770_);
lean_dec_ref(v_arg_2769_);
lean_dec_ref(v_arg_2766_);
lean_dec_ref(v_arg_2763_);
lean_dec_ref(v_arg_2760_);
lean_dec_ref(v_arg_2757_);
lean_dec_ref(v_e_2741_);
goto v___jp_2752_;
}
else
{
lean_object* v___x_2773_; 
lean_inc(v___y_2750_);
lean_inc_ref(v___y_2749_);
lean_inc(v___y_2748_);
lean_inc_ref(v___y_2747_);
lean_inc(v___y_2746_);
lean_inc_ref(v___y_2745_);
lean_inc(v___y_2744_);
lean_inc_ref(v___y_2743_);
lean_inc(v___y_2742_);
lean_inc_ref(v_arg_2766_);
v___x_2773_ = lean_sym_simp(v_arg_2766_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2773_, 1);
if (lean_obj_tag(v_a_2774_) == 0)
{
uint8_t v_contextDependent_2775_; lean_object* v___x_2776_; 
lean_dec_ref(v_e_2741_);
v_contextDependent_2775_ = lean_ctor_get_uint8(v_a_2774_, 1);
lean_dec_ref_known(v_a_2774_, 0);
v___x_2776_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_2766_, v___y_2745_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; uint8_t v___x_2778_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2776_, 1);
v___x_2778_ = lean_unbox(v_a_2777_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; 
v___x_2779_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_2766_, v___y_2745_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; uint8_t v___x_2781_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2780_);
lean_dec_ref_known(v___x_2779_, 1);
v___x_2781_ = lean_unbox(v_a_2780_);
lean_dec(v_a_2780_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2782_; lean_object* v___f_2783_; lean_object* v___x_2784_; 
lean_dec(v_a_2777_);
v___x_2782_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_2772_, v_contextDependent_2775_);
v___f_2783_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2783_, 0, v___x_2782_);
v___x_2784_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v___x_2770_, v_arg_2769_, v_arg_2766_, v_arg_2763_, v_arg_2760_, v_arg_2757_, v___f_2783_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
lean_dec_ref(v___x_2770_);
return v___x_2784_;
}
else
{
lean_object* v___x_2785_; uint8_t v___x_2786_; uint8_t v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
lean_dec_ref(v_arg_2766_);
v___x_2785_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5);
v___x_2786_ = lean_unbox(v_a_2777_);
v___x_2787_ = lean_unbox(v_a_2777_);
lean_inc_ref(v_arg_2757_);
v___x_2788_ = l_Lean_Expr_betaRev(v_arg_2757_, v___x_2785_, v___x_2786_, v___x_2787_);
v___x_2789_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2788_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2803_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2792_ = v___x_2789_;
v_isShared_2793_ = v_isSharedCheck_2803_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2789_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2803_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; uint8_t v___x_2799_; lean_object* v___x_2801_; 
v___x_2794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6));
v___x_2795_ = l_Lean_Expr_constLevels_x21(v___x_2770_);
lean_dec_ref(v___x_2770_);
v___x_2796_ = l_Lean_mkConst(v___x_2794_, v___x_2795_);
v___x_2797_ = l_Lean_mkApp4(v___x_2796_, v_arg_2769_, v_arg_2763_, v_arg_2760_, v_arg_2757_);
v___x_2798_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2798_, 0, v_a_2790_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
v___x_2799_ = lean_unbox(v_a_2777_);
lean_dec(v_a_2777_);
lean_ctor_set_uint8(v___x_2798_, sizeof(void*)*2, v___x_2799_);
lean_ctor_set_uint8(v___x_2798_, sizeof(void*)*2 + 1, v_contextDependent_2775_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 0, v___x_2798_);
v___x_2801_ = v___x_2792_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2798_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_dec(v_a_2777_);
lean_dec_ref(v___x_2770_);
lean_dec_ref(v_arg_2769_);
lean_dec_ref(v_arg_2763_);
lean_dec_ref(v_arg_2760_);
lean_dec_ref(v_arg_2757_);
v_a_2804_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2789_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2789_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_dec(v_a_2777_);
lean_dec_ref(v___x_2770_);
lean_dec_ref(v_arg_2769_);
lean_dec_ref(v_arg_2766_);
lean_dec_ref(v_arg_2763_);
lean_dec_ref(v_arg_2760_);
lean_dec_ref(v_arg_2757_);
v_a_2812_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2779_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2779_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
else
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
lean_dec(v_a_2777_);
lean_dec_ref(v_arg_2766_);
v___x_2820_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10);
lean_inc_ref(v_arg_2760_);
v___x_2821_ = l_Lean_Expr_betaRev(v_arg_2760_, v___x_2820_, v___x_2740_, v___x_2740_);
v___x_2822_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2821_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2835_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2825_ = v___x_2822_;
v_isShared_2826_ = v_isSharedCheck_2835_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2822_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2835_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2833_; 
v___x_2827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11));
v___x_2828_ = l_Lean_Expr_constLevels_x21(v___x_2770_);
lean_dec_ref(v___x_2770_);
v___x_2829_ = l_Lean_mkConst(v___x_2827_, v___x_2828_);
v___x_2830_ = l_Lean_mkApp4(v___x_2829_, v_arg_2769_, v_arg_2763_, v_arg_2760_, v_arg_2757_);
v___x_2831_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2831_, 0, v_a_2823_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
lean_ctor_set_uint8(v___x_2831_, sizeof(void*)*2, v___x_2740_);
lean_ctor_set_uint8(v___x_2831_, sizeof(void*)*2 + 1, v_contextDependent_2775_);
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v___x_2831_);
v___x_2833_ = v___x_2825_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2831_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
lean_dec_ref(v___x_2770_);
lean_dec_ref(v_arg_2769_);
lean_dec_ref(v_arg_2763_);
lean_dec_ref(v_arg_2760_);
lean_dec_ref(v_arg_2757_);
v_a_2836_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2822_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2822_);
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
}
else
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
lean_dec_ref(v___x_2770_);
lean_dec_ref(v_arg_2769_);
lean_dec_ref(v_arg_2766_);
lean_dec_ref(v_arg_2763_);
lean_dec_ref(v_arg_2760_);
lean_dec_ref(v_arg_2757_);
v_a_2844_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___x_2776_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2776_);
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
else
{
lean_object* v_e_x27_2852_; lean_object* v_proof_2853_; uint8_t v_contextDependent_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2984_; 
v_e_x27_2852_ = lean_ctor_get(v_a_2774_, 0);
v_proof_2853_ = lean_ctor_get(v_a_2774_, 1);
v_contextDependent_2854_ = lean_ctor_get_uint8(v_a_2774_, sizeof(void*)*2 + 1);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_a_2774_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2856_ = v_a_2774_;
v_isShared_2857_ = v_isSharedCheck_2984_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_proof_2853_);
lean_inc(v_e_x27_2852_);
lean_dec(v_a_2774_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2984_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2858_; 
v___x_2858_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_2852_, v___y_2745_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; uint8_t v___x_2860_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref_known(v___x_2858_, 1);
v___x_2860_ = lean_unbox(v_a_2859_);
if (v___x_2860_ == 0)
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_2852_, v___y_2745_);
lean_dec_ref(v_e_x27_2852_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; uint8_t v___x_2863_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
v___x_2863_ = lean_unbox(v_a_2862_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; 
lean_dec(v_a_2859_);
lean_del_object(v___x_2856_);
lean_dec_ref(v_proof_2853_);
lean_inc_ref(v_arg_2763_);
v___x_2864_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance(v_arg_2763_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v_fst_2866_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2864_, 1);
v_fst_2866_ = lean_ctor_get(v_a_2865_, 0);
lean_inc(v_fst_2866_);
if (lean_obj_tag(v_fst_2866_) == 0)
{
uint8_t v_contextDependent_2867_; lean_object* v___x_2868_; lean_object* v___f_2869_; lean_object* v___x_2870_; 
lean_dec(v_a_2865_);
lean_dec(v_a_2862_);
lean_dec_ref(v_e_2741_);
v_contextDependent_2867_ = lean_ctor_get_uint8(v_fst_2866_, 1);
lean_dec_ref_known(v_fst_2866_, 0);
v___x_2868_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_2772_, v_contextDependent_2867_);
v___f_2869_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_2869_, 0, v___x_2868_);
v___x_2870_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v___x_2770_, v_arg_2769_, v_arg_2766_, v_arg_2763_, v_arg_2760_, v_arg_2757_, v___f_2869_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
lean_dec_ref(v___x_2770_);
return v___x_2870_;
}
else
{
lean_object* v_snd_2871_; lean_object* v_e_x27_2872_; lean_object* v_proof_2873_; uint8_t v_contextDependent_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___f_2879_; lean_object* v___x_2880_; 
v_snd_2871_ = lean_ctor_get(v_a_2865_, 1);
lean_inc_n(v_snd_2871_, 2);
lean_dec(v_a_2865_);
v_e_x27_2872_ = lean_ctor_get(v_fst_2866_, 0);
lean_inc_ref_n(v_e_x27_2872_, 2);
v_proof_2873_ = lean_ctor_get(v_fst_2866_, 1);
lean_inc_ref_n(v_proof_2873_, 2);
v_contextDependent_2874_ = lean_ctor_get_uint8(v_fst_2866_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_2866_, 2);
v___x_2875_ = lean_unsigned_to_nat(4u);
v___x_2876_ = l_Lean_Expr_getBoundedAppFn(v___x_2875_, v_e_2741_);
v___x_2877_ = lean_box(v___x_2772_);
v___x_2878_ = lean_box(v_contextDependent_2874_);
lean_inc_ref(v_arg_2757_);
lean_inc_ref(v_arg_2760_);
lean_inc_ref(v_arg_2766_);
v___f_2879_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__2___boxed), 21, 11);
lean_closure_set(v___f_2879_, 0, v_proof_2873_);
lean_closure_set(v___f_2879_, 1, v_arg_2766_);
lean_closure_set(v___f_2879_, 2, v_e_x27_2872_);
lean_closure_set(v___f_2879_, 3, v_arg_2760_);
lean_closure_set(v___f_2879_, 4, v_a_2862_);
lean_closure_set(v___f_2879_, 5, v_arg_2757_);
lean_closure_set(v___f_2879_, 6, v___x_2876_);
lean_closure_set(v___f_2879_, 7, v_snd_2871_);
lean_closure_set(v___f_2879_, 8, v_e_2741_);
lean_closure_set(v___f_2879_, 9, v___x_2877_);
lean_closure_set(v___f_2879_, 10, v___x_2878_);
v___x_2880_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr(v___x_2770_, v_arg_2769_, v_arg_2766_, v_arg_2763_, v_arg_2760_, v_arg_2757_, v_e_x27_2872_, v_proof_2873_, v_snd_2871_, v___f_2879_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
lean_dec_ref(v___x_2770_);
return v___x_2880_;
}
}
else
{
lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
lean_dec(v_a_2862_);
lean_dec_ref(v___x_2770_);
lean_dec_ref(v_arg_2769_);
lean_dec_ref(v_arg_2766_);
lean_dec_ref(v_arg_2763_);
lean_dec_ref(v_arg_2760_);
lean_dec_ref(v_arg_2757_);
lean_dec_ref(v_e_2741_);
v_a_2881_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2864_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_dec(v___x_2864_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
else
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
lean_dec(v_a_2862_);
lean_dec_ref(v___x_2770_);
lean_dec_ref(v_arg_2769_);
lean_dec_ref(v_arg_2763_);
lean_dec_ref(v_arg_2760_);
lean_inc_ref(v_proof_2853_);
v___x_2889_ = l_Lean_Meta_mkOfEqFalseCore(v_arg_2766_, v_proof_2853_);
v___x_2890_ = l_Lean_Meta_Sym_shareCommon(v___x_2889_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; uint8_t v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
lean_dec_ref_known(v___x_2890_, 1);
v___x_2892_ = lean_unsigned_to_nat(1u);
v___x_2893_ = lean_mk_empty_array_with_capacity(v___x_2892_);
v___x_2894_ = lean_array_push(v___x_2893_, v_a_2891_);
v___x_2895_ = lean_unbox(v_a_2859_);
v___x_2896_ = lean_unbox(v_a_2859_);
v___x_2897_ = l_Lean_Expr_betaRev(v_arg_2757_, v___x_2894_, v___x_2895_, v___x_2896_);
lean_dec_ref(v___x_2894_);
v___x_2898_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2897_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2913_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2901_ = v___x_2898_;
v_isShared_2902_ = v_isSharedCheck_2913_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2898_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2913_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2907_; 
v___x_2903_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13));
v___x_2904_ = l_Lean_Expr_replaceFn(v_e_2741_, v___x_2903_);
v___x_2905_ = l_Lean_Expr_app___override(v___x_2904_, v_proof_2853_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 1, v___x_2905_);
lean_ctor_set(v___x_2856_, 0, v_a_2899_);
v___x_2907_ = v___x_2856_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2899_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v___x_2905_);
v___x_2907_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
uint8_t v___x_2908_; lean_object* v___x_2910_; 
v___x_2908_ = lean_unbox(v_a_2859_);
lean_dec(v_a_2859_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*2, v___x_2908_);
lean_ctor_set_uint8(v___x_2907_, sizeof(void*)*2 + 1, v_contextDependent_2854_);
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 0, v___x_2907_);
v___x_2910_ = v___x_2901_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2907_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec(v_a_2859_);
lean_del_object(v___x_2856_);
lean_dec_ref(v_proof_2853_);
lean_dec_ref(v_e_2741_);
v_a_2914_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2898_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2898_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec(v_a_2859_);
lean_del_object(v___x_2856_);
lean_dec_ref(v_proof_2853_);
lean_dec_ref(v_arg_2757_);
lean_dec_ref(v_e_2741_);
v_a_2922_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2890_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2890_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec(v_a_2859_);
lean_del_object(v___x_2856_);
lean_dec_ref(v_proof_2853_);
lean_dec_ref(v___x_2770_);
lean_dec_ref(v_arg_2769_);
lean_dec_ref(v_arg_2766_);
lean_dec_ref(v_arg_2763_);
lean_dec_ref(v_arg_2760_);
lean_dec_ref(v_arg_2757_);
lean_dec_ref(v_e_2741_);
v_a_2930_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2861_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2861_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
else
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
lean_dec(v_a_2859_);
lean_dec_ref(v_e_x27_2852_);
lean_dec_ref(v___x_2770_);
lean_dec_ref(v_arg_2769_);
lean_dec_ref(v_arg_2763_);
lean_dec_ref(v_arg_2757_);
lean_inc_ref(v_proof_2853_);
v___x_2938_ = l_Lean_Meta_mkOfEqTrueCore(v_arg_2766_, v_proof_2853_);
v___x_2939_ = l_Lean_Meta_Sym_shareCommon(v___x_2938_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref_known(v___x_2939_, 1);
v___x_2941_ = lean_unsigned_to_nat(1u);
v___x_2942_ = lean_mk_empty_array_with_capacity(v___x_2941_);
v___x_2943_ = lean_array_push(v___x_2942_, v_a_2940_);
v___x_2944_ = l_Lean_Expr_betaRev(v_arg_2760_, v___x_2943_, v___x_2740_, v___x_2740_);
lean_dec_ref(v___x_2943_);
v___x_2945_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2944_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2959_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2948_ = v___x_2945_;
v_isShared_2949_ = v_isSharedCheck_2959_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2945_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2959_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2954_; 
v___x_2950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15));
v___x_2951_ = l_Lean_Expr_replaceFn(v_e_2741_, v___x_2950_);
v___x_2952_ = l_Lean_Expr_app___override(v___x_2951_, v_proof_2853_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 1, v___x_2952_);
lean_ctor_set(v___x_2856_, 0, v_a_2946_);
v___x_2954_ = v___x_2856_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2946_);
lean_ctor_set(v_reuseFailAlloc_2958_, 1, v___x_2952_);
lean_ctor_set_uint8(v_reuseFailAlloc_2958_, sizeof(void*)*2 + 1, v_contextDependent_2854_);
v___x_2954_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
lean_object* v___x_2956_; 
lean_ctor_set_uint8(v___x_2954_, sizeof(void*)*2, v___x_2740_);
if (v_isShared_2949_ == 0)
{
lean_ctor_set(v___x_2948_, 0, v___x_2954_);
v___x_2956_ = v___x_2948_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v___x_2954_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
lean_del_object(v___x_2856_);
lean_dec_ref(v_proof_2853_);
lean_dec_ref(v_e_2741_);
v_a_2960_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2945_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2945_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
lean_del_object(v___x_2856_);
lean_dec_ref(v_proof_2853_);
lean_dec_ref(v_arg_2760_);
lean_dec_ref(v_e_2741_);
v_a_2968_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2939_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2939_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_del_object(v___x_2856_);
lean_dec_ref(v_proof_2853_);
lean_dec_ref(v_e_x27_2852_);
lean_dec_ref(v___x_2770_);
lean_dec_ref(v_arg_2769_);
lean_dec_ref(v_arg_2766_);
lean_dec_ref(v_arg_2763_);
lean_dec_ref(v_arg_2760_);
lean_dec_ref(v_arg_2757_);
lean_dec_ref(v_e_2741_);
v_a_2976_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2858_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2858_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_2770_);
lean_dec_ref(v_arg_2769_);
lean_dec_ref(v_arg_2766_);
lean_dec_ref(v_arg_2763_);
lean_dec_ref(v_arg_2760_);
lean_dec_ref(v_arg_2757_);
lean_dec_ref(v_e_2741_);
return v___x_2773_;
}
}
}
}
}
}
}
v___jp_2752_:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2753_, 0, v___x_2740_);
lean_ctor_set_uint8(v___x_2753_, 1, v___x_2740_);
v___x_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
return v___x_2754_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2740_ = stack[0].m_num;
lean_object* v_e_2741_ = stack[1].m_obj;
lean_object* v___y_2742_ = stack[2].m_obj;
lean_object* v___y_2743_ = stack[3].m_obj;
lean_object* v___y_2744_ = stack[4].m_obj;
lean_object* v___y_2745_ = stack[5].m_obj;
lean_object* v___y_2746_ = stack[6].m_obj;
lean_object* v___y_2747_ = stack[7].m_obj;
lean_object* v___y_2748_ = stack[8].m_obj;
lean_object* v___y_2749_ = stack[9].m_obj;
lean_object* v___y_2750_ = stack[10].m_obj;
lean_object* v_res_2985_;
v_res_2985_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(v___x_2740_, v_e_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
stack->m_obj
 = v_res_2985_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed(lean_object* v___x_2986_, lean_object* v_e_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
uint8_t v___x_30930__boxed_2998_; lean_object* v_res_2999_; 
v___x_30930__boxed_2998_ = lean_unbox(v___x_2986_);
v_res_2999_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(v___x_30930__boxed_2998_, v_e_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec(v___y_2988_);
return v_res_2999_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv(lean_object* v_e_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_){
_start:
{
lean_object* v_numArgs_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; 
v_numArgs_3011_ = l_Lean_Expr_getAppNumArgs(v_e_3000_);
v___x_3012_ = lean_unsigned_to_nat(5u);
v___x_3013_ = lean_nat_dec_lt(v_numArgs_3011_, v___x_3012_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; lean_object* v___f_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3014_ = lean_box(v___x_3013_);
v___f_3015_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed), 12, 1);
lean_closure_set(v___f_3015_, 0, v___x_3014_);
v___x_3016_ = lean_nat_sub(v_numArgs_3011_, v___x_3012_);
lean_dec(v_numArgs_3011_);
v___x_3017_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_3000_, v___x_3016_, v___f_3015_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_);
lean_dec(v___x_3016_);
return v___x_3017_;
}
else
{
uint8_t v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
lean_dec(v_numArgs_3011_);
lean_dec_ref(v_e_3000_);
v___x_3018_ = 0;
v___x_3019_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3019_, 0, v___x_3013_);
lean_ctor_set_uint8(v___x_3019_, 1, v___x_3018_);
v___x_3020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3019_);
return v___x_3020_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3000_ = stack[0].m_obj;
lean_object* v_a_3001_ = stack[1].m_obj;
lean_object* v_a_3002_ = stack[2].m_obj;
lean_object* v_a_3003_ = stack[3].m_obj;
lean_object* v_a_3004_ = stack[4].m_obj;
lean_object* v_a_3005_ = stack[5].m_obj;
lean_object* v_a_3006_ = stack[6].m_obj;
lean_object* v_a_3007_ = stack[7].m_obj;
lean_object* v_a_3008_ = stack[8].m_obj;
lean_object* v_a_3009_ = stack[9].m_obj;
lean_object* v_res_3021_;
v_res_3021_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv(v_e_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_);
stack->m_obj
 = v_res_3021_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed(lean_object* v_e_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv(v_e_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_);
lean_dec(v_a_3031_);
lean_dec_ref(v_a_3030_);
lean_dec(v_a_3029_);
lean_dec_ref(v_a_3028_);
lean_dec(v_a_3027_);
lean_dec_ref(v_a_3026_);
lean_dec(v_a_3025_);
lean_dec_ref(v_a_3024_);
lean_dec(v_a_3023_);
return v_res_3033_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3052_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17_));
v___x_3053_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17_));
v___x_3054_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed), 11, 0);
v___x_3055_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_3052_, v___x_3053_, v___x_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3056_;
v_res_3056_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17_();
stack->m_obj
 = v_res_3056_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17____boxed(lean_object* v_a_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17_();
return v_res_3058_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_3060_; uint8_t v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3060_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17_));
v___x_3061_ = 0;
v___x_3062_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed), 11, 0);
v___x_3063_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_3060_, v___x_3061_, v___x_3062_);
return v___x_3063_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_19__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3064_;
v_res_3064_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_19_();
stack->m_obj
 = v_res_3064_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_19____boxed(lean_object* v_a_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_19_();
return v_res_3066_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3072_ = lean_box(0);
v___x_3073_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1));
v___x_3074_ = l_Lean_mkConst(v___x_3073_, v___x_3072_);
return v___x_3074_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = lean_box(0);
v___x_3081_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4));
v___x_3082_ = l_Lean_mkConst(v___x_3081_, v___x_3080_);
return v___x_3082_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(lean_object* v_p_3083_, lean_object* v_inst_3084_, lean_object* v_instToMatch_3085_, lean_object* v_fallback_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_){
_start:
{
lean_object* v___x_3097_; 
v___x_3097_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_instToMatch_3085_, v_a_3093_);
if (lean_obj_tag(v___x_3097_) == 0)
{
lean_object* v_a_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
lean_dec_ref_known(v___x_3097_, 1);
v___x_3099_ = l_Lean_Expr_cleanupAnnotations(v_a_3098_);
v___x_3100_ = l_Lean_Expr_isApp(v___x_3099_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; 
lean_dec_ref(v___x_3099_);
lean_dec_ref(v_inst_3084_);
lean_dec_ref(v_p_3083_);
lean_inc(v_a_3095_);
lean_inc_ref(v_a_3094_);
lean_inc(v_a_3093_);
lean_inc_ref(v_a_3092_);
lean_inc(v_a_3091_);
lean_inc_ref(v_a_3090_);
lean_inc(v_a_3089_);
lean_inc_ref(v_a_3088_);
lean_inc(v_a_3087_);
v___x_3101_ = lean_apply_10(v_fallback_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, lean_box(0));
return v___x_3101_;
}
else
{
lean_object* v_arg_3102_; lean_object* v___x_3103_; uint8_t v___x_3104_; 
v_arg_3102_ = lean_ctor_get(v___x_3099_, 1);
lean_inc_ref(v_arg_3102_);
v___x_3103_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3099_);
v___x_3104_ = l_Lean_Expr_isApp(v___x_3103_);
if (v___x_3104_ == 0)
{
lean_object* v___x_3105_; 
lean_dec_ref(v___x_3103_);
lean_dec_ref(v_arg_3102_);
lean_dec_ref(v_inst_3084_);
lean_dec_ref(v_p_3083_);
lean_inc(v_a_3095_);
lean_inc_ref(v_a_3094_);
lean_inc(v_a_3093_);
lean_inc_ref(v_a_3092_);
lean_inc(v_a_3091_);
lean_inc_ref(v_a_3090_);
lean_inc(v_a_3089_);
lean_inc_ref(v_a_3088_);
lean_inc(v_a_3087_);
v___x_3105_ = lean_apply_10(v_fallback_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, lean_box(0));
return v___x_3105_;
}
else
{
lean_object* v_arg_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; 
v_arg_3106_ = lean_ctor_get(v___x_3103_, 1);
lean_inc_ref(v_arg_3106_);
v___x_3107_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3103_);
v___x_3108_ = l_Lean_Expr_isApp(v___x_3107_);
if (v___x_3108_ == 0)
{
lean_object* v___x_3109_; 
lean_dec_ref(v___x_3107_);
lean_dec_ref(v_arg_3106_);
lean_dec_ref(v_arg_3102_);
lean_dec_ref(v_inst_3084_);
lean_dec_ref(v_p_3083_);
lean_inc(v_a_3095_);
lean_inc_ref(v_a_3094_);
lean_inc(v_a_3093_);
lean_inc_ref(v_a_3092_);
lean_inc(v_a_3091_);
lean_inc_ref(v_a_3090_);
lean_inc(v_a_3089_);
lean_inc_ref(v_a_3088_);
lean_inc(v_a_3087_);
v___x_3109_ = lean_apply_10(v_fallback_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, lean_box(0));
return v___x_3109_;
}
else
{
lean_object* v___x_3110_; lean_object* v___x_3111_; uint8_t v___x_3112_; 
v___x_3110_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3107_);
v___x_3111_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_3112_ = l_Lean_Expr_isConstOf(v___x_3110_, v___x_3111_);
lean_dec_ref(v___x_3110_);
if (v___x_3112_ == 0)
{
lean_object* v___x_3113_; 
lean_dec_ref(v_arg_3106_);
lean_dec_ref(v_arg_3102_);
lean_dec_ref(v_inst_3084_);
lean_dec_ref(v_p_3083_);
lean_inc(v_a_3095_);
lean_inc_ref(v_a_3094_);
lean_inc(v_a_3093_);
lean_inc_ref(v_a_3092_);
lean_inc(v_a_3091_);
lean_inc_ref(v_a_3090_);
lean_inc(v_a_3089_);
lean_inc_ref(v_a_3088_);
lean_inc(v_a_3087_);
v___x_3113_ = lean_apply_10(v_fallback_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, lean_box(0));
return v___x_3113_;
}
else
{
lean_object* v___x_3114_; 
v___x_3114_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_3106_, v_a_3093_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3115_);
lean_dec_ref_known(v___x_3114_, 1);
v___x_3116_ = l_Lean_Expr_cleanupAnnotations(v_a_3115_);
v___x_3117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_3118_ = l_Lean_Expr_isConstOf(v___x_3116_, v___x_3117_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3119_; uint8_t v___x_3120_; 
v___x_3119_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_3120_ = l_Lean_Expr_isConstOf(v___x_3116_, v___x_3119_);
lean_dec_ref(v___x_3116_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; 
lean_dec_ref(v_arg_3102_);
lean_dec_ref(v_inst_3084_);
lean_dec_ref(v_p_3083_);
lean_inc(v_a_3095_);
lean_inc_ref(v_a_3094_);
lean_inc(v_a_3093_);
lean_inc_ref(v_a_3092_);
lean_inc(v_a_3091_);
lean_inc_ref(v_a_3090_);
lean_inc(v_a_3089_);
lean_inc_ref(v_a_3088_);
lean_inc(v_a_3087_);
v___x_3121_ = lean_apply_10(v_fallback_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, lean_box(0));
return v___x_3121_;
}
else
{
lean_object* v___x_3122_; 
lean_dec_ref(v_fallback_3086_);
v___x_3122_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_3090_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3133_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3125_ = v___x_3122_;
v_isShared_3126_ = v_isSharedCheck_3133_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3122_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3133_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3131_; 
v___x_3127_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2);
v___x_3128_ = l_Lean_mkApp3(v___x_3127_, v_p_3083_, v_inst_3084_, v_arg_3102_);
v___x_3129_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3129_, 0, v_a_3123_);
lean_ctor_set(v___x_3129_, 1, v___x_3128_);
lean_ctor_set_uint8(v___x_3129_, sizeof(void*)*2, v___x_3118_);
lean_ctor_set_uint8(v___x_3129_, sizeof(void*)*2 + 1, v___x_3118_);
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 0, v___x_3129_);
v___x_3131_ = v___x_3125_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v___x_3129_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
lean_dec_ref(v_arg_3102_);
lean_dec_ref(v_inst_3084_);
lean_dec_ref(v_p_3083_);
v_a_3134_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3136_ = v___x_3122_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3122_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3134_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
}
else
{
lean_object* v___x_3142_; 
lean_dec_ref(v___x_3116_);
lean_dec_ref(v_fallback_3086_);
v___x_3142_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_3090_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3154_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3145_ = v___x_3142_;
v_isShared_3146_ = v_isSharedCheck_3154_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3142_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3154_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3152_; 
v___x_3147_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5);
v___x_3148_ = l_Lean_mkApp3(v___x_3147_, v_p_3083_, v_inst_3084_, v_arg_3102_);
v___x_3149_ = 0;
v___x_3150_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3150_, 0, v_a_3143_);
lean_ctor_set(v___x_3150_, 1, v___x_3148_);
lean_ctor_set_uint8(v___x_3150_, sizeof(void*)*2, v___x_3149_);
lean_ctor_set_uint8(v___x_3150_, sizeof(void*)*2 + 1, v___x_3149_);
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 0, v___x_3150_);
v___x_3152_ = v___x_3145_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3150_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec_ref(v_arg_3102_);
lean_dec_ref(v_inst_3084_);
lean_dec_ref(v_p_3083_);
v_a_3155_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3142_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3142_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_dec_ref(v_arg_3102_);
lean_dec_ref(v_fallback_3086_);
lean_dec_ref(v_inst_3084_);
lean_dec_ref(v_p_3083_);
v_a_3163_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3114_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3114_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
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
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
lean_dec_ref(v_fallback_3086_);
lean_dec_ref(v_inst_3084_);
lean_dec_ref(v_p_3083_);
v_a_3171_ = lean_ctor_get(v___x_3097_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3097_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3097_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3097_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3083_ = stack[0].m_obj;
lean_object* v_inst_3084_ = stack[1].m_obj;
lean_object* v_instToMatch_3085_ = stack[2].m_obj;
lean_object* v_fallback_3086_ = stack[3].m_obj;
lean_object* v_a_3087_ = stack[4].m_obj;
lean_object* v_a_3088_ = stack[5].m_obj;
lean_object* v_a_3089_ = stack[6].m_obj;
lean_object* v_a_3090_ = stack[7].m_obj;
lean_object* v_a_3091_ = stack[8].m_obj;
lean_object* v_a_3092_ = stack[9].m_obj;
lean_object* v_a_3093_ = stack[10].m_obj;
lean_object* v_a_3094_ = stack[11].m_obj;
lean_object* v_a_3095_ = stack[12].m_obj;
lean_object* v_res_3179_;
v_res_3179_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_3083_, v_inst_3084_, v_instToMatch_3085_, v_fallback_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_);
stack->m_obj
 = v_res_3179_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___boxed(lean_object* v_p_3180_, lean_object* v_inst_3181_, lean_object* v_instToMatch_3182_, lean_object* v_fallback_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_3180_, v_inst_3181_, v_instToMatch_3182_, v_fallback_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_);
lean_dec(v_a_3192_);
lean_dec_ref(v_a_3191_);
lean_dec(v_a_3190_);
lean_dec_ref(v_a_3189_);
lean_dec(v_a_3188_);
lean_dec_ref(v_a_3187_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
return v_res_3194_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2(void){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3200_ = lean_box(0);
v___x_3201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1));
v___x_3202_ = l_Lean_mkConst(v___x_3201_, v___x_3200_);
return v___x_3202_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5(void){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3208_ = lean_box(0);
v___x_3209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4));
v___x_3210_ = l_Lean_mkConst(v___x_3209_, v___x_3208_);
return v___x_3210_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(lean_object* v_p_3211_, lean_object* v_p_x27_3212_, lean_object* v_h_3213_, lean_object* v_inst_3214_, lean_object* v_inst_x27_3215_, lean_object* v_fallback_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_){
_start:
{
lean_object* v___x_3227_; 
v___x_3227_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_x27_3215_, v_a_3223_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; lean_object* v___x_3229_; uint8_t v___x_3230_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_a_3228_);
lean_dec_ref_known(v___x_3227_, 1);
v___x_3229_ = l_Lean_Expr_cleanupAnnotations(v_a_3228_);
v___x_3230_ = l_Lean_Expr_isApp(v___x_3229_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; 
lean_dec_ref(v___x_3229_);
lean_dec_ref(v_inst_3214_);
lean_dec_ref(v_h_3213_);
lean_dec_ref(v_p_x27_3212_);
lean_dec_ref(v_p_3211_);
lean_inc(v_a_3225_);
lean_inc_ref(v_a_3224_);
lean_inc(v_a_3223_);
lean_inc_ref(v_a_3222_);
lean_inc(v_a_3221_);
lean_inc_ref(v_a_3220_);
lean_inc(v_a_3219_);
lean_inc_ref(v_a_3218_);
lean_inc(v_a_3217_);
v___x_3231_ = lean_apply_10(v_fallback_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, lean_box(0));
return v___x_3231_;
}
else
{
lean_object* v_arg_3232_; lean_object* v___x_3233_; uint8_t v___x_3234_; 
v_arg_3232_ = lean_ctor_get(v___x_3229_, 1);
lean_inc_ref(v_arg_3232_);
v___x_3233_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3229_);
v___x_3234_ = l_Lean_Expr_isApp(v___x_3233_);
if (v___x_3234_ == 0)
{
lean_object* v___x_3235_; 
lean_dec_ref(v___x_3233_);
lean_dec_ref(v_arg_3232_);
lean_dec_ref(v_inst_3214_);
lean_dec_ref(v_h_3213_);
lean_dec_ref(v_p_x27_3212_);
lean_dec_ref(v_p_3211_);
lean_inc(v_a_3225_);
lean_inc_ref(v_a_3224_);
lean_inc(v_a_3223_);
lean_inc_ref(v_a_3222_);
lean_inc(v_a_3221_);
lean_inc_ref(v_a_3220_);
lean_inc(v_a_3219_);
lean_inc_ref(v_a_3218_);
lean_inc(v_a_3217_);
v___x_3235_ = lean_apply_10(v_fallback_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, lean_box(0));
return v___x_3235_;
}
else
{
lean_object* v_arg_3236_; lean_object* v___x_3237_; uint8_t v___x_3238_; 
v_arg_3236_ = lean_ctor_get(v___x_3233_, 1);
lean_inc_ref(v_arg_3236_);
v___x_3237_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3233_);
v___x_3238_ = l_Lean_Expr_isApp(v___x_3237_);
if (v___x_3238_ == 0)
{
lean_object* v___x_3239_; 
lean_dec_ref(v___x_3237_);
lean_dec_ref(v_arg_3236_);
lean_dec_ref(v_arg_3232_);
lean_dec_ref(v_inst_3214_);
lean_dec_ref(v_h_3213_);
lean_dec_ref(v_p_x27_3212_);
lean_dec_ref(v_p_3211_);
lean_inc(v_a_3225_);
lean_inc_ref(v_a_3224_);
lean_inc(v_a_3223_);
lean_inc_ref(v_a_3222_);
lean_inc(v_a_3221_);
lean_inc_ref(v_a_3220_);
lean_inc(v_a_3219_);
lean_inc_ref(v_a_3218_);
lean_inc(v_a_3217_);
v___x_3239_ = lean_apply_10(v_fallback_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, lean_box(0));
return v___x_3239_;
}
else
{
lean_object* v___x_3240_; lean_object* v___x_3241_; uint8_t v___x_3242_; 
v___x_3240_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3237_);
v___x_3241_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1));
v___x_3242_ = l_Lean_Expr_isConstOf(v___x_3240_, v___x_3241_);
lean_dec_ref(v___x_3240_);
if (v___x_3242_ == 0)
{
lean_object* v___x_3243_; 
lean_dec_ref(v_arg_3236_);
lean_dec_ref(v_arg_3232_);
lean_dec_ref(v_inst_3214_);
lean_dec_ref(v_h_3213_);
lean_dec_ref(v_p_x27_3212_);
lean_dec_ref(v_p_3211_);
lean_inc(v_a_3225_);
lean_inc_ref(v_a_3224_);
lean_inc(v_a_3223_);
lean_inc_ref(v_a_3222_);
lean_inc(v_a_3221_);
lean_inc_ref(v_a_3220_);
lean_inc(v_a_3219_);
lean_inc_ref(v_a_3218_);
lean_inc(v_a_3217_);
v___x_3243_ = lean_apply_10(v_fallback_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, lean_box(0));
return v___x_3243_;
}
else
{
lean_object* v___x_3244_; 
v___x_3244_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_3236_, v_a_3223_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; uint8_t v___x_3248_; 
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_a_3245_);
lean_dec_ref_known(v___x_3244_, 1);
v___x_3246_ = l_Lean_Expr_cleanupAnnotations(v_a_3245_);
v___x_3247_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4));
v___x_3248_ = l_Lean_Expr_isConstOf(v___x_3246_, v___x_3247_);
if (v___x_3248_ == 0)
{
lean_object* v___x_3249_; uint8_t v___x_3250_; 
v___x_3249_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6));
v___x_3250_ = l_Lean_Expr_isConstOf(v___x_3246_, v___x_3249_);
lean_dec_ref(v___x_3246_);
if (v___x_3250_ == 0)
{
lean_object* v___x_3251_; 
lean_dec_ref(v_arg_3232_);
lean_dec_ref(v_inst_3214_);
lean_dec_ref(v_h_3213_);
lean_dec_ref(v_p_x27_3212_);
lean_dec_ref(v_p_3211_);
lean_inc(v_a_3225_);
lean_inc_ref(v_a_3224_);
lean_inc(v_a_3223_);
lean_inc_ref(v_a_3222_);
lean_inc(v_a_3221_);
lean_inc_ref(v_a_3220_);
lean_inc(v_a_3219_);
lean_inc_ref(v_a_3218_);
lean_inc(v_a_3217_);
v___x_3251_ = lean_apply_10(v_fallback_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, lean_box(0));
return v___x_3251_;
}
else
{
lean_object* v___x_3252_; 
lean_dec_ref(v_fallback_3216_);
v___x_3252_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_3220_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3255_; uint8_t v_isShared_3256_; uint8_t v_isSharedCheck_3263_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3255_ = v___x_3252_;
v_isShared_3256_ = v_isSharedCheck_3263_;
goto v_resetjp_3254_;
}
else
{
lean_inc(v_a_3253_);
lean_dec(v___x_3252_);
v___x_3255_ = lean_box(0);
v_isShared_3256_ = v_isSharedCheck_3263_;
goto v_resetjp_3254_;
}
v_resetjp_3254_:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3261_; 
v___x_3257_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2);
v___x_3258_ = l_Lean_mkApp5(v___x_3257_, v_p_3211_, v_p_x27_3212_, v_h_3213_, v_inst_3214_, v_arg_3232_);
v___x_3259_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3259_, 0, v_a_3253_);
lean_ctor_set(v___x_3259_, 1, v___x_3258_);
lean_ctor_set_uint8(v___x_3259_, sizeof(void*)*2, v___x_3248_);
lean_ctor_set_uint8(v___x_3259_, sizeof(void*)*2 + 1, v___x_3248_);
if (v_isShared_3256_ == 0)
{
lean_ctor_set(v___x_3255_, 0, v___x_3259_);
v___x_3261_ = v___x_3255_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3259_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_dec_ref(v_arg_3232_);
lean_dec_ref(v_inst_3214_);
lean_dec_ref(v_h_3213_);
lean_dec_ref(v_p_x27_3212_);
lean_dec_ref(v_p_3211_);
v_a_3264_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3252_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3252_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
}
else
{
lean_object* v___x_3272_; 
lean_dec_ref(v___x_3246_);
lean_dec_ref(v_fallback_3216_);
v___x_3272_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_3220_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3284_; 
v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3275_ = v___x_3272_;
v_isShared_3276_ = v_isSharedCheck_3284_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3272_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3284_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; uint8_t v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3282_; 
v___x_3277_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5);
v___x_3278_ = l_Lean_mkApp5(v___x_3277_, v_p_3211_, v_p_x27_3212_, v_h_3213_, v_inst_3214_, v_arg_3232_);
v___x_3279_ = 0;
v___x_3280_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3280_, 0, v_a_3273_);
lean_ctor_set(v___x_3280_, 1, v___x_3278_);
lean_ctor_set_uint8(v___x_3280_, sizeof(void*)*2, v___x_3279_);
lean_ctor_set_uint8(v___x_3280_, sizeof(void*)*2 + 1, v___x_3279_);
if (v_isShared_3276_ == 0)
{
lean_ctor_set(v___x_3275_, 0, v___x_3280_);
v___x_3282_ = v___x_3275_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3280_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec_ref(v_arg_3232_);
lean_dec_ref(v_inst_3214_);
lean_dec_ref(v_h_3213_);
lean_dec_ref(v_p_x27_3212_);
lean_dec_ref(v_p_3211_);
v_a_3285_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3272_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3272_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
}
else
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3300_; 
lean_dec_ref(v_arg_3232_);
lean_dec_ref(v_fallback_3216_);
lean_dec_ref(v_inst_3214_);
lean_dec_ref(v_h_3213_);
lean_dec_ref(v_p_x27_3212_);
lean_dec_ref(v_p_3211_);
v_a_3293_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3295_ = v___x_3244_;
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3244_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3298_; 
if (v_isShared_3296_ == 0)
{
v___x_3298_ = v___x_3295_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3293_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
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
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
lean_dec_ref(v_fallback_3216_);
lean_dec_ref(v_inst_3214_);
lean_dec_ref(v_h_3213_);
lean_dec_ref(v_p_x27_3212_);
lean_dec_ref(v_p_3211_);
v_a_3301_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_3227_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3227_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3211_ = stack[0].m_obj;
lean_object* v_p_x27_3212_ = stack[1].m_obj;
lean_object* v_h_3213_ = stack[2].m_obj;
lean_object* v_inst_3214_ = stack[3].m_obj;
lean_object* v_inst_x27_3215_ = stack[4].m_obj;
lean_object* v_fallback_3216_ = stack[5].m_obj;
lean_object* v_a_3217_ = stack[6].m_obj;
lean_object* v_a_3218_ = stack[7].m_obj;
lean_object* v_a_3219_ = stack[8].m_obj;
lean_object* v_a_3220_ = stack[9].m_obj;
lean_object* v_a_3221_ = stack[10].m_obj;
lean_object* v_a_3222_ = stack[11].m_obj;
lean_object* v_a_3223_ = stack[12].m_obj;
lean_object* v_a_3224_ = stack[13].m_obj;
lean_object* v_a_3225_ = stack[14].m_obj;
lean_object* v_res_3309_;
v_res_3309_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_3211_, v_p_x27_3212_, v_h_3213_, v_inst_3214_, v_inst_x27_3215_, v_fallback_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_);
stack->m_obj
 = v_res_3309_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___boxed(lean_object* v_p_3310_, lean_object* v_p_x27_3311_, lean_object* v_h_3312_, lean_object* v_inst_3313_, lean_object* v_inst_x27_3314_, lean_object* v_fallback_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_3310_, v_p_x27_3311_, v_h_3312_, v_inst_3313_, v_inst_x27_3314_, v_fallback_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_);
lean_dec(v_a_3324_);
lean_dec_ref(v_a_3323_);
lean_dec(v_a_3322_);
lean_dec_ref(v_a_3321_);
lean_dec(v_a_3320_);
lean_dec_ref(v_a_3319_);
lean_dec(v_a_3318_);
lean_dec_ref(v_a_3317_);
lean_dec(v_a_3316_);
return v_res_3326_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(lean_object* v_p_3327_, lean_object* v_inst_3328_, lean_object* v_fallback_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_){
_start:
{
lean_object* v___x_3340_; uint8_t v___x_3341_; lean_object* v___x_3342_; lean_object* v___f_3343_; lean_object* v___x_3344_; 
v___x_3340_ = lean_unsigned_to_nat(0u);
v___x_3341_ = 5;
v___x_3342_ = lean_box(v___x_3341_);
lean_inc_ref(v_inst_3328_);
v___f_3343_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3343_, 0, v___x_3342_);
lean_closure_set(v___f_3343_, 1, v_inst_3328_);
lean_closure_set(v___f_3343_, 2, v___x_3340_);
v___x_3344_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_3343_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v_a_3345_; 
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_a_3345_);
lean_dec_ref_known(v___x_3344_, 1);
if (lean_obj_tag(v_a_3345_) == 0)
{
lean_object* v___x_3346_; 
lean_inc(v_a_3338_);
lean_inc_ref(v_a_3337_);
lean_inc(v_a_3336_);
lean_inc_ref(v_a_3335_);
lean_inc(v_a_3334_);
lean_inc_ref(v_a_3333_);
lean_inc(v_a_3332_);
lean_inc_ref(v_a_3331_);
lean_inc(v_a_3330_);
lean_inc_ref(v_inst_3328_);
v___x_3346_ = lean_sym_simp(v_inst_3328_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v_a_3347_; 
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3347_);
lean_dec_ref_known(v___x_3346_, 1);
if (lean_obj_tag(v_a_3347_) == 0)
{
uint8_t v_contextDependent_3348_; lean_object* v___x_3349_; 
v_contextDependent_3348_ = lean_ctor_get_uint8(v_a_3347_, 1);
lean_dec_ref_known(v_a_3347_, 0);
lean_inc_ref(v_inst_3328_);
v___x_3349_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_3327_, v_inst_3328_, v_inst_3328_, v_fallback_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; uint8_t v___y_3352_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
if (v_contextDependent_3348_ == 0)
{
return v___x_3349_;
}
else
{
if (lean_obj_tag(v_a_3350_) == 0)
{
uint8_t v_contextDependent_3362_; 
v_contextDependent_3362_ = lean_ctor_get_uint8(v_a_3350_, 1);
v___y_3352_ = v_contextDependent_3362_;
goto v___jp_3351_;
}
else
{
uint8_t v_contextDependent_3363_; 
v_contextDependent_3363_ = lean_ctor_get_uint8(v_a_3350_, sizeof(void*)*2 + 1);
v___y_3352_ = v_contextDependent_3363_;
goto v___jp_3351_;
}
}
v___jp_3351_:
{
if (v___y_3352_ == 0)
{
lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3360_; 
lean_inc(v_a_3350_);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3360_ == 0)
{
lean_object* v_unused_3361_; 
v_unused_3361_ = lean_ctor_get(v___x_3349_, 0);
lean_dec(v_unused_3361_);
v___x_3354_ = v___x_3349_;
v_isShared_3355_ = v_isSharedCheck_3360_;
goto v_resetjp_3353_;
}
else
{
lean_dec(v___x_3349_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3360_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3356_; lean_object* v___x_3358_; 
v___x_3356_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3350_);
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v___x_3356_);
v___x_3358_ = v___x_3354_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3356_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
else
{
return v___x_3349_;
}
}
}
else
{
return v___x_3349_;
}
}
else
{
lean_object* v_e_x27_3364_; uint8_t v_contextDependent_3365_; lean_object* v___x_3366_; 
v_e_x27_3364_ = lean_ctor_get(v_a_3347_, 0);
lean_inc_ref(v_e_x27_3364_);
v_contextDependent_3365_ = lean_ctor_get_uint8(v_a_3347_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_3347_, 2);
v___x_3366_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_3327_, v_inst_3328_, v_e_x27_3364_, v_fallback_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; uint8_t v___y_3369_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
if (v_contextDependent_3365_ == 0)
{
return v___x_3366_;
}
else
{
if (lean_obj_tag(v_a_3367_) == 0)
{
uint8_t v_contextDependent_3379_; 
v_contextDependent_3379_ = lean_ctor_get_uint8(v_a_3367_, 1);
v___y_3369_ = v_contextDependent_3379_;
goto v___jp_3368_;
}
else
{
uint8_t v_contextDependent_3380_; 
v_contextDependent_3380_ = lean_ctor_get_uint8(v_a_3367_, sizeof(void*)*2 + 1);
v___y_3369_ = v_contextDependent_3380_;
goto v___jp_3368_;
}
}
v___jp_3368_:
{
if (v___y_3369_ == 0)
{
lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3377_; 
lean_inc(v_a_3367_);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3377_ == 0)
{
lean_object* v_unused_3378_; 
v_unused_3378_ = lean_ctor_get(v___x_3366_, 0);
lean_dec(v_unused_3378_);
v___x_3371_ = v___x_3366_;
v_isShared_3372_ = v_isSharedCheck_3377_;
goto v_resetjp_3370_;
}
else
{
lean_dec(v___x_3366_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3377_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3373_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3367_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v___x_3373_);
v___x_3375_ = v___x_3371_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
else
{
return v___x_3366_;
}
}
}
else
{
return v___x_3366_;
}
}
}
else
{
lean_dec_ref(v_fallback_3329_);
lean_dec_ref(v_inst_3328_);
lean_dec_ref(v_p_3327_);
return v___x_3346_;
}
}
else
{
lean_object* v_val_3381_; lean_object* v___x_3382_; 
lean_dec_ref(v_fallback_3329_);
lean_dec_ref(v_inst_3328_);
lean_dec_ref(v_p_3327_);
v_val_3381_ = lean_ctor_get(v_a_3345_, 0);
lean_inc(v_val_3381_);
lean_dec_ref_known(v_a_3345_, 1);
v___x_3382_ = l_Lean_Meta_Sym_shareCommonInc(v_val_3381_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3395_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3385_ = v___x_3382_;
v_isShared_3386_ = v_isSharedCheck_3395_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3382_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3395_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; uint8_t v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3393_; 
v___x_3387_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8);
v___x_3388_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10);
lean_inc(v_a_3383_);
v___x_3389_ = l_Lean_mkAppB(v___x_3387_, v___x_3388_, v_a_3383_);
v___x_3390_ = 0;
v___x_3391_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3391_, 0, v_a_3383_);
lean_ctor_set(v___x_3391_, 1, v___x_3389_);
lean_ctor_set_uint8(v___x_3391_, sizeof(void*)*2, v___x_3390_);
lean_ctor_set_uint8(v___x_3391_, sizeof(void*)*2 + 1, v___x_3390_);
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 0, v___x_3391_);
v___x_3393_ = v___x_3385_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3391_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
v_a_3396_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3382_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3382_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
}
else
{
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
lean_dec_ref(v_fallback_3329_);
lean_dec_ref(v_inst_3328_);
lean_dec_ref(v_p_3327_);
v_a_3404_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3344_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3344_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3327_ = stack[0].m_obj;
lean_object* v_inst_3328_ = stack[1].m_obj;
lean_object* v_fallback_3329_ = stack[2].m_obj;
lean_object* v_a_3330_ = stack[3].m_obj;
lean_object* v_a_3331_ = stack[4].m_obj;
lean_object* v_a_3332_ = stack[5].m_obj;
lean_object* v_a_3333_ = stack[6].m_obj;
lean_object* v_a_3334_ = stack[7].m_obj;
lean_object* v_a_3335_ = stack[8].m_obj;
lean_object* v_a_3336_ = stack[9].m_obj;
lean_object* v_a_3337_ = stack[10].m_obj;
lean_object* v_a_3338_ = stack[11].m_obj;
lean_object* v_res_3412_;
v_res_3412_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(v_p_3327_, v_inst_3328_, v_fallback_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_);
stack->m_obj
 = v_res_3412_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable___boxed(lean_object* v_p_3413_, lean_object* v_inst_3414_, lean_object* v_fallback_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_){
_start:
{
lean_object* v_res_3426_; 
v_res_3426_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(v_p_3413_, v_inst_3414_, v_fallback_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_);
lean_dec(v_a_3424_);
lean_dec_ref(v_a_3423_);
lean_dec(v_a_3422_);
lean_dec_ref(v_a_3421_);
lean_dec(v_a_3420_);
lean_dec_ref(v_a_3419_);
lean_dec(v_a_3418_);
lean_dec_ref(v_a_3417_);
lean_dec(v_a_3416_);
return v_res_3426_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__2(void){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3432_ = lean_box(0);
v___x_3433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__1));
v___x_3434_ = l_Lean_mkConst(v___x_3433_, v___x_3432_);
return v___x_3434_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(lean_object* v_p_3435_, lean_object* v_p_x27_3436_, lean_object* v_h_3437_, lean_object* v_inst_3438_, lean_object* v_inst_x27_3439_, lean_object* v_fallback_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_){
_start:
{
lean_object* v___x_3451_; uint8_t v___x_3452_; lean_object* v___x_3453_; lean_object* v___f_3454_; lean_object* v___x_3455_; 
v___x_3451_ = lean_unsigned_to_nat(0u);
v___x_3452_ = 5;
v___x_3453_ = lean_box(v___x_3452_);
lean_inc_ref(v_inst_x27_3439_);
v___f_3454_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3454_, 0, v___x_3453_);
lean_closure_set(v___f_3454_, 1, v_inst_x27_3439_);
lean_closure_set(v___f_3454_, 2, v___x_3451_);
v___x_3455_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_3454_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3456_);
lean_dec_ref_known(v___x_3455_, 1);
if (lean_obj_tag(v_a_3456_) == 0)
{
lean_object* v___x_3457_; 
lean_inc(v_a_3449_);
lean_inc_ref(v_a_3448_);
lean_inc(v_a_3447_);
lean_inc_ref(v_a_3446_);
lean_inc(v_a_3445_);
lean_inc_ref(v_a_3444_);
lean_inc(v_a_3443_);
lean_inc_ref(v_a_3442_);
lean_inc(v_a_3441_);
lean_inc_ref(v_inst_x27_3439_);
v___x_3457_ = lean_sym_simp(v_inst_x27_3439_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref_known(v___x_3457_, 1);
if (lean_obj_tag(v_a_3458_) == 0)
{
uint8_t v_contextDependent_3459_; lean_object* v___x_3460_; 
v_contextDependent_3459_ = lean_ctor_get_uint8(v_a_3458_, 1);
lean_dec_ref_known(v_a_3458_, 0);
v___x_3460_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_3435_, v_p_x27_3436_, v_h_3437_, v_inst_3438_, v_inst_x27_3439_, v_fallback_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; uint8_t v___y_3463_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
if (v_contextDependent_3459_ == 0)
{
return v___x_3460_;
}
else
{
if (lean_obj_tag(v_a_3461_) == 0)
{
uint8_t v_contextDependent_3473_; 
v_contextDependent_3473_ = lean_ctor_get_uint8(v_a_3461_, 1);
v___y_3463_ = v_contextDependent_3473_;
goto v___jp_3462_;
}
else
{
uint8_t v_contextDependent_3474_; 
v_contextDependent_3474_ = lean_ctor_get_uint8(v_a_3461_, sizeof(void*)*2 + 1);
v___y_3463_ = v_contextDependent_3474_;
goto v___jp_3462_;
}
}
v___jp_3462_:
{
if (v___y_3463_ == 0)
{
lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3471_; 
lean_inc(v_a_3461_);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3471_ == 0)
{
lean_object* v_unused_3472_; 
v_unused_3472_ = lean_ctor_get(v___x_3460_, 0);
lean_dec(v_unused_3472_);
v___x_3465_ = v___x_3460_;
v_isShared_3466_ = v_isSharedCheck_3471_;
goto v_resetjp_3464_;
}
else
{
lean_dec(v___x_3460_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3471_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3467_; lean_object* v___x_3469_; 
v___x_3467_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3461_);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 0, v___x_3467_);
v___x_3469_ = v___x_3465_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3467_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
else
{
return v___x_3460_;
}
}
}
else
{
return v___x_3460_;
}
}
else
{
lean_object* v_e_x27_3475_; uint8_t v_contextDependent_3476_; lean_object* v___x_3477_; 
lean_dec_ref(v_inst_x27_3439_);
v_e_x27_3475_ = lean_ctor_get(v_a_3458_, 0);
lean_inc_ref(v_e_x27_3475_);
v_contextDependent_3476_ = lean_ctor_get_uint8(v_a_3458_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_3458_, 2);
v___x_3477_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_3435_, v_p_x27_3436_, v_h_3437_, v_inst_3438_, v_e_x27_3475_, v_fallback_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; uint8_t v___y_3480_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
if (v_contextDependent_3476_ == 0)
{
return v___x_3477_;
}
else
{
if (lean_obj_tag(v_a_3478_) == 0)
{
uint8_t v_contextDependent_3490_; 
v_contextDependent_3490_ = lean_ctor_get_uint8(v_a_3478_, 1);
v___y_3480_ = v_contextDependent_3490_;
goto v___jp_3479_;
}
else
{
uint8_t v_contextDependent_3491_; 
v_contextDependent_3491_ = lean_ctor_get_uint8(v_a_3478_, sizeof(void*)*2 + 1);
v___y_3480_ = v_contextDependent_3491_;
goto v___jp_3479_;
}
}
v___jp_3479_:
{
if (v___y_3480_ == 0)
{
lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3488_; 
lean_inc(v_a_3478_);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3488_ == 0)
{
lean_object* v_unused_3489_; 
v_unused_3489_ = lean_ctor_get(v___x_3477_, 0);
lean_dec(v_unused_3489_);
v___x_3482_ = v___x_3477_;
v_isShared_3483_ = v_isSharedCheck_3488_;
goto v_resetjp_3481_;
}
else
{
lean_dec(v___x_3477_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3488_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3484_; lean_object* v___x_3486_; 
v___x_3484_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3478_);
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 0, v___x_3484_);
v___x_3486_ = v___x_3482_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3484_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
else
{
return v___x_3477_;
}
}
}
else
{
return v___x_3477_;
}
}
}
else
{
lean_dec_ref(v_fallback_3440_);
lean_dec_ref(v_inst_x27_3439_);
lean_dec_ref(v_inst_3438_);
lean_dec_ref(v_h_3437_);
lean_dec_ref(v_p_x27_3436_);
lean_dec_ref(v_p_3435_);
return v___x_3457_;
}
}
else
{
lean_object* v_val_3492_; lean_object* v___x_3493_; 
lean_dec_ref(v_fallback_3440_);
v_val_3492_ = lean_ctor_get(v_a_3456_, 0);
lean_inc(v_val_3492_);
lean_dec_ref_known(v_a_3456_, 1);
v___x_3493_ = l_Lean_Meta_Sym_shareCommonInc(v_val_3492_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3508_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3496_ = v___x_3493_;
v_isShared_3497_ = v_isSharedCheck_3508_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3493_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3508_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; uint8_t v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3506_; 
v___x_3498_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__8);
v___x_3499_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__10);
lean_inc_n(v_a_3494_, 2);
v___x_3500_ = l_Lean_mkAppB(v___x_3498_, v___x_3499_, v_a_3494_);
v___x_3501_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___closed__2);
v___x_3502_ = l_Lean_mkApp7(v___x_3501_, v_p_3435_, v_p_x27_3436_, v_h_3437_, v_inst_3438_, v_inst_x27_3439_, v_a_3494_, v___x_3500_);
v___x_3503_ = 0;
v___x_3504_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3504_, 0, v_a_3494_);
lean_ctor_set(v___x_3504_, 1, v___x_3502_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*2, v___x_3503_);
lean_ctor_set_uint8(v___x_3504_, sizeof(void*)*2 + 1, v___x_3503_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 0, v___x_3504_);
v___x_3506_ = v___x_3496_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3504_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
else
{
lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3516_; 
lean_dec_ref(v_inst_x27_3439_);
lean_dec_ref(v_inst_3438_);
lean_dec_ref(v_h_3437_);
lean_dec_ref(v_p_x27_3436_);
lean_dec_ref(v_p_3435_);
v_a_3509_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3511_ = v___x_3493_;
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___x_3493_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3514_; 
if (v_isShared_3512_ == 0)
{
v___x_3514_ = v___x_3511_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3509_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
}
else
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
lean_dec_ref(v_fallback_3440_);
lean_dec_ref(v_inst_x27_3439_);
lean_dec_ref(v_inst_3438_);
lean_dec_ref(v_h_3437_);
lean_dec_ref(v_p_x27_3436_);
lean_dec_ref(v_p_3435_);
v_a_3517_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3519_ = v___x_3455_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3455_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3517_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_3435_ = stack[0].m_obj;
lean_object* v_p_x27_3436_ = stack[1].m_obj;
lean_object* v_h_3437_ = stack[2].m_obj;
lean_object* v_inst_3438_ = stack[3].m_obj;
lean_object* v_inst_x27_3439_ = stack[4].m_obj;
lean_object* v_fallback_3440_ = stack[5].m_obj;
lean_object* v_a_3441_ = stack[6].m_obj;
lean_object* v_a_3442_ = stack[7].m_obj;
lean_object* v_a_3443_ = stack[8].m_obj;
lean_object* v_a_3444_ = stack[9].m_obj;
lean_object* v_a_3445_ = stack[10].m_obj;
lean_object* v_a_3446_ = stack[11].m_obj;
lean_object* v_a_3447_ = stack[12].m_obj;
lean_object* v_a_3448_ = stack[13].m_obj;
lean_object* v_a_3449_ = stack[14].m_obj;
lean_object* v_res_3525_;
v_res_3525_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(v_p_3435_, v_p_x27_3436_, v_h_3437_, v_inst_3438_, v_inst_x27_3439_, v_fallback_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
stack->m_obj
 = v_res_3525_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___boxed(lean_object* v_p_3526_, lean_object* v_p_x27_3527_, lean_object* v_h_3528_, lean_object* v_inst_3529_, lean_object* v_inst_x27_3530_, lean_object* v_fallback_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v_res_3542_; 
v_res_3542_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(v_p_3526_, v_p_x27_3527_, v_h_3528_, v_inst_3529_, v_inst_x27_3530_, v_fallback_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_);
lean_dec(v_a_3540_);
lean_dec_ref(v_a_3539_);
lean_dec(v_a_3538_);
lean_dec_ref(v_a_3537_);
lean_dec(v_a_3536_);
lean_dec_ref(v_a_3535_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
return v_res_3542_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2(lean_object* v___x_3544_, lean_object* v_e_x27_3545_, lean_object* v_snd_3546_, lean_object* v___x_3547_, lean_object* v___x_3548_, lean_object* v___x_3549_, lean_object* v_arg_3550_, lean_object* v_proof_3551_, lean_object* v_arg_3552_, uint8_t v___x_3553_, uint8_t v_contextDependent_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l_Lean_Meta_Sym_shareCommon(v___x_3544_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_a_3566_; lean_object* v___x_3567_; 
v_a_3566_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_a_3566_);
lean_dec_ref_known(v___x_3565_, 1);
lean_inc_ref(v_snd_3546_);
lean_inc_ref(v_e_x27_3545_);
v___x_3567_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___redArg(v_a_3566_, v_e_x27_3545_, v_snd_3546_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3580_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3570_ = v___x_3567_;
v_isShared_3571_ = v_isSharedCheck_3580_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3567_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3580_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3578_; 
v___x_3572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2___closed__0));
v___x_3573_ = l_Lean_Name_mkStr3(v___x_3547_, v___x_3548_, v___x_3572_);
v___x_3574_ = l_Lean_mkConst(v___x_3573_, v___x_3549_);
v___x_3575_ = l_Lean_mkApp5(v___x_3574_, v_arg_3550_, v_e_x27_3545_, v_proof_3551_, v_arg_3552_, v_snd_3546_);
v___x_3576_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3576_, 0, v_a_3568_);
lean_ctor_set(v___x_3576_, 1, v___x_3575_);
lean_ctor_set_uint8(v___x_3576_, sizeof(void*)*2, v___x_3553_);
lean_ctor_set_uint8(v___x_3576_, sizeof(void*)*2 + 1, v_contextDependent_3554_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 0, v___x_3576_);
v___x_3578_ = v___x_3570_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3576_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec_ref(v_arg_3552_);
lean_dec_ref(v_proof_3551_);
lean_dec_ref(v_arg_3550_);
lean_dec(v___x_3549_);
lean_dec_ref(v___x_3548_);
lean_dec_ref(v___x_3547_);
lean_dec_ref(v_snd_3546_);
lean_dec_ref(v_e_x27_3545_);
v_a_3581_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3567_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3567_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
}
else
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3596_; 
lean_dec_ref(v_arg_3552_);
lean_dec_ref(v_proof_3551_);
lean_dec_ref(v_arg_3550_);
lean_dec(v___x_3549_);
lean_dec_ref(v___x_3548_);
lean_dec_ref(v___x_3547_);
lean_dec_ref(v_snd_3546_);
lean_dec_ref(v_e_x27_3545_);
v_a_3589_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3591_ = v___x_3565_;
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3565_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3596_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___x_3594_; 
if (v_isShared_3592_ == 0)
{
v___x_3594_ = v___x_3591_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v_a_3589_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3544_ = stack[0].m_obj;
lean_object* v_e_x27_3545_ = stack[1].m_obj;
lean_object* v_snd_3546_ = stack[2].m_obj;
lean_object* v___x_3547_ = stack[3].m_obj;
lean_object* v___x_3548_ = stack[4].m_obj;
lean_object* v___x_3549_ = stack[5].m_obj;
lean_object* v_arg_3550_ = stack[6].m_obj;
lean_object* v_proof_3551_ = stack[7].m_obj;
lean_object* v_arg_3552_ = stack[8].m_obj;
uint8_t v___x_3553_ = stack[9].m_num;
uint8_t v_contextDependent_3554_ = stack[10].m_num;
lean_object* v___y_3555_ = stack[11].m_obj;
lean_object* v___y_3556_ = stack[12].m_obj;
lean_object* v___y_3557_ = stack[13].m_obj;
lean_object* v___y_3558_ = stack[14].m_obj;
lean_object* v___y_3559_ = stack[15].m_obj;
lean_object* v___y_3560_ = stack[16].m_obj;
lean_object* v___y_3561_ = stack[17].m_obj;
lean_object* v___y_3562_ = stack[18].m_obj;
lean_object* v___y_3563_ = stack[19].m_obj;
lean_object* v_res_3597_;
v_res_3597_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2(v___x_3544_, v_e_x27_3545_, v_snd_3546_, v___x_3547_, v___x_3548_, v___x_3549_, v_arg_3550_, v_proof_3551_, v_arg_3552_, v___x_3553_, v_contextDependent_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
stack->m_obj
 = v_res_3597_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2___boxed(lean_object** _args){
lean_object* v___x_3598_ = _args[0];
lean_object* v_e_x27_3599_ = _args[1];
lean_object* v_snd_3600_ = _args[2];
lean_object* v___x_3601_ = _args[3];
lean_object* v___x_3602_ = _args[4];
lean_object* v___x_3603_ = _args[5];
lean_object* v_arg_3604_ = _args[6];
lean_object* v_proof_3605_ = _args[7];
lean_object* v_arg_3606_ = _args[8];
lean_object* v___x_3607_ = _args[9];
lean_object* v_contextDependent_3608_ = _args[10];
lean_object* v___y_3609_ = _args[11];
lean_object* v___y_3610_ = _args[12];
lean_object* v___y_3611_ = _args[13];
lean_object* v___y_3612_ = _args[14];
lean_object* v___y_3613_ = _args[15];
lean_object* v___y_3614_ = _args[16];
lean_object* v___y_3615_ = _args[17];
lean_object* v___y_3616_ = _args[18];
lean_object* v___y_3617_ = _args[19];
lean_object* v___y_3618_ = _args[20];
_start:
{
uint8_t v___x_20269__boxed_3619_; uint8_t v_contextDependent_20270__boxed_3620_; lean_object* v_res_3621_; 
v___x_20269__boxed_3619_ = lean_unbox(v___x_3607_);
v_contextDependent_20270__boxed_3620_ = lean_unbox(v_contextDependent_3608_);
v_res_3621_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2(v___x_3598_, v_e_x27_3599_, v_snd_3600_, v___x_3601_, v___x_3602_, v___x_3603_, v_arg_3604_, v_proof_3605_, v_arg_3606_, v___x_20269__boxed_3619_, v_contextDependent_20270__boxed_3620_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec(v___y_3609_);
return v_res_3621_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2(void){
_start:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3625_ = lean_box(0);
v___x_3626_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1));
v___x_3627_ = l_Lean_mkConst(v___x_3626_, v___x_3625_);
return v___x_3627_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3631_ = lean_box(0);
v___x_3632_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4));
v___x_3633_ = l_Lean_mkConst(v___x_3632_, v___x_3631_);
return v___x_3633_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3639_ = lean_box(0);
v___x_3640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7));
v___x_3641_ = l_Lean_mkConst(v___x_3640_, v___x_3639_);
return v___x_3641_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11(void){
_start:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3647_ = lean_box(0);
v___x_3648_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10));
v___x_3649_ = l_Lean_mkConst(v___x_3648_, v___x_3647_);
return v___x_3649_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0(uint8_t v___x_3650_, lean_object* v_e_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v___x_3665_; uint8_t v___x_3666_; 
v___x_3665_ = l_Lean_Expr_cleanupAnnotations(v_e_3651_);
v___x_3666_ = l_Lean_Expr_isApp(v___x_3665_);
if (v___x_3666_ == 0)
{
lean_dec_ref(v___x_3665_);
goto v___jp_3662_;
}
else
{
lean_object* v_arg_3667_; lean_object* v___x_3668_; uint8_t v___x_3669_; 
v_arg_3667_ = lean_ctor_get(v___x_3665_, 1);
lean_inc_ref(v_arg_3667_);
v___x_3668_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3665_);
v___x_3669_ = l_Lean_Expr_isApp(v___x_3668_);
if (v___x_3669_ == 0)
{
lean_dec_ref(v___x_3668_);
lean_dec_ref(v_arg_3667_);
goto v___jp_3662_;
}
else
{
lean_object* v_arg_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; uint8_t v___x_3675_; 
v_arg_3670_ = lean_ctor_get(v___x_3668_, 1);
lean_inc_ref(v_arg_3670_);
v___x_3671_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3668_);
v___x_3672_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___lam__0___closed__0));
v___x_3673_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__0));
v___x_3674_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__1));
v___x_3675_ = l_Lean_Expr_isConstOf(v___x_3671_, v___x_3674_);
lean_dec_ref(v___x_3671_);
if (v___x_3675_ == 0)
{
lean_dec_ref(v_arg_3670_);
lean_dec_ref(v_arg_3667_);
goto v___jp_3662_;
}
else
{
lean_object* v___x_3676_; 
lean_inc(v___y_3660_);
lean_inc_ref(v___y_3659_);
lean_inc(v___y_3658_);
lean_inc_ref(v___y_3657_);
lean_inc(v___y_3656_);
lean_inc_ref(v___y_3655_);
lean_inc(v___y_3654_);
lean_inc_ref(v___y_3653_);
lean_inc(v___y_3652_);
lean_inc_ref(v_arg_3670_);
v___x_3676_ = lean_sym_simp(v_arg_3670_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_a_3677_);
lean_dec_ref_known(v___x_3676_, 1);
if (lean_obj_tag(v_a_3677_) == 0)
{
uint8_t v_contextDependent_3678_; lean_object* v___x_3679_; 
v_contextDependent_3678_ = lean_ctor_get_uint8(v_a_3677_, 1);
lean_dec_ref_known(v_a_3677_, 0);
v___x_3679_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_arg_3670_, v___y_3655_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v_a_3680_; uint8_t v___x_3681_; 
v_a_3680_ = lean_ctor_get(v___x_3679_, 0);
lean_inc(v_a_3680_);
lean_dec_ref_known(v___x_3679_, 1);
v___x_3681_ = lean_unbox(v_a_3680_);
if (v___x_3681_ == 0)
{
lean_object* v___x_3682_; 
v___x_3682_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_3670_, v___y_3655_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_object* v_a_3683_; uint8_t v___x_3684_; 
v_a_3683_ = lean_ctor_get(v___x_3682_, 0);
lean_inc(v_a_3683_);
lean_dec_ref_known(v___x_3682_, 1);
v___x_3684_ = lean_unbox(v_a_3683_);
lean_dec(v_a_3683_);
if (v___x_3684_ == 0)
{
lean_object* v___x_3685_; lean_object* v___f_3686_; lean_object* v___x_3687_; 
lean_dec(v_a_3680_);
v___x_3685_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_3675_, v_contextDependent_3678_);
v___f_3686_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_3686_, 0, v___x_3685_);
v___x_3687_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(v_arg_3670_, v_arg_3667_, v___f_3686_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
return v___x_3687_;
}
else
{
lean_object* v___x_3688_; 
lean_dec_ref(v_arg_3670_);
v___x_3688_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_3655_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3700_; 
v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3691_ = v___x_3688_;
v_isShared_3692_ = v_isSharedCheck_3700_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3688_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3700_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; uint8_t v___x_3696_; lean_object* v___x_3698_; 
v___x_3693_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2);
v___x_3694_ = l_Lean_Expr_app___override(v___x_3693_, v_arg_3667_);
v___x_3695_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3695_, 0, v_a_3689_);
lean_ctor_set(v___x_3695_, 1, v___x_3694_);
v___x_3696_ = lean_unbox(v_a_3680_);
lean_dec(v_a_3680_);
lean_ctor_set_uint8(v___x_3695_, sizeof(void*)*2, v___x_3696_);
lean_ctor_set_uint8(v___x_3695_, sizeof(void*)*2 + 1, v_contextDependent_3678_);
if (v_isShared_3692_ == 0)
{
lean_ctor_set(v___x_3691_, 0, v___x_3695_);
v___x_3698_ = v___x_3691_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3695_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
else
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
lean_dec(v_a_3680_);
lean_dec_ref(v_arg_3667_);
v_a_3701_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___x_3688_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3688_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3701_);
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
}
else
{
lean_object* v_a_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3716_; 
lean_dec(v_a_3680_);
lean_dec_ref(v_arg_3670_);
lean_dec_ref(v_arg_3667_);
v_a_3709_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3682_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3682_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3715_; 
v_reuseFailAlloc_3715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
v___x_3714_ = v_reuseFailAlloc_3715_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
return v___x_3714_;
}
}
}
}
else
{
lean_object* v___x_3717_; 
lean_dec(v_a_3680_);
lean_dec_ref(v_arg_3670_);
v___x_3717_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_3655_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3728_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3720_ = v___x_3717_;
v_isShared_3721_ = v_isSharedCheck_3728_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3717_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3728_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3726_; 
v___x_3722_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5);
v___x_3723_ = l_Lean_Expr_app___override(v___x_3722_, v_arg_3667_);
v___x_3724_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3724_, 0, v_a_3718_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
lean_ctor_set_uint8(v___x_3724_, sizeof(void*)*2, v___x_3650_);
lean_ctor_set_uint8(v___x_3724_, sizeof(void*)*2 + 1, v_contextDependent_3678_);
if (v_isShared_3721_ == 0)
{
lean_ctor_set(v___x_3720_, 0, v___x_3724_);
v___x_3726_ = v___x_3720_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3724_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
else
{
lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3736_; 
lean_dec_ref(v_arg_3667_);
v_a_3729_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3731_ = v___x_3717_;
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v___x_3717_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
if (v_isShared_3732_ == 0)
{
v___x_3734_ = v___x_3731_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
}
}
else
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
lean_dec_ref(v_arg_3670_);
lean_dec_ref(v_arg_3667_);
v_a_3737_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v___x_3679_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3679_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_a_3737_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
}
else
{
lean_object* v_e_x27_3745_; lean_object* v_proof_3746_; uint8_t v_contextDependent_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3843_; 
v_e_x27_3745_ = lean_ctor_get(v_a_3677_, 0);
v_proof_3746_ = lean_ctor_get(v_a_3677_, 1);
v_contextDependent_3747_ = lean_ctor_get_uint8(v_a_3677_, sizeof(void*)*2 + 1);
v_isSharedCheck_3843_ = !lean_is_exclusive(v_a_3677_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3749_ = v_a_3677_;
v_isShared_3750_ = v_isSharedCheck_3843_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_proof_3746_);
lean_inc(v_e_x27_3745_);
lean_dec(v_a_3677_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3843_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3751_; 
v___x_3751_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_3745_, v___y_3655_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_a_3752_; uint8_t v___x_3753_; 
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
lean_inc(v_a_3752_);
lean_dec_ref_known(v___x_3751_, 1);
v___x_3753_ = lean_unbox(v_a_3752_);
if (v___x_3753_ == 0)
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_3745_, v___y_3655_);
lean_dec_ref(v_e_x27_3745_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; uint8_t v___x_3756_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc(v_a_3755_);
lean_dec_ref_known(v___x_3754_, 1);
v___x_3756_ = lean_unbox(v_a_3755_);
lean_dec(v_a_3755_);
if (v___x_3756_ == 0)
{
lean_object* v___x_3757_; 
lean_dec(v_a_3752_);
lean_del_object(v___x_3749_);
lean_dec_ref(v_proof_3746_);
lean_inc_ref(v_arg_3667_);
v___x_3757_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance(v_arg_3667_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_object* v_a_3758_; lean_object* v_fst_3759_; 
v_a_3758_ = lean_ctor_get(v___x_3757_, 0);
lean_inc(v_a_3758_);
lean_dec_ref_known(v___x_3757_, 1);
v_fst_3759_ = lean_ctor_get(v_a_3758_, 0);
lean_inc(v_fst_3759_);
if (lean_obj_tag(v_fst_3759_) == 0)
{
uint8_t v_contextDependent_3760_; lean_object* v___x_3761_; lean_object* v___f_3762_; lean_object* v___x_3763_; 
lean_dec(v_a_3758_);
v_contextDependent_3760_ = lean_ctor_get_uint8(v_fst_3759_, 1);
lean_dec_ref_known(v_fst_3759_, 0);
v___x_3761_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_3675_, v_contextDependent_3760_);
v___f_3762_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed), 11, 1);
lean_closure_set(v___f_3762_, 0, v___x_3761_);
v___x_3763_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(v_arg_3670_, v_arg_3667_, v___f_3762_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
return v___x_3763_;
}
else
{
lean_object* v_snd_3764_; lean_object* v_e_x27_3765_; lean_object* v_proof_3766_; uint8_t v_contextDependent_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___f_3772_; lean_object* v___x_3773_; 
v_snd_3764_ = lean_ctor_get(v_a_3758_, 1);
lean_inc_n(v_snd_3764_, 2);
lean_dec(v_a_3758_);
v_e_x27_3765_ = lean_ctor_get(v_fst_3759_, 0);
lean_inc_ref_n(v_e_x27_3765_, 2);
v_proof_3766_ = lean_ctor_get(v_fst_3759_, 1);
lean_inc_ref_n(v_proof_3766_, 2);
v_contextDependent_3767_ = lean_ctor_get_uint8(v_fst_3759_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_fst_3759_, 2);
v___x_3768_ = lean_box(0);
v___x_3769_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___closed__2);
v___x_3770_ = lean_box(v___x_3675_);
v___x_3771_ = lean_box(v_contextDependent_3767_);
lean_inc_ref(v_arg_3667_);
lean_inc_ref(v_arg_3670_);
v___f_3772_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__2___boxed), 21, 11);
lean_closure_set(v___f_3772_, 0, v___x_3769_);
lean_closure_set(v___f_3772_, 1, v_e_x27_3765_);
lean_closure_set(v___f_3772_, 2, v_snd_3764_);
lean_closure_set(v___f_3772_, 3, v___x_3672_);
lean_closure_set(v___f_3772_, 4, v___x_3673_);
lean_closure_set(v___f_3772_, 5, v___x_3768_);
lean_closure_set(v___f_3772_, 6, v_arg_3670_);
lean_closure_set(v___f_3772_, 7, v_proof_3766_);
lean_closure_set(v___f_3772_, 8, v_arg_3667_);
lean_closure_set(v___f_3772_, 9, v___x_3770_);
lean_closure_set(v___f_3772_, 10, v___x_3771_);
v___x_3773_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(v_arg_3670_, v_e_x27_3765_, v_proof_3766_, v_arg_3667_, v_snd_3764_, v___f_3772_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
return v___x_3773_;
}
}
else
{
lean_object* v_a_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3781_; 
lean_dec_ref(v_arg_3670_);
lean_dec_ref(v_arg_3667_);
v_a_3774_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3776_ = v___x_3757_;
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_a_3774_);
lean_dec(v___x_3757_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3779_; 
if (v_isShared_3777_ == 0)
{
v___x_3779_ = v___x_3776_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3774_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
}
else
{
lean_object* v___x_3782_; 
v___x_3782_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_3655_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3796_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3796_ == 0)
{
v___x_3785_ = v___x_3782_;
v_isShared_3786_ = v_isSharedCheck_3796_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3782_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3796_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3790_; 
v___x_3787_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8);
v___x_3788_ = l_Lean_mkApp3(v___x_3787_, v_arg_3670_, v_arg_3667_, v_proof_3746_);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 1, v___x_3788_);
lean_ctor_set(v___x_3749_, 0, v_a_3783_);
v___x_3790_ = v___x_3749_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3783_);
lean_ctor_set(v_reuseFailAlloc_3795_, 1, v___x_3788_);
v___x_3790_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
uint8_t v___x_3791_; lean_object* v___x_3793_; 
v___x_3791_ = lean_unbox(v_a_3752_);
lean_dec(v_a_3752_);
lean_ctor_set_uint8(v___x_3790_, sizeof(void*)*2, v___x_3791_);
lean_ctor_set_uint8(v___x_3790_, sizeof(void*)*2 + 1, v_contextDependent_3747_);
if (v_isShared_3786_ == 0)
{
lean_ctor_set(v___x_3785_, 0, v___x_3790_);
v___x_3793_ = v___x_3785_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v___x_3790_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
else
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3804_; 
lean_dec(v_a_3752_);
lean_del_object(v___x_3749_);
lean_dec_ref(v_proof_3746_);
lean_dec_ref(v_arg_3670_);
lean_dec_ref(v_arg_3667_);
v_a_3797_ = lean_ctor_get(v___x_3782_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3782_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3799_ = v___x_3782_;
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3782_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3804_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3802_; 
if (v_isShared_3800_ == 0)
{
v___x_3802_ = v___x_3799_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3797_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
}
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3812_; 
lean_dec(v_a_3752_);
lean_del_object(v___x_3749_);
lean_dec_ref(v_proof_3746_);
lean_dec_ref(v_arg_3670_);
lean_dec_ref(v_arg_3667_);
v_a_3805_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3807_ = v___x_3754_;
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3754_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3810_; 
if (v_isShared_3808_ == 0)
{
v___x_3810_ = v___x_3807_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_a_3805_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
}
else
{
lean_object* v___x_3813_; 
lean_dec(v_a_3752_);
lean_dec_ref(v_e_x27_3745_);
v___x_3813_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_3655_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3826_; 
v_a_3814_ = lean_ctor_get(v___x_3813_, 0);
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3813_);
if (v_isSharedCheck_3826_ == 0)
{
v___x_3816_ = v___x_3813_;
v_isShared_3817_ = v_isSharedCheck_3826_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3813_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3826_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3821_; 
v___x_3818_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11, &l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11_once, _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11);
v___x_3819_ = l_Lean_mkApp3(v___x_3818_, v_arg_3670_, v_arg_3667_, v_proof_3746_);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 1, v___x_3819_);
lean_ctor_set(v___x_3749_, 0, v_a_3814_);
v___x_3821_ = v___x_3749_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3814_);
lean_ctor_set(v_reuseFailAlloc_3825_, 1, v___x_3819_);
lean_ctor_set_uint8(v_reuseFailAlloc_3825_, sizeof(void*)*2 + 1, v_contextDependent_3747_);
v___x_3821_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
lean_object* v___x_3823_; 
lean_ctor_set_uint8(v___x_3821_, sizeof(void*)*2, v___x_3650_);
if (v_isShared_3817_ == 0)
{
lean_ctor_set(v___x_3816_, 0, v___x_3821_);
v___x_3823_ = v___x_3816_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v___x_3821_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
else
{
lean_object* v_a_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3834_; 
lean_del_object(v___x_3749_);
lean_dec_ref(v_proof_3746_);
lean_dec_ref(v_arg_3670_);
lean_dec_ref(v_arg_3667_);
v_a_3827_ = lean_ctor_get(v___x_3813_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3813_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3829_ = v___x_3813_;
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
else
{
lean_inc(v_a_3827_);
lean_dec(v___x_3813_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3832_; 
if (v_isShared_3830_ == 0)
{
v___x_3832_ = v___x_3829_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_a_3827_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
}
}
else
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3842_; 
lean_del_object(v___x_3749_);
lean_dec_ref(v_proof_3746_);
lean_dec_ref(v_e_x27_3745_);
lean_dec_ref(v_arg_3670_);
lean_dec_ref(v_arg_3667_);
v_a_3835_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3837_ = v___x_3751_;
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3751_);
v___x_3837_ = lean_box(0);
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
v_resetjp_3836_:
{
lean_object* v___x_3840_; 
if (v_isShared_3838_ == 0)
{
v___x_3840_ = v___x_3837_;
goto v_reusejp_3839_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3835_);
v___x_3840_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3839_;
}
v_reusejp_3839_:
{
return v___x_3840_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_arg_3670_);
lean_dec_ref(v_arg_3667_);
return v___x_3676_;
}
}
}
}
v___jp_3662_:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3663_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3663_, 0, v___x_3650_);
lean_ctor_set_uint8(v___x_3663_, 1, v___x_3650_);
v___x_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3663_);
return v___x_3664_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3650_ = stack[0].m_num;
lean_object* v_e_3651_ = stack[1].m_obj;
lean_object* v___y_3652_ = stack[2].m_obj;
lean_object* v___y_3653_ = stack[3].m_obj;
lean_object* v___y_3654_ = stack[4].m_obj;
lean_object* v___y_3655_ = stack[5].m_obj;
lean_object* v___y_3656_ = stack[6].m_obj;
lean_object* v___y_3657_ = stack[7].m_obj;
lean_object* v___y_3658_ = stack[8].m_obj;
lean_object* v___y_3659_ = stack[9].m_obj;
lean_object* v___y_3660_ = stack[10].m_obj;
lean_object* v_res_3844_;
v_res_3844_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0(v___x_3650_, v_e_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
stack->m_obj
 = v_res_3844_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___boxed(lean_object* v___x_3845_, lean_object* v_e_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
uint8_t v___x_20531__boxed_3857_; lean_object* v_res_3858_; 
v___x_20531__boxed_3857_ = lean_unbox(v___x_3845_);
v_res_3858_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0(v___x_20531__boxed_3857_, v_e_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
lean_dec(v___y_3851_);
lean_dec_ref(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
return v_res_3858_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv(lean_object* v_e_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_){
_start:
{
lean_object* v_numArgs_3870_; lean_object* v___x_3871_; uint8_t v___x_3872_; 
v_numArgs_3870_ = l_Lean_Expr_getAppNumArgs(v_e_3859_);
v___x_3871_ = lean_unsigned_to_nat(2u);
v___x_3872_ = lean_nat_dec_lt(v_numArgs_3870_, v___x_3871_);
if (v___x_3872_ == 0)
{
lean_object* v___x_3873_; lean_object* v___f_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3873_ = lean_box(v___x_3872_);
v___f_3874_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___boxed), 12, 1);
lean_closure_set(v___f_3874_, 0, v___x_3873_);
v___x_3875_ = lean_nat_sub(v_numArgs_3870_, v___x_3871_);
lean_dec(v_numArgs_3870_);
v___x_3876_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(v_e_3859_, v___x_3875_, v___f_3874_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_);
lean_dec(v___x_3875_);
return v___x_3876_;
}
else
{
uint8_t v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
lean_dec(v_numArgs_3870_);
lean_dec_ref(v_e_3859_);
v___x_3877_ = 0;
v___x_3878_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3878_, 0, v___x_3872_);
lean_ctor_set_uint8(v___x_3878_, 1, v___x_3877_);
v___x_3879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3878_);
return v___x_3879_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3859_ = stack[0].m_obj;
lean_object* v_a_3860_ = stack[1].m_obj;
lean_object* v_a_3861_ = stack[2].m_obj;
lean_object* v_a_3862_ = stack[3].m_obj;
lean_object* v_a_3863_ = stack[4].m_obj;
lean_object* v_a_3864_ = stack[5].m_obj;
lean_object* v_a_3865_ = stack[6].m_obj;
lean_object* v_a_3866_ = stack[7].m_obj;
lean_object* v_a_3867_ = stack[8].m_obj;
lean_object* v_a_3868_ = stack[9].m_obj;
lean_object* v_res_3880_;
v_res_3880_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv(v_e_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_);
stack->m_obj
 = v_res_3880_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed(lean_object* v_e_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv(v_e_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_);
lean_dec(v_a_3890_);
lean_dec_ref(v_a_3889_);
lean_dec(v_a_3888_);
lean_dec_ref(v_a_3887_);
lean_dec(v_a_3886_);
lean_dec_ref(v_a_3885_);
lean_dec(v_a_3884_);
lean_dec_ref(v_a_3883_);
lean_dec(v_a_3882_);
return v_res_3892_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_));
v___x_3909_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_));
v___x_3910_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed), 11, 0);
v___x_3911_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_3908_, v___x_3909_, v___x_3910_);
return v___x_3911_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3912_;
v_res_3912_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_();
stack->m_obj
 = v_res_3912_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14____boxed(lean_object* v_a_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_();
return v_res_3914_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_16_(){
_start:
{
lean_object* v___x_3916_; uint8_t v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3916_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__60___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_14_));
v___x_3917_ = 0;
v___x_3918_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed), 11, 0);
v___x_3919_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_3916_, v___x_3917_, v___x_3918_);
return v___x_3919_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_16__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3920_;
v_res_3920_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_16_();
stack->m_obj
 = v_res_3920_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_16____boxed(lean_object* v_a_3921_){
_start:
{
lean_object* v_res_3922_; 
v_res_3922_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_4092751164____hygCtx___hyg_16_();
return v_res_3922_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond(lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_){
_start:
{
lean_object* v___x_3934_; 
v___x_3934_ = l_Lean_Meta_Sym_Simp_simpCond(v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
return v___x_3934_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3923_ = stack[0].m_obj;
lean_object* v_a_3924_ = stack[1].m_obj;
lean_object* v_a_3925_ = stack[2].m_obj;
lean_object* v_a_3926_ = stack[3].m_obj;
lean_object* v_a_3927_ = stack[4].m_obj;
lean_object* v_a_3928_ = stack[5].m_obj;
lean_object* v_a_3929_ = stack[6].m_obj;
lean_object* v_a_3930_ = stack[7].m_obj;
lean_object* v_a_3931_ = stack[8].m_obj;
lean_object* v_a_3932_ = stack[9].m_obj;
lean_object* v_res_3935_;
v_res_3935_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond(v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_);
stack->m_obj
 = v_res_3935_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___boxed(lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond(v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_);
lean_dec(v_a_3945_);
lean_dec_ref(v_a_3944_);
lean_dec(v_a_3943_);
lean_dec_ref(v_a_3942_);
lean_dec(v_a_3941_);
lean_dec_ref(v_a_3940_);
lean_dec(v_a_3939_);
lean_dec_ref(v_a_3938_);
lean_dec(v_a_3937_);
return v_res_3947_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_(){
_start:
{
lean_object* v___f_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___f_3974_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_));
v___x_3975_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_));
v___x_3976_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_));
v___x_3977_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_3975_, v___x_3976_, v___f_3974_);
return v___x_3977_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3978_;
v_res_3978_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_();
stack->m_obj
 = v_res_3978_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16____boxed(lean_object* v_a_3979_){
_start:
{
lean_object* v_res_3980_; 
v_res_3980_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_();
return v_res_3980_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_18_(){
_start:
{
lean_object* v___f_3982_; lean_object* v___x_3983_; uint8_t v___x_3984_; lean_object* v___x_3985_; 
v___f_3982_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_));
v___x_3983_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__68___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_16_));
v___x_3984_ = 0;
v___x_3985_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_3983_, v___x_3984_, v___f_3982_);
return v___x_3985_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_18__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3986_;
v_res_3986_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_18_();
stack->m_obj
 = v_res_3986_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_18____boxed(lean_object* v_a_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_18_();
return v_res_3988_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(lean_object* v_msgData_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_){
_start:
{
lean_object* v___x_3995_; lean_object* v_env_3996_; uint8_t v___x_3997_; lean_object* v_env_3998_; lean_object* v___x_3999_; lean_object* v_toCold_4000_; lean_object* v_mctx_4001_; lean_object* v_lctx_4002_; lean_object* v_options_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_3995_ = lean_st_ref_get(v___y_3993_);
v_env_3996_ = lean_ctor_get(v___x_3995_, 0);
lean_inc_ref(v_env_3996_);
lean_dec(v___x_3995_);
v___x_3997_ = 0;
v_env_3998_ = l_Lean_Environment_setRecordingDeps(v_env_3996_, v___x_3997_);
v___x_3999_ = lean_st_ref_get(v___y_3991_);
v_toCold_4000_ = lean_ctor_get(v___y_3992_, 0);
v_mctx_4001_ = lean_ctor_get(v___x_3999_, 0);
lean_inc_ref(v_mctx_4001_);
lean_dec(v___x_3999_);
v_lctx_4002_ = lean_ctor_get(v___y_3990_, 2);
v_options_4003_ = lean_ctor_get(v_toCold_4000_, 2);
lean_inc_ref(v_options_4003_);
lean_inc_ref(v_lctx_4002_);
v___x_4004_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4004_, 0, v_env_3998_);
lean_ctor_set(v___x_4004_, 1, v_mctx_4001_);
lean_ctor_set(v___x_4004_, 2, v_lctx_4002_);
lean_ctor_set(v___x_4004_, 3, v_options_4003_);
v___x_4005_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4004_);
lean_ctor_set(v___x_4005_, 1, v_msgData_3989_);
v___x_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4005_);
return v___x_4006_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_3989_ = stack[0].m_obj;
lean_object* v___y_3990_ = stack[1].m_obj;
lean_object* v___y_3991_ = stack[2].m_obj;
lean_object* v___y_3992_ = stack[3].m_obj;
lean_object* v___y_3993_ = stack[4].m_obj;
lean_object* v_res_4007_;
v_res_4007_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(v_msgData_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
stack->m_obj
 = v_res_4007_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0___boxed(lean_object* v_msgData_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(v_msgData_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
return v_res_4014_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_4015_; double v___x_4016_; 
v___x_4015_ = lean_unsigned_to_nat(0u);
v___x_4016_ = lean_float_of_nat(v___x_4015_);
return v___x_4016_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(lean_object* v_cls_4020_, lean_object* v_msg_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v_ref_4027_; lean_object* v___x_4028_; lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4074_; 
v_ref_4027_ = lean_ctor_get(v___y_4024_, 2);
v___x_4028_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(v_msg_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4031_ = v___x_4028_;
v_isShared_4032_ = v_isSharedCheck_4074_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4028_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4074_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4033_; lean_object* v_traceState_4034_; lean_object* v_env_4035_; lean_object* v_nextMacroScope_4036_; lean_object* v_ngen_4037_; lean_object* v_auxDeclNGen_4038_; lean_object* v_cache_4039_; lean_object* v_recordedDeps_4040_; lean_object* v_messages_4041_; lean_object* v_infoState_4042_; lean_object* v_snapshotTasks_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4073_; 
v___x_4033_ = lean_st_ref_take(v___y_4025_);
v_traceState_4034_ = lean_ctor_get(v___x_4033_, 4);
v_env_4035_ = lean_ctor_get(v___x_4033_, 0);
v_nextMacroScope_4036_ = lean_ctor_get(v___x_4033_, 1);
v_ngen_4037_ = lean_ctor_get(v___x_4033_, 2);
v_auxDeclNGen_4038_ = lean_ctor_get(v___x_4033_, 3);
v_cache_4039_ = lean_ctor_get(v___x_4033_, 5);
v_recordedDeps_4040_ = lean_ctor_get(v___x_4033_, 6);
v_messages_4041_ = lean_ctor_get(v___x_4033_, 7);
v_infoState_4042_ = lean_ctor_get(v___x_4033_, 8);
v_snapshotTasks_4043_ = lean_ctor_get(v___x_4033_, 9);
v_isSharedCheck_4073_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4045_ = v___x_4033_;
v_isShared_4046_ = v_isSharedCheck_4073_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_snapshotTasks_4043_);
lean_inc(v_infoState_4042_);
lean_inc(v_messages_4041_);
lean_inc(v_recordedDeps_4040_);
lean_inc(v_cache_4039_);
lean_inc(v_traceState_4034_);
lean_inc(v_auxDeclNGen_4038_);
lean_inc(v_ngen_4037_);
lean_inc(v_nextMacroScope_4036_);
lean_inc(v_env_4035_);
lean_dec(v___x_4033_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4073_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
uint64_t v_tid_4047_; lean_object* v_traces_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4072_; 
v_tid_4047_ = lean_ctor_get_uint64(v_traceState_4034_, sizeof(void*)*1);
v_traces_4048_ = lean_ctor_get(v_traceState_4034_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v_traceState_4034_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4050_ = v_traceState_4034_;
v_isShared_4051_ = v_isSharedCheck_4072_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_traces_4048_);
lean_dec(v_traceState_4034_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4072_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; double v___x_4054_; uint8_t v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4063_; 
v___x_4052_ = lean_box(0);
v___x_4053_ = lean_box(0);
v___x_4054_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0);
v___x_4055_ = 0;
v___x_4056_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__1));
v___x_4057_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4057_, 0, v_cls_4020_);
lean_ctor_set(v___x_4057_, 1, v___x_4053_);
lean_ctor_set(v___x_4057_, 2, v___x_4056_);
lean_ctor_set_float(v___x_4057_, sizeof(void*)*3, v___x_4054_);
lean_ctor_set_float(v___x_4057_, sizeof(void*)*3 + 8, v___x_4054_);
lean_ctor_set_uint8(v___x_4057_, sizeof(void*)*3 + 16, v___x_4055_);
v___x_4058_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__2));
v___x_4059_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4057_);
lean_ctor_set(v___x_4059_, 1, v_a_4029_);
lean_ctor_set(v___x_4059_, 2, v___x_4058_);
lean_inc(v_ref_4027_);
v___x_4060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4060_, 0, v_ref_4027_);
lean_ctor_set(v___x_4060_, 1, v___x_4059_);
v___x_4061_ = l_Lean_PersistentArray_push___redArg(v_traces_4048_, v___x_4060_);
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 0, v___x_4061_);
v___x_4063_ = v___x_4050_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4061_);
lean_ctor_set_uint64(v_reuseFailAlloc_4071_, sizeof(void*)*1, v_tid_4047_);
v___x_4063_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
lean_object* v___x_4065_; 
if (v_isShared_4046_ == 0)
{
lean_ctor_set(v___x_4045_, 4, v___x_4063_);
v___x_4065_ = v___x_4045_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_env_4035_);
lean_ctor_set(v_reuseFailAlloc_4070_, 1, v_nextMacroScope_4036_);
lean_ctor_set(v_reuseFailAlloc_4070_, 2, v_ngen_4037_);
lean_ctor_set(v_reuseFailAlloc_4070_, 3, v_auxDeclNGen_4038_);
lean_ctor_set(v_reuseFailAlloc_4070_, 4, v___x_4063_);
lean_ctor_set(v_reuseFailAlloc_4070_, 5, v_cache_4039_);
lean_ctor_set(v_reuseFailAlloc_4070_, 6, v_recordedDeps_4040_);
lean_ctor_set(v_reuseFailAlloc_4070_, 7, v_messages_4041_);
lean_ctor_set(v_reuseFailAlloc_4070_, 8, v_infoState_4042_);
lean_ctor_set(v_reuseFailAlloc_4070_, 9, v_snapshotTasks_4043_);
v___x_4065_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
lean_object* v___x_4066_; lean_object* v___x_4068_; 
v___x_4066_ = lean_st_ref_put(v___y_4025_, v___x_4065_);
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 0, v___x_4052_);
v___x_4068_ = v___x_4031_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4052_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_4020_ = stack[0].m_obj;
lean_object* v_msg_4021_ = stack[1].m_obj;
lean_object* v___y_4022_ = stack[2].m_obj;
lean_object* v___y_4023_ = stack[3].m_obj;
lean_object* v___y_4024_ = stack[4].m_obj;
lean_object* v___y_4025_ = stack[5].m_obj;
lean_object* v_res_4075_;
v_res_4075_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v_cls_4020_, v_msg_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
stack->m_obj
 = v_res_4075_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___boxed(lean_object* v_cls_4076_, lean_object* v_msg_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v_res_4083_; 
v_res_4083_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v_cls_4076_, v_msg_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
return v_res_4083_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5(void){
_start:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4094_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2));
v___x_4095_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4));
v___x_4096_ = l_Lean_Name_append(v___x_4095_, v___x_4094_);
return v___x_4096_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7(void){
_start:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4098_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__6));
v___x_4099_ = l_Lean_stringToMessageData(v___x_4098_);
return v___x_4099_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9(void){
_start:
{
lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4101_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__8));
v___x_4102_ = l_Lean_stringToMessageData(v___x_4101_);
return v___x_4102_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(lean_object* v_e_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_){
_start:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; 
lean_inc_ref(v_e_4103_);
v___x_4114_ = lean_alloc_closure((void*)(l_Lean_Meta_reduceRecMatcher_x3f___boxed), 6, 1);
lean_closure_set(v___x_4114_, 0, v_e_4103_);
v___x_4115_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___x_4114_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_);
if (lean_obj_tag(v___x_4115_) == 0)
{
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4174_; 
v_a_4116_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4118_ = v___x_4115_;
v_isShared_4119_ = v_isSharedCheck_4174_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4115_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4174_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
if (lean_obj_tag(v_a_4116_) == 1)
{
lean_object* v_val_4120_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v_toCold_4147_; lean_object* v_options_4148_; uint8_t v_hasTrace_4149_; 
lean_del_object(v___x_4118_);
v_val_4120_ = lean_ctor_get(v_a_4116_, 0);
lean_inc(v_val_4120_);
lean_dec_ref_known(v_a_4116_, 1);
v_toCold_4147_ = lean_ctor_get(v_a_4111_, 0);
v_options_4148_ = lean_ctor_get(v_toCold_4147_, 2);
v_hasTrace_4149_ = lean_ctor_get_uint8(v_options_4148_, sizeof(void*)*1);
if (v_hasTrace_4149_ == 0)
{
lean_dec_ref(v_e_4103_);
v___y_4122_ = v_a_4107_;
v___y_4123_ = v_a_4108_;
v___y_4124_ = v_a_4109_;
v___y_4125_ = v_a_4110_;
v___y_4126_ = v_a_4111_;
v___y_4127_ = v_a_4112_;
goto v___jp_4121_;
}
else
{
lean_object* v_inheritedTraceOptions_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; uint8_t v___x_4153_; 
v_inheritedTraceOptions_4150_ = lean_ctor_get(v_toCold_4147_, 11);
v___x_4151_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2));
v___x_4152_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5);
v___x_4153_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4150_, v_options_4148_, v___x_4152_);
if (v___x_4153_ == 0)
{
lean_dec_ref(v_e_4103_);
v___y_4122_ = v_a_4107_;
v___y_4123_ = v_a_4108_;
v___y_4124_ = v_a_4109_;
v___y_4125_ = v_a_4110_;
v___y_4126_ = v_a_4111_;
v___y_4127_ = v_a_4112_;
goto v___jp_4121_;
}
else
{
lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4154_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7);
v___x_4155_ = l_Lean_indentExpr(v_e_4103_);
v___x_4156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4154_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
v___x_4157_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9);
v___x_4158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4156_);
lean_ctor_set(v___x_4158_, 1, v___x_4157_);
lean_inc(v_val_4120_);
v___x_4159_ = l_Lean_indentExpr(v_val_4120_);
v___x_4160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4158_);
lean_ctor_set(v___x_4160_, 1, v___x_4159_);
v___x_4161_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v___x_4151_, v___x_4160_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_);
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_dec_ref_known(v___x_4161_, 1);
v___y_4122_ = v_a_4107_;
v___y_4123_ = v_a_4108_;
v___y_4124_ = v_a_4109_;
v___y_4125_ = v_a_4110_;
v___y_4126_ = v_a_4111_;
v___y_4127_ = v_a_4112_;
goto v___jp_4121_;
}
else
{
lean_object* v_a_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4169_; 
lean_dec(v_val_4120_);
v_a_4162_ = lean_ctor_get(v___x_4161_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___x_4161_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4164_ = v___x_4161_;
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_a_4162_);
lean_dec(v___x_4161_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v___x_4167_; 
if (v_isShared_4165_ == 0)
{
v___x_4167_ = v___x_4164_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v_a_4162_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
}
}
}
v___jp_4121_:
{
lean_object* v___x_4128_; 
lean_inc(v_val_4120_);
v___x_4128_ = l_Lean_Meta_Sym_mkEqRefl(v_val_4120_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4138_; 
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4131_ = v___x_4128_;
v_isShared_4132_ = v_isSharedCheck_4138_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4128_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4138_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
uint8_t v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4136_; 
v___x_4133_ = 0;
v___x_4134_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_4134_, 0, v_val_4120_);
lean_ctor_set(v___x_4134_, 1, v_a_4129_);
lean_ctor_set_uint8(v___x_4134_, sizeof(void*)*2, v___x_4133_);
lean_ctor_set_uint8(v___x_4134_, sizeof(void*)*2 + 1, v___x_4133_);
if (v_isShared_4132_ == 0)
{
lean_ctor_set(v___x_4131_, 0, v___x_4134_);
v___x_4136_ = v___x_4131_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v___x_4134_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
else
{
lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4146_; 
lean_dec(v_val_4120_);
v_a_4139_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4141_ = v___x_4128_;
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v___x_4128_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4144_; 
if (v_isShared_4142_ == 0)
{
v___x_4144_ = v___x_4141_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_a_4139_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
}
}
else
{
lean_object* v___x_4170_; lean_object* v___x_4172_; 
lean_dec(v_a_4116_);
lean_dec_ref(v_e_4103_);
v___x_4170_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___closed__0));
if (v_isShared_4119_ == 0)
{
lean_ctor_set(v___x_4118_, 0, v___x_4170_);
v___x_4172_ = v___x_4118_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4170_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
lean_dec_ref(v_e_4103_);
v_a_4175_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4177_ = v___x_4115_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___x_4115_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4180_; 
if (v_isShared_4178_ == 0)
{
v___x_4180_ = v___x_4177_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_reduceRecMatcher_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4103_ = stack[0].m_obj;
lean_object* v_a_4104_ = stack[1].m_obj;
lean_object* v_a_4105_ = stack[2].m_obj;
lean_object* v_a_4106_ = stack[3].m_obj;
lean_object* v_a_4107_ = stack[4].m_obj;
lean_object* v_a_4108_ = stack[5].m_obj;
lean_object* v_a_4109_ = stack[6].m_obj;
lean_object* v_a_4110_ = stack[7].m_obj;
lean_object* v_a_4111_ = stack[8].m_obj;
lean_object* v_a_4112_ = stack[9].m_obj;
lean_object* v_res_4183_;
v_res_4183_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_);
stack->m_obj
 = v_res_4183_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___boxed(lean_object* v_e_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_4184_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_);
lean_dec(v_a_4193_);
lean_dec_ref(v_a_4192_);
lean_dec(v_a_4191_);
lean_dec_ref(v_a_4190_);
lean_dec(v_a_4189_);
lean_dec_ref(v_a_4188_);
lean_dec(v_a_4187_);
lean_dec_ref(v_a_4186_);
lean_dec(v_a_4185_);
return v_res_4195_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0(lean_object* v_cls_4196_, lean_object* v_msg_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v___x_4208_; 
v___x_4208_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v_cls_4196_, v_msg_4197_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
return v___x_4208_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_4196_ = stack[0].m_obj;
lean_object* v_msg_4197_ = stack[1].m_obj;
lean_object* v___y_4198_ = stack[2].m_obj;
lean_object* v___y_4199_ = stack[3].m_obj;
lean_object* v___y_4200_ = stack[4].m_obj;
lean_object* v___y_4201_ = stack[5].m_obj;
lean_object* v___y_4202_ = stack[6].m_obj;
lean_object* v___y_4203_ = stack[7].m_obj;
lean_object* v___y_4204_ = stack[8].m_obj;
lean_object* v___y_4205_ = stack[9].m_obj;
lean_object* v___y_4206_ = stack[10].m_obj;
lean_object* v_res_4209_;
v_res_4209_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0(v_cls_4196_, v_msg_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
stack->m_obj
 = v_res_4209_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___boxed(lean_object* v_cls_4210_, lean_object* v_msg_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0(v_cls_4210_, v_msg_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
return v_res_4222_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec(lean_object* v_x_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_){
_start:
{
uint8_t v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4246_ = 0;
v___x_4247_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__0));
lean_inc_ref(v_x_4235_);
v___x_4248_ = l_Lean_Meta_Sym_Simp_simpInterlaced(v_x_4235_, v___x_4247_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_);
if (lean_obj_tag(v___x_4248_) == 0)
{
lean_object* v_a_4249_; 
v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
lean_inc(v_a_4249_);
if (lean_obj_tag(v_a_4249_) == 0)
{
uint8_t v_done_4250_; 
v_done_4250_ = lean_ctor_get_uint8(v_a_4249_, 0);
if (v_done_4250_ == 0)
{
lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4263_; 
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4263_ == 0)
{
lean_object* v_unused_4264_; 
v_unused_4264_ = lean_ctor_get(v___x_4248_, 0);
lean_dec(v_unused_4264_);
v___x_4252_ = v___x_4248_;
v_isShared_4253_ = v_isSharedCheck_4263_;
goto v_resetjp_4251_;
}
else
{
lean_dec(v___x_4248_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4263_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
uint8_t v_contextDependent_4254_; lean_object* v___x_4255_; 
v_contextDependent_4254_ = lean_ctor_get_uint8(v_a_4249_, 1);
lean_dec_ref_known(v_a_4249_, 0);
v___x_4255_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_x_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_);
if (lean_obj_tag(v___x_4255_) == 0)
{
lean_object* v_a_4256_; uint8_t v___y_4258_; 
v_a_4256_ = lean_ctor_get(v___x_4255_, 0);
if (v_contextDependent_4254_ == 0)
{
lean_del_object(v___x_4252_);
return v___x_4255_;
}
else
{
lean_inc(v_a_4256_);
lean_dec_ref_known(v___x_4255_, 1);
v___y_4258_ = v___x_4246_;
goto v___jp_4257_;
}
v___jp_4257_:
{
lean_object* v___x_4259_; lean_object* v___x_4261_; 
v___x_4259_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_4256_);
if (v_isShared_4253_ == 0)
{
lean_ctor_set(v___x_4252_, 0, v___x_4259_);
v___x_4261_ = v___x_4252_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v___x_4259_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
else
{
lean_del_object(v___x_4252_);
return v___x_4255_;
}
}
}
else
{
lean_dec_ref_known(v_a_4249_, 0);
lean_dec_ref(v_x_4235_);
return v___x_4248_;
}
}
else
{
uint8_t v_done_4265_; 
v_done_4265_ = lean_ctor_get_uint8(v_a_4249_, sizeof(void*)*2);
if (v_done_4265_ == 0)
{
lean_object* v_e_x27_4266_; lean_object* v_proof_4267_; uint8_t v_contextDependent_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4314_; 
lean_dec_ref_known(v___x_4248_, 1);
v_e_x27_4266_ = lean_ctor_get(v_a_4249_, 0);
v_proof_4267_ = lean_ctor_get(v_a_4249_, 1);
v_contextDependent_4268_ = lean_ctor_get_uint8(v_a_4249_, sizeof(void*)*2 + 1);
v_isSharedCheck_4314_ = !lean_is_exclusive(v_a_4249_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4270_ = v_a_4249_;
v_isShared_4271_ = v_isSharedCheck_4314_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_proof_4267_);
lean_inc(v_e_x27_4266_);
lean_dec(v_a_4249_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4314_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___x_4272_; 
lean_inc_ref(v_e_x27_4266_);
v___x_4272_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_x27_4266_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4313_; 
v_a_4273_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4275_ = v___x_4272_;
v_isShared_4276_ = v_isSharedCheck_4313_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4272_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4313_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
if (lean_obj_tag(v_a_4273_) == 0)
{
uint8_t v___y_4278_; 
lean_dec_ref_known(v_a_4273_, 0);
lean_dec_ref(v_x_4235_);
if (v_contextDependent_4268_ == 0)
{
v___y_4278_ = v___x_4246_;
goto v___jp_4277_;
}
else
{
v___y_4278_ = v_contextDependent_4268_;
goto v___jp_4277_;
}
v___jp_4277_:
{
lean_object* v___x_4280_; 
if (v_isShared_4271_ == 0)
{
v___x_4280_ = v___x_4270_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_e_x27_4266_);
lean_ctor_set(v_reuseFailAlloc_4284_, 1, v_proof_4267_);
v___x_4280_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
lean_object* v___x_4282_; 
lean_ctor_set_uint8(v___x_4280_, sizeof(void*)*2, v___x_4246_);
lean_ctor_set_uint8(v___x_4280_, sizeof(void*)*2 + 1, v___y_4278_);
if (v_isShared_4276_ == 0)
{
lean_ctor_set(v___x_4275_, 0, v___x_4280_);
v___x_4282_ = v___x_4275_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v___x_4280_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
}
else
{
lean_object* v_e_x27_4285_; lean_object* v_proof_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4312_; 
lean_del_object(v___x_4275_);
lean_del_object(v___x_4270_);
v_e_x27_4285_ = lean_ctor_get(v_a_4273_, 0);
v_proof_4286_ = lean_ctor_get(v_a_4273_, 1);
v_isSharedCheck_4312_ = !lean_is_exclusive(v_a_4273_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4288_ = v_a_4273_;
v_isShared_4289_ = v_isSharedCheck_4312_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_proof_4286_);
lean_inc(v_e_x27_4285_);
lean_dec(v_a_4273_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4312_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4290_; 
lean_inc_ref(v_e_x27_4285_);
v___x_4290_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_x_4235_, v_e_x27_4266_, v_proof_4267_, v_e_x27_4285_, v_proof_4286_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4303_; 
v_a_4291_ = lean_ctor_get(v___x_4290_, 0);
v_isSharedCheck_4303_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4303_ == 0)
{
v___x_4293_ = v___x_4290_;
v_isShared_4294_ = v_isSharedCheck_4303_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___x_4290_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4303_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
uint8_t v___y_4296_; 
if (v_contextDependent_4268_ == 0)
{
v___y_4296_ = v___x_4246_;
goto v___jp_4295_;
}
else
{
v___y_4296_ = v_contextDependent_4268_;
goto v___jp_4295_;
}
v___jp_4295_:
{
lean_object* v___x_4298_; 
if (v_isShared_4289_ == 0)
{
lean_ctor_set(v___x_4288_, 1, v_a_4291_);
v___x_4298_ = v___x_4288_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4302_; 
v_reuseFailAlloc_4302_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_4302_, 0, v_e_x27_4285_);
lean_ctor_set(v_reuseFailAlloc_4302_, 1, v_a_4291_);
v___x_4298_ = v_reuseFailAlloc_4302_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
lean_object* v___x_4300_; 
lean_ctor_set_uint8(v___x_4298_, sizeof(void*)*2, v___x_4246_);
lean_ctor_set_uint8(v___x_4298_, sizeof(void*)*2 + 1, v___y_4296_);
if (v_isShared_4294_ == 0)
{
lean_ctor_set(v___x_4293_, 0, v___x_4298_);
v___x_4300_ = v___x_4293_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v___x_4298_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
return v___x_4300_;
}
}
}
}
}
else
{
lean_object* v_a_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4311_; 
lean_del_object(v___x_4288_);
lean_dec_ref(v_e_x27_4285_);
v_a_4304_ = lean_ctor_get(v___x_4290_, 0);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4306_ = v___x_4290_;
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_a_4304_);
lean_dec(v___x_4290_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4309_; 
if (v_isShared_4307_ == 0)
{
v___x_4309_ = v___x_4306_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4304_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_4270_);
lean_dec_ref(v_proof_4267_);
lean_dec_ref(v_e_x27_4266_);
lean_dec_ref(v_x_4235_);
return v___x_4272_;
}
}
}
else
{
lean_dec_ref_known(v_a_4249_, 2);
lean_dec_ref(v_x_4235_);
return v___x_4248_;
}
}
}
else
{
lean_dec_ref(v_x_4235_);
return v___x_4248_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4235_ = stack[0].m_obj;
lean_object* v_a_4236_ = stack[1].m_obj;
lean_object* v_a_4237_ = stack[2].m_obj;
lean_object* v_a_4238_ = stack[3].m_obj;
lean_object* v_a_4239_ = stack[4].m_obj;
lean_object* v_a_4240_ = stack[5].m_obj;
lean_object* v_a_4241_ = stack[6].m_obj;
lean_object* v_a_4242_ = stack[7].m_obj;
lean_object* v_a_4243_ = stack[8].m_obj;
lean_object* v_a_4244_ = stack[9].m_obj;
lean_object* v_res_4315_;
v_res_4315_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec(v_x_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_);
stack->m_obj
 = v_res_4315_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed(lean_object* v_x_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec(v_x_4316_, v_a_4317_, v_a_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_, v_a_4325_);
lean_dec(v_a_4325_);
lean_dec_ref(v_a_4324_);
lean_dec(v_a_4323_);
lean_dec_ref(v_a_4322_);
lean_dec(v_a_4321_);
lean_dec_ref(v_a_4320_);
lean_dec(v_a_4319_);
lean_dec_ref(v_a_4318_);
lean_dec(v_a_4317_);
return v_res_4327_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_(){
_start:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_));
v___x_4350_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_));
v___x_4351_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed), 11, 0);
v___x_4352_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_4349_, v___x_4350_, v___x_4351_);
return v___x_4352_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4353_;
v_res_4353_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_();
stack->m_obj
 = v_res_4353_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17____boxed(lean_object* v_a_4354_){
_start:
{
lean_object* v_res_4355_; 
v_res_4355_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_();
return v_res_4355_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_19_(){
_start:
{
lean_object* v___x_4357_; uint8_t v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__76___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_17_));
v___x_4358_ = 0;
v___x_4359_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed), 11, 0);
v___x_4360_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_4357_, v___x_4358_, v___x_4359_);
return v___x_4360_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_19__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4361_;
v_res_4361_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_19_();
stack->m_obj
 = v_res_4361_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_19____boxed(lean_object* v_a_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3437262075____hygCtx___hyg_19_();
return v_res_4363_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(lean_object* v_appFn_4365_, lean_object* v_e_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_){
_start:
{
lean_object* v___x_4377_; 
v___x_4377_ = l_Lean_Meta_Tactic_Cbv_getMatchTheorems(v_appFn_4365_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
lean_inc(v_a_4378_);
lean_dec_ref_known(v___x_4377_, 1);
v___x_4379_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0));
v___x_4380_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_4378_, v___x_4379_, v_e_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_);
lean_dec(v_a_4378_);
return v___x_4380_;
}
else
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4388_; 
lean_dec_ref(v_e_4366_);
v_a_4381_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4383_ = v___x_4377_;
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4377_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4386_; 
if (v_isShared_4384_ == 0)
{
v___x_4386_ = v___x_4383_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_a_4381_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
return v___x_4386_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations_0interp(lean_interpreter_value* stack)
{
lean_object* v_appFn_4365_ = stack[0].m_obj;
lean_object* v_e_4366_ = stack[1].m_obj;
lean_object* v_a_4367_ = stack[2].m_obj;
lean_object* v_a_4368_ = stack[3].m_obj;
lean_object* v_a_4369_ = stack[4].m_obj;
lean_object* v_a_4370_ = stack[5].m_obj;
lean_object* v_a_4371_ = stack[6].m_obj;
lean_object* v_a_4372_ = stack[7].m_obj;
lean_object* v_a_4373_ = stack[8].m_obj;
lean_object* v_a_4374_ = stack[9].m_obj;
lean_object* v_a_4375_ = stack[10].m_obj;
lean_object* v_res_4389_;
v_res_4389_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_appFn_4365_, v_e_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_);
stack->m_obj
 = v_res_4389_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___boxed(lean_object* v_appFn_4390_, lean_object* v_e_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_){
_start:
{
lean_object* v_res_4402_; 
v_res_4402_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_appFn_4390_, v_e_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_);
lean_dec(v_a_4400_);
lean_dec_ref(v_a_4399_);
lean_dec(v_a_4398_);
lean_dec_ref(v_a_4397_);
lean_dec(v_a_4396_);
lean_dec_ref(v_a_4395_);
lean_dec(v_a_4394_);
lean_dec_ref(v_a_4393_);
lean_dec(v_a_4392_);
return v_res_4402_;
}
}
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(lean_object* v_declName_4403_, lean_object* v___y_4404_){
_start:
{
lean_object* v___x_4406_; lean_object* v_env_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4406_ = lean_st_ref_get(v___y_4404_);
v_env_4407_ = lean_ctor_get(v___x_4406_, 0);
lean_inc_ref(v_env_4407_);
lean_dec(v___x_4406_);
v___x_4408_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_4407_, v_declName_4403_);
v___x_4409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4408_);
return v___x_4409_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_4403_ = stack[0].m_obj;
lean_object* v___y_4404_ = stack[1].m_obj;
lean_object* v_res_4410_;
v_res_4410_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(v_declName_4403_, v___y_4404_);
stack->m_obj
 = v_res_4410_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg___boxed(lean_object* v_declName_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
lean_object* v_res_4414_; 
v_res_4414_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(v_declName_4411_, v___y_4412_);
lean_dec(v___y_4412_);
return v_res_4414_;
}
}
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(lean_object* v_declName_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v___x_4426_; 
v___x_4426_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(v_declName_4415_, v___y_4424_);
return v___x_4426_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_4415_ = stack[0].m_obj;
lean_object* v___y_4416_ = stack[1].m_obj;
lean_object* v___y_4417_ = stack[2].m_obj;
lean_object* v___y_4418_ = stack[3].m_obj;
lean_object* v___y_4419_ = stack[4].m_obj;
lean_object* v___y_4420_ = stack[5].m_obj;
lean_object* v___y_4421_ = stack[6].m_obj;
lean_object* v___y_4422_ = stack[7].m_obj;
lean_object* v___y_4423_ = stack[8].m_obj;
lean_object* v___y_4424_ = stack[9].m_obj;
lean_object* v_res_4427_;
v_res_4427_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(v_declName_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
stack->m_obj
 = v_res_4427_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___boxed(lean_object* v_declName_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
lean_object* v_res_4439_; 
v_res_4439_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(v_declName_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
return v_res_4439_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2(void){
_start:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
v___x_4446_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1));
v___x_4447_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4));
v___x_4448_ = l_Lean_Name_append(v___x_4447_, v___x_4446_);
return v___x_4448_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4(void){
_start:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4450_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__3));
v___x_4451_ = l_Lean_stringToMessageData(v___x_4450_);
return v___x_4451_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6(void){
_start:
{
lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4453_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__5));
v___x_4454_ = l_Lean_stringToMessageData(v___x_4453_);
return v___x_4454_;
}
}
lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher(lean_object* v_e_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_){
_start:
{
uint8_t v___x_4466_; 
v___x_4466_ = l_Lean_Expr_isApp(v_e_4455_);
if (v___x_4466_ == 0)
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
lean_dec_ref(v_e_4455_);
v___x_4467_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_4467_, 0, v___x_4466_);
lean_ctor_set_uint8(v___x_4467_, 1, v___x_4466_);
v___x_4468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4468_, 0, v___x_4467_);
return v___x_4468_;
}
else
{
lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___x_4469_ = l_Lean_Expr_getAppFn(v_e_4455_);
v___x_4470_ = l_Lean_Expr_constName_x3f(v___x_4469_);
lean_dec_ref(v___x_4469_);
if (lean_obj_tag(v___x_4470_) == 1)
{
lean_object* v_val_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4619_; 
v_val_4471_ = lean_ctor_get(v___x_4470_, 0);
v_isSharedCheck_4619_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4473_ = v___x_4470_;
v_isShared_4474_ = v_isSharedCheck_4619_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_val_4471_);
lean_dec(v___x_4470_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4619_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v_a_4476_; lean_object* v_e_x27_4477_; lean_object* v___y_4520_; lean_object* v_a_4521_; lean_object* v___y_4524_; lean_object* v___y_4527_; lean_object* v___y_4528_; uint8_t v___y_4529_; lean_object* v___y_4533_; lean_object* v_a_4534_; lean_object* v___y_4542_; lean_object* v___x_4544_; lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4618_; 
lean_inc(v_val_4471_);
v___x_4544_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(v_val_4471_, v_a_4464_);
v_a_4545_ = lean_ctor_get(v___x_4544_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v___x_4544_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4547_ = v___x_4544_;
v_isShared_4548_ = v_isSharedCheck_4618_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_dec(v___x_4544_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4618_;
goto v_resetjp_4546_;
}
v___jp_4475_:
{
lean_object* v_toCold_4478_; lean_object* v_options_4479_; uint8_t v_hasTrace_4480_; 
v_toCold_4478_ = lean_ctor_get(v_a_4463_, 0);
v_options_4479_ = lean_ctor_get(v_toCold_4478_, 2);
v_hasTrace_4480_ = lean_ctor_get_uint8(v_options_4479_, sizeof(void*)*1);
if (v_hasTrace_4480_ == 0)
{
lean_object* v___x_4482_; 
lean_dec_ref(v_e_x27_4477_);
lean_dec(v_val_4471_);
lean_dec_ref(v_e_4455_);
if (v_isShared_4474_ == 0)
{
lean_ctor_set_tag(v___x_4473_, 0);
lean_ctor_set(v___x_4473_, 0, v_a_4476_);
v___x_4482_ = v___x_4473_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4476_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
else
{
lean_object* v_inheritedTraceOptions_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; uint8_t v___x_4487_; 
v_inheritedTraceOptions_4484_ = lean_ctor_get(v_toCold_4478_, 11);
v___x_4485_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1));
v___x_4486_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2, &l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2_once, _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2);
v___x_4487_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4484_, v_options_4479_, v___x_4486_);
if (v___x_4487_ == 0)
{
lean_object* v___x_4489_; 
lean_dec_ref(v_e_x27_4477_);
lean_dec(v_val_4471_);
lean_dec_ref(v_e_4455_);
if (v_isShared_4474_ == 0)
{
lean_ctor_set_tag(v___x_4473_, 0);
lean_ctor_set(v___x_4473_, 0, v_a_4476_);
v___x_4489_ = v___x_4473_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_a_4476_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
else
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; 
lean_del_object(v___x_4473_);
v___x_4491_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4, &l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4_once, _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4);
v___x_4492_ = l_Lean_MessageData_ofName(v_val_4471_);
v___x_4493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4491_);
lean_ctor_set(v___x_4493_, 1, v___x_4492_);
v___x_4494_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6, &l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6);
v___x_4495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4493_);
lean_ctor_set(v___x_4495_, 1, v___x_4494_);
v___x_4496_ = l_Lean_indentExpr(v_e_4455_);
v___x_4497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4497_, 0, v___x_4495_);
lean_ctor_set(v___x_4497_, 1, v___x_4496_);
v___x_4498_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9, &l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9_once, _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9);
v___x_4499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4499_, 0, v___x_4497_);
lean_ctor_set(v___x_4499_, 1, v___x_4498_);
v___x_4500_ = l_Lean_indentExpr(v_e_x27_4477_);
v___x_4501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4501_, 0, v___x_4499_);
lean_ctor_set(v___x_4501_, 1, v___x_4500_);
v___x_4502_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v___x_4485_, v___x_4501_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_);
if (lean_obj_tag(v___x_4502_) == 0)
{
lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4509_; 
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4502_);
if (v_isSharedCheck_4509_ == 0)
{
lean_object* v_unused_4510_; 
v_unused_4510_ = lean_ctor_get(v___x_4502_, 0);
lean_dec(v_unused_4510_);
v___x_4504_ = v___x_4502_;
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
else
{
lean_dec(v___x_4502_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4507_; 
if (v_isShared_4505_ == 0)
{
lean_ctor_set(v___x_4504_, 0, v_a_4476_);
v___x_4507_ = v___x_4504_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4476_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
else
{
lean_object* v_a_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4518_; 
lean_dec_ref(v_a_4476_);
v_a_4511_ = lean_ctor_get(v___x_4502_, 0);
v_isSharedCheck_4518_ = !lean_is_exclusive(v___x_4502_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4513_ = v___x_4502_;
v_isShared_4514_ = v_isSharedCheck_4518_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_a_4511_);
lean_dec(v___x_4502_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4518_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v___x_4516_; 
if (v_isShared_4514_ == 0)
{
v___x_4516_ = v___x_4513_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v_a_4511_);
v___x_4516_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
return v___x_4516_;
}
}
}
}
}
}
v___jp_4519_:
{
if (lean_obj_tag(v_a_4521_) == 1)
{
lean_object* v_e_x27_4522_; 
lean_dec_ref(v___y_4520_);
v_e_x27_4522_ = lean_ctor_get(v_a_4521_, 0);
lean_inc_ref(v_e_x27_4522_);
v_a_4476_ = v_a_4521_;
v_e_x27_4477_ = v_e_x27_4522_;
goto v___jp_4475_;
}
else
{
lean_dec_ref(v_a_4521_);
lean_del_object(v___x_4473_);
lean_dec(v_val_4471_);
lean_dec_ref(v_e_4455_);
return v___y_4520_;
}
}
v___jp_4523_:
{
if (lean_obj_tag(v___y_4524_) == 0)
{
lean_object* v_a_4525_; 
v_a_4525_ = lean_ctor_get(v___y_4524_, 0);
lean_inc(v_a_4525_);
v___y_4520_ = v___y_4524_;
v_a_4521_ = v_a_4525_;
goto v___jp_4519_;
}
else
{
lean_del_object(v___x_4473_);
lean_dec(v_val_4471_);
lean_dec_ref(v_e_4455_);
return v___y_4524_;
}
}
v___jp_4526_:
{
lean_object* v___x_4530_; lean_object* v___x_4531_; 
lean_dec_ref(v___y_4527_);
v___x_4530_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_4528_);
lean_inc_ref(v___x_4530_);
v___x_4531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4530_);
v___y_4520_ = v___x_4531_;
v_a_4521_ = v___x_4530_;
goto v___jp_4519_;
}
v___jp_4532_:
{
if (lean_obj_tag(v_a_4534_) == 0)
{
uint8_t v_done_4535_; 
v_done_4535_ = lean_ctor_get_uint8(v_a_4534_, 0);
if (v_done_4535_ == 0)
{
uint8_t v_contextDependent_4536_; lean_object* v___x_4537_; 
lean_dec_ref(v___y_4533_);
v_contextDependent_4536_ = lean_ctor_get_uint8(v_a_4534_, 1);
lean_dec_ref_known(v_a_4534_, 0);
lean_inc_ref(v_e_4455_);
v___x_4537_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_);
if (lean_obj_tag(v___x_4537_) == 0)
{
if (v_contextDependent_4536_ == 0)
{
v___y_4524_ = v___x_4537_;
goto v___jp_4523_;
}
else
{
lean_object* v_a_4538_; uint8_t v___x_4539_; 
v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
lean_inc(v_a_4538_);
v___x_4539_ = 0;
v___y_4527_ = v___x_4537_;
v___y_4528_ = v_a_4538_;
v___y_4529_ = v___x_4539_;
goto v___jp_4526_;
}
}
else
{
v___y_4524_ = v___x_4537_;
goto v___jp_4523_;
}
}
else
{
lean_dec_ref_known(v_a_4534_, 0);
lean_del_object(v___x_4473_);
lean_dec(v_val_4471_);
lean_dec_ref(v_e_4455_);
return v___y_4533_;
}
}
else
{
lean_object* v_e_x27_4540_; 
lean_dec_ref(v___y_4533_);
v_e_x27_4540_ = lean_ctor_get(v_a_4534_, 0);
lean_inc_ref(v_e_x27_4540_);
v_a_4476_ = v_a_4534_;
v_e_x27_4477_ = v_e_x27_4540_;
goto v___jp_4475_;
}
}
v___jp_4541_:
{
if (lean_obj_tag(v___y_4542_) == 0)
{
lean_object* v_a_4543_; 
v_a_4543_ = lean_ctor_get(v___y_4542_, 0);
lean_inc(v_a_4543_);
v___y_4533_ = v___y_4542_;
v_a_4534_ = v_a_4543_;
goto v___jp_4532_;
}
else
{
lean_del_object(v___x_4473_);
lean_dec(v_val_4471_);
lean_dec_ref(v_e_4455_);
return v___y_4542_;
}
}
v_resetjp_4546_:
{
if (lean_obj_tag(v_a_4545_) == 1)
{
lean_object* v_val_4549_; lean_object* v_numParams_4550_; lean_object* v_numDiscrs_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
lean_del_object(v___x_4547_);
v_val_4549_ = lean_ctor_get(v_a_4545_, 0);
lean_inc(v_val_4549_);
lean_dec_ref_known(v_a_4545_, 1);
v_numParams_4550_ = lean_ctor_get(v_val_4549_, 0);
lean_inc(v_numParams_4550_);
v_numDiscrs_4551_ = lean_ctor_get(v_val_4549_, 1);
lean_inc(v_numDiscrs_4551_);
lean_dec(v_val_4549_);
v___x_4552_ = lean_unsigned_to_nat(1u);
v___x_4553_ = lean_nat_add(v_numParams_4550_, v___x_4552_);
lean_dec(v_numParams_4550_);
v___x_4554_ = lean_nat_add(v___x_4553_, v_numDiscrs_4551_);
lean_dec(v_numDiscrs_4551_);
lean_inc_ref(v_e_4455_);
v___x_4555_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_e_4455_, v___x_4553_, v___x_4554_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_);
lean_dec(v___x_4554_);
lean_dec(v___x_4553_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v_a_4556_; 
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
lean_inc(v_a_4556_);
if (lean_obj_tag(v_a_4556_) == 0)
{
uint8_t v_done_4557_; 
v_done_4557_ = lean_ctor_get_uint8(v_a_4556_, 0);
if (v_done_4557_ == 0)
{
uint8_t v_contextDependent_4558_; lean_object* v___x_4559_; 
lean_dec_ref_known(v___x_4555_, 1);
v_contextDependent_4558_ = lean_ctor_get_uint8(v_a_4556_, 1);
lean_dec_ref_known(v_a_4556_, 0);
lean_inc_ref(v_e_4455_);
lean_inc(v_val_4471_);
v___x_4559_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_val_4471_, v_e_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_);
if (lean_obj_tag(v___x_4559_) == 0)
{
lean_object* v_a_4560_; uint8_t v___y_4562_; 
v_a_4560_ = lean_ctor_get(v___x_4559_, 0);
if (v_contextDependent_4558_ == 0)
{
v___y_4542_ = v___x_4559_;
goto v___jp_4541_;
}
else
{
if (lean_obj_tag(v_a_4560_) == 0)
{
uint8_t v_contextDependent_4572_; 
v_contextDependent_4572_ = lean_ctor_get_uint8(v_a_4560_, 1);
v___y_4562_ = v_contextDependent_4572_;
goto v___jp_4561_;
}
else
{
uint8_t v_contextDependent_4573_; 
v_contextDependent_4573_ = lean_ctor_get_uint8(v_a_4560_, sizeof(void*)*2 + 1);
v___y_4562_ = v_contextDependent_4573_;
goto v___jp_4561_;
}
}
v___jp_4561_:
{
if (v___y_4562_ == 0)
{
lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4570_; 
lean_inc(v_a_4560_);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4559_);
if (v_isSharedCheck_4570_ == 0)
{
lean_object* v_unused_4571_; 
v_unused_4571_ = lean_ctor_get(v___x_4559_, 0);
lean_dec(v_unused_4571_);
v___x_4564_ = v___x_4559_;
v_isShared_4565_ = v_isSharedCheck_4570_;
goto v_resetjp_4563_;
}
else
{
lean_dec(v___x_4559_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4570_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4566_; lean_object* v___x_4568_; 
v___x_4566_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_4560_);
lean_inc_ref(v___x_4566_);
if (v_isShared_4565_ == 0)
{
lean_ctor_set(v___x_4564_, 0, v___x_4566_);
v___x_4568_ = v___x_4564_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v___x_4566_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
v___y_4533_ = v___x_4568_;
v_a_4534_ = v___x_4566_;
goto v___jp_4532_;
}
}
}
else
{
v___y_4542_ = v___x_4559_;
goto v___jp_4541_;
}
}
}
else
{
v___y_4542_ = v___x_4559_;
goto v___jp_4541_;
}
}
else
{
lean_dec_ref_known(v_a_4556_, 0);
v___y_4542_ = v___x_4555_;
goto v___jp_4541_;
}
}
else
{
uint8_t v_done_4574_; 
v_done_4574_ = lean_ctor_get_uint8(v_a_4556_, sizeof(void*)*2);
if (v_done_4574_ == 0)
{
lean_object* v_e_x27_4575_; lean_object* v_proof_4576_; uint8_t v_contextDependent_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4613_; 
lean_dec_ref_known(v___x_4555_, 1);
v_e_x27_4575_ = lean_ctor_get(v_a_4556_, 0);
v_proof_4576_ = lean_ctor_get(v_a_4556_, 1);
v_contextDependent_4577_ = lean_ctor_get_uint8(v_a_4556_, sizeof(void*)*2 + 1);
v_isSharedCheck_4613_ = !lean_is_exclusive(v_a_4556_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4579_ = v_a_4556_;
v_isShared_4580_ = v_isSharedCheck_4613_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_proof_4576_);
lean_inc(v_e_x27_4575_);
lean_dec(v_a_4556_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4613_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4581_; 
lean_inc_ref(v_e_x27_4575_);
lean_inc(v_val_4471_);
v___x_4581_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_val_4471_, v_e_x27_4575_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_);
if (lean_obj_tag(v___x_4581_) == 0)
{
lean_object* v_a_4582_; 
v_a_4582_ = lean_ctor_get(v___x_4581_, 0);
lean_inc(v_a_4582_);
lean_dec_ref_known(v___x_4581_, 1);
if (lean_obj_tag(v_a_4582_) == 0)
{
uint8_t v_done_4583_; uint8_t v_contextDependent_4584_; uint8_t v___y_4586_; 
v_done_4583_ = lean_ctor_get_uint8(v_a_4582_, 0);
v_contextDependent_4584_ = lean_ctor_get_uint8(v_a_4582_, 1);
lean_dec_ref_known(v_a_4582_, 0);
if (v_contextDependent_4577_ == 0)
{
v___y_4586_ = v_contextDependent_4584_;
goto v___jp_4585_;
}
else
{
v___y_4586_ = v_contextDependent_4577_;
goto v___jp_4585_;
}
v___jp_4585_:
{
lean_object* v___x_4588_; 
lean_inc_ref(v_e_x27_4575_);
if (v_isShared_4580_ == 0)
{
v___x_4588_ = v___x_4579_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_e_x27_4575_);
lean_ctor_set(v_reuseFailAlloc_4589_, 1, v_proof_4576_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
lean_ctor_set_uint8(v___x_4588_, sizeof(void*)*2, v_done_4583_);
lean_ctor_set_uint8(v___x_4588_, sizeof(void*)*2 + 1, v___y_4586_);
v_a_4476_ = v___x_4588_;
v_e_x27_4477_ = v_e_x27_4575_;
goto v___jp_4475_;
}
}
}
else
{
lean_object* v_e_x27_4590_; lean_object* v_proof_4591_; uint8_t v_done_4592_; uint8_t v_contextDependent_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4612_; 
lean_del_object(v___x_4579_);
v_e_x27_4590_ = lean_ctor_get(v_a_4582_, 0);
v_proof_4591_ = lean_ctor_get(v_a_4582_, 1);
v_done_4592_ = lean_ctor_get_uint8(v_a_4582_, sizeof(void*)*2);
v_contextDependent_4593_ = lean_ctor_get_uint8(v_a_4582_, sizeof(void*)*2 + 1);
v_isSharedCheck_4612_ = !lean_is_exclusive(v_a_4582_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4595_ = v_a_4582_;
v_isShared_4596_ = v_isSharedCheck_4612_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_proof_4591_);
lean_inc(v_e_x27_4590_);
lean_dec(v_a_4582_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4612_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v___x_4597_; 
lean_inc_ref(v_e_x27_4590_);
lean_inc_ref(v_e_4455_);
v___x_4597_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_4455_, v_e_x27_4575_, v_proof_4576_, v_e_x27_4590_, v_proof_4591_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_);
if (lean_obj_tag(v___x_4597_) == 0)
{
lean_object* v_a_4598_; uint8_t v___y_4600_; 
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
lean_inc(v_a_4598_);
lean_dec_ref_known(v___x_4597_, 1);
if (v_contextDependent_4577_ == 0)
{
v___y_4600_ = v_contextDependent_4593_;
goto v___jp_4599_;
}
else
{
v___y_4600_ = v_contextDependent_4577_;
goto v___jp_4599_;
}
v___jp_4599_:
{
lean_object* v___x_4602_; 
lean_inc_ref(v_e_x27_4590_);
if (v_isShared_4596_ == 0)
{
lean_ctor_set(v___x_4595_, 1, v_a_4598_);
v___x_4602_ = v___x_4595_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_e_x27_4590_);
lean_ctor_set(v_reuseFailAlloc_4603_, 1, v_a_4598_);
lean_ctor_set_uint8(v_reuseFailAlloc_4603_, sizeof(void*)*2, v_done_4592_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
lean_ctor_set_uint8(v___x_4602_, sizeof(void*)*2 + 1, v___y_4600_);
v_a_4476_ = v___x_4602_;
v_e_x27_4477_ = v_e_x27_4590_;
goto v___jp_4475_;
}
}
}
else
{
lean_object* v_a_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4611_; 
lean_del_object(v___x_4595_);
lean_dec_ref(v_e_x27_4590_);
lean_del_object(v___x_4473_);
lean_dec(v_val_4471_);
lean_dec_ref(v_e_4455_);
v_a_4604_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4611_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4611_ == 0)
{
v___x_4606_ = v___x_4597_;
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_a_4604_);
lean_dec(v___x_4597_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4611_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
lean_object* v___x_4609_; 
if (v_isShared_4607_ == 0)
{
v___x_4609_ = v___x_4606_;
goto v_reusejp_4608_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v_a_4604_);
v___x_4609_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4608_;
}
v_reusejp_4608_:
{
return v___x_4609_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_4579_);
lean_dec_ref(v_proof_4576_);
lean_dec_ref(v_e_x27_4575_);
v___y_4542_ = v___x_4581_;
goto v___jp_4541_;
}
}
}
else
{
lean_dec_ref_known(v_a_4556_, 2);
v___y_4542_ = v___x_4555_;
goto v___jp_4541_;
}
}
}
else
{
v___y_4542_ = v___x_4555_;
goto v___jp_4541_;
}
}
else
{
lean_object* v___x_4614_; lean_object* v___x_4616_; 
lean_dec(v_a_4545_);
lean_del_object(v___x_4473_);
lean_dec(v_val_4471_);
lean_dec_ref(v_e_4455_);
v___x_4614_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___closed__0));
if (v_isShared_4548_ == 0)
{
lean_ctor_set(v___x_4547_, 0, v___x_4614_);
v___x_4616_ = v___x_4547_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v___x_4614_);
v___x_4616_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
return v___x_4616_;
}
}
}
}
}
else
{
lean_object* v___x_4620_; lean_object* v___x_4621_; 
lean_dec(v___x_4470_);
lean_dec_ref(v_e_4455_);
v___x_4620_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_rewriteDecidableInstance_spec__2___closed__0));
v___x_4621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4621_, 0, v___x_4620_);
return v___x_4621_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_Cbv_tryMatcher_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4455_ = stack[0].m_obj;
lean_object* v_a_4456_ = stack[1].m_obj;
lean_object* v_a_4457_ = stack[2].m_obj;
lean_object* v_a_4458_ = stack[3].m_obj;
lean_object* v_a_4459_ = stack[4].m_obj;
lean_object* v_a_4460_ = stack[5].m_obj;
lean_object* v_a_4461_ = stack[6].m_obj;
lean_object* v_a_4462_ = stack[7].m_obj;
lean_object* v_a_4463_ = stack[8].m_obj;
lean_object* v_a_4464_ = stack[9].m_obj;
lean_object* v_res_4622_;
v_res_4622_ = l_Lean_Meta_Tactic_Cbv_tryMatcher(v_e_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_);
stack->m_obj
 = v_res_4622_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher___boxed(lean_object* v_e_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_){
_start:
{
lean_object* v_res_4634_; 
v_res_4634_ = l_Lean_Meta_Tactic_Cbv_tryMatcher(v_e_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
lean_dec(v_a_4632_);
lean_dec_ref(v_a_4631_);
lean_dec(v_a_4630_);
lean_dec_ref(v_a_4629_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
lean_dec(v_a_4626_);
lean_dec_ref(v_a_4625_);
lean_dec(v_a_4624_);
return v_res_4634_;
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
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__26_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1644260207____hygCtx___hyg_19_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__43_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_17_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2250268465____hygCtx___hyg_19_();
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

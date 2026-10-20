// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.NormSymProcs
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.Simp.Result import Lean.Meta.Sym.Simp.App import Lean.Meta.Sym.Simp.Forall import Lean.Meta.Match.MatcherInfo import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.AbstractS import Lean.Meta.Sym.Util import Lean.Meta.Sym.Eta import Lean.Meta.Sym.InferType import Lean.Meta.Sym.SynthInstance import Lean.Meta.AppBuilder import Lean.Meta.Tactic.Grind.ForallAnd import Lean.Meta.CtorRecognizer import Init.Grind.Norm import Init.Grind.Util import Init.Grind.Lemmas import Init.ByCases
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkForallCongrFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkForallFVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Expr_getForallBody(lean_object*);
lean_object* l_Lean_Meta_Grind_forallImpAnd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpAppArgRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkCongrArg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkRflResult(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Sym_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_betaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Sym_isEtaReducible(lean_object*);
lean_object* l_Lean_Meta_Sym_etaReduce(lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Exists"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 29, 48, 135, 199, 176, 149, 70)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_hasEtaReducibleArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_hasEtaReducibleArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_NormSym_etaReduce___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Subtype"};
static const lean_object* l_Lean_Meta_Grind_NormSym_etaReduce___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_etaReduce___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_etaReduce___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_etaReduce___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 108, 3, 75, 185, 102, 103, 84)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_etaReduce___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_etaReduce___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_etaReduce___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_etaReduce___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_etaReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_etaReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PreMatchCond"};
static const lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(215, 220, 208, 216, 173, 156, 210, 29)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "simpMatchDiscrsOnly"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 129, 49, 184, 77, 13, 95, 2)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__1_value),LEAN_SCALAR_PTR_LITERAL(160, 26, 8, 228, 104, 32, 82, 85)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__3_value),LEAN_SCALAR_PTR_LITERAL(90, 191, 239, 225, 113, 224, 109, 182)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__5_value),LEAN_SCALAR_PTR_LITERAL(208, 215, 171, 150, 192, 180, 249, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__7_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__8_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__10_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__11_value),LEAN_SCALAR_PTR_LITERAL(16, 96, 65, 173, 152, 155, 4, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__12_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "eq_false_eq"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__3_value),LEAN_SCALAR_PTR_LITERAL(79, 24, 241, 157, 245, 218, 196, 160)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpEq___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__5;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpEq___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eq_true_eq"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__6_value),LEAN_SCALAR_PTR_LITERAL(100, 12, 190, 92, 208, 172, 117, 90)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpEq___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__8;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpEq___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "eq_self"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__9_value),LEAN_SCALAR_PTR_LITERAL(224, 148, 98, 216, 254, 239, 13, 169)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpEq___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__11_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__12_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpEq___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__13_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__14_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpEq___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "flip_bool_eq"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__16_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__15_value),LEAN_SCALAR_PTR_LITERAL(19, 65, 30, 112, 127, 84, 12, 55)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpEq___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__17;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpEq___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "bool_eq_to_prop"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__19_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__18_value),LEAN_SCALAR_PTR_LITERAL(79, 89, 141, 151, 119, 96, 24, 167)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpEq___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__20;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpDIte___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpDIte___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpDIte___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpDIte___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpDIte___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpDIte___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpDIte___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpDIte___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpDIte___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpDIte___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpDIte___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpDIte___closed__2_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpDIte___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpDIte___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpDIte___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "dite_eq_ite"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpDIte___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpDIte___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpDIte___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpDIte___closed__4_value),LEAN_SCALAR_PTR_LITERAL(58, 201, 242, 159, 222, 42, 9, 203)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpDIte___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpDIte___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpDIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpDIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "not_forall"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 192, 91, 90, 91, 211, 131, 26)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "not_implies"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(142, 189, 44, 77, 86, 197, 178, 67)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_pushNot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__4;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__5_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__7_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "not_ite"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__9_value),LEAN_SCALAR_PTR_LITERAL(132, 165, 120, 219, 71, 87, 242, 138)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_pushNot___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__11;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "not_eq_true"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__12_value),LEAN_SCALAR_PTR_LITERAL(225, 244, 63, 40, 164, 6, 8, 162)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_pushNot___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__14;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "not_eq_false"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__15_value),LEAN_SCALAR_PTR_LITERAL(83, 226, 87, 91, 103, 177, 77, 30)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_pushNot___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__17;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "not_eq_prop"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__19_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__18_value),LEAN_SCALAR_PTR_LITERAL(93, 9, 240, 16, 38, 110, 5, 203)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_pushNot___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__20;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "not_and"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__22_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__21_value),LEAN_SCALAR_PTR_LITERAL(239, 225, 24, 71, 205, 142, 249, 26)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_pushNot___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__23;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "not_or"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__25_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__24_value),LEAN_SCALAR_PTR_LITERAL(235, 74, 178, 162, 31, 3, 143, 38)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__25_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_pushNot___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__26;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__27_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__27_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__28_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "not_exists"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__29 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__29_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__30_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__30_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__29_value),LEAN_SCALAR_PTR_LITERAL(122, 84, 103, 56, 9, 28, 88, 199)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__30 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__30_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "not_not"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__31 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__31_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__32_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__32_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__31_value),LEAN_SCALAR_PTR_LITERAL(37, 13, 167, 116, 75, 172, 227, 19)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__32 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__32_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_pushNot___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__33;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "not_true"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__34_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__35_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__35_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__34_value),LEAN_SCALAR_PTR_LITERAL(189, 233, 184, 33, 201, 88, 141, 182)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__35_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_pushNot___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__36;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_false"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__37 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__37_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__38_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__38_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__37_value),LEAN_SCALAR_PTR_LITERAL(32, 161, 26, 17, 134, 82, 22, 22)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__38 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__38_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_pushNot___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__39;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_pushNot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_pushNot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "or_swap13"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 5, 180, 71, 127, 106, 169, 101)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "or_swap12"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(122, 217, 194, 116, 8, 17, 212, 54)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "or_true"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(42, 114, 114, 128, 39, 158, 116, 220)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "or_false"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(153, 216, 196, 245, 126, 96, 113, 194)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "or_assoc"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(177, 212, 104, 129, 180, 187, 236, 119)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "true_or"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(151, 252, 187, 232, 224, 57, 40, 42)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "false_or"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__18_value),LEAN_SCALAR_PTR_LITERAL(30, 122, 222, 214, 97, 236, 146, 97)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_NormSym_reduceCtorEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_reduceCtorEq___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_reduceCtorEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_reduceCtorEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_reduceCtorEq___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "forall_forall_or"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 112, 166, 94, 237, 48, 167, 129)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "forall_or_forall"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(121, 14, 212, 131, 198, 226, 199, 154)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpForall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "imp_self_eq"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 96, 8, 70, 216, 37, 74, 175)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpForall___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__2;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpForall___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "implies_true"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__3_value),LEAN_SCALAR_PTR_LITERAL(104, 135, 195, 91, 224, 240, 122, 198)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpForall___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "imp_false_eq"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__5_value),LEAN_SCALAR_PTR_LITERAL(217, 93, 174, 85, 201, 7, 0, 65)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpForall___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__7;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpForall___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "true_imp_eq"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__8_value),LEAN_SCALAR_PTR_LITERAL(20, 154, 121, 57, 70, 129, 111, 154)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpForall___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__10;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpForall___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "false_imp_eq"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__12_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__11_value),LEAN_SCALAR_PTR_LITERAL(127, 143, 249, 102, 140, 8, 231, 12)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpForall___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__13;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpForall___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__7_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__14_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__15_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpForall___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "forall_true"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__16_value),LEAN_SCALAR_PTR_LITERAL(87, 243, 84, 112, 33, 203, 156, 65)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpForall___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__18;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpForall___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__19;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpForall___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__20;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpForall___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "forall_false"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__21_value),LEAN_SCALAR_PTR_LITERAL(12, 96, 31, 202, 138, 131, 44, 134)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpForall___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__23;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Nonempty"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 191, 110, 220, 210, 100, 152, 183)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpExists___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "exists_const"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 209, 190, 134, 241, 243, 173, 71)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpExists___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "exists_prop"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__4_value),LEAN_SCALAR_PTR_LITERAL(210, 14, 159, 153, 168, 50, 182, 0)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpExists___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpExists___closed__6;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpExists___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "exists_and_left"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__7_value),LEAN_SCALAR_PTR_LITERAL(211, 136, 99, 9, 218, 202, 25, 69)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpExists___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "exists_and_right"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__9_value),LEAN_SCALAR_PTR_LITERAL(70, 93, 78, 251, 76, 254, 187, 237)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpExists___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "exists_or"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__12_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__11_value),LEAN_SCALAR_PTR_LITERAL(161, 112, 226, 203, 229, 162, 152, 185)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(lean_object* v_declName_1_, lean_object* v_us_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = l_Lean_Expr_const___override(v_declName_1_, v_us_2_);
v___x_6_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_5_, v___y_3_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg___boxed(lean_object* v_declName_7_, lean_object* v_us_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v_declName_7_, v_us_8_, v___y_9_);
lean_dec(v___y_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0(lean_object* v_declName_12_, lean_object* v_us_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v_declName_12_, v_us_13_, v___y_18_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___boxed(lean_object* v_declName_25_, lean_object* v_us_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0(v_declName_25_, v_us_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
lean_dec(v___y_31_);
lean_dec_ref(v___y_30_);
lean_dec(v___y_29_);
lean_dec_ref(v___y_28_);
lean_dec(v___y_27_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(lean_object* v_f_38_, lean_object* v_a_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v___y_48_; lean_object* v___x_51_; uint8_t v_debug_52_; 
v___x_51_ = lean_st_ref_get(v___y_41_);
v_debug_52_ = lean_ctor_get_uint8(v___x_51_, sizeof(void*)*12);
lean_dec(v___x_51_);
if (v_debug_52_ == 0)
{
v___y_48_ = v___y_41_;
goto v___jp_47_;
}
else
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_38_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
if (lean_obj_tag(v___x_53_) == 0)
{
lean_object* v___x_54_; 
lean_dec_ref_known(v___x_53_, 1);
v___x_54_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_dec_ref_known(v___x_54_, 1);
v___y_48_ = v___y_41_;
goto v___jp_47_;
}
else
{
lean_object* v_a_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_62_; 
lean_dec_ref(v_a_39_);
lean_dec_ref(v_f_38_);
v_a_55_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_62_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_62_ == 0)
{
v___x_57_ = v___x_54_;
v_isShared_58_ = v_isSharedCheck_62_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_a_55_);
lean_dec(v___x_54_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_62_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_60_; 
if (v_isShared_58_ == 0)
{
v___x_60_ = v___x_57_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_a_55_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
}
}
else
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_70_; 
lean_dec_ref(v_a_39_);
lean_dec_ref(v_f_38_);
v_a_63_ = lean_ctor_get(v___x_53_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_53_);
if (v_isSharedCheck_70_ == 0)
{
v___x_65_ = v___x_53_;
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_53_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_70_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_68_; 
if (v_isShared_66_ == 0)
{
v___x_68_ = v___x_65_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_a_63_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
}
v___jp_47_:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = l_Lean_Expr_app___override(v_f_38_, v_a_39_);
v___x_50_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_49_, v___y_48_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg___boxed(lean_object* v_f_71_, lean_object* v_a_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_f_71_, v_a_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec(v___y_76_);
lean_dec_ref(v___y_75_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1(lean_object* v_f_81_, lean_object* v_a_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_f_81_, v_a_82_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___boxed(lean_object* v_f_94_, lean_object* v_a_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1(v_f_94_, v_a_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(lean_object* v_p_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS___closed__1));
v___x_122_ = lean_box(0);
v___x_123_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v___x_121_, v___x_122_, v_a_115_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v_a_124_; lean_object* v___x_125_; 
v_a_124_ = lean_ctor_get(v___x_123_, 0);
lean_inc(v_a_124_);
lean_dec_ref_known(v___x_123_, 1);
v___x_125_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_a_124_, v_p_110_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_);
return v___x_125_;
}
else
{
lean_dec_ref(v_p_110_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS___boxed(lean_object* v_p_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_p_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec(v_a_129_);
lean_dec_ref(v_a_128_);
lean_dec(v_a_127_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(lean_object* v_f_138_, lean_object* v_a_u2081_139_, lean_object* v_a_u2082_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_f_138_, v_a_u2081_139_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_149_; lean_object* v___x_150_; 
v_a_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_a_149_);
lean_dec_ref_known(v___x_148_, 1);
v___x_150_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_a_149_, v_a_u2082_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
return v___x_150_;
}
else
{
lean_dec_ref(v_a_u2082_140_);
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg___boxed(lean_object* v_f_151_, lean_object* v_a_u2081_152_, lean_object* v_a_u2082_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v_f_151_, v_a_u2081_152_, v_a_u2082_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
lean_dec(v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(lean_object* v_p_165_, lean_object* v_q_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS___closed__1));
v___x_178_ = lean_box(0);
v___x_179_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v___x_177_, v___x_178_, v_a_171_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_181_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_179_, 1);
v___x_181_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v_a_180_, v_p_165_, v_q_166_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
return v___x_181_;
}
else
{
lean_dec_ref(v_q_166_);
lean_dec_ref(v_p_165_);
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS___boxed(lean_object* v_p_182_, lean_object* v_q_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v_p_182_, v_q_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0(lean_object* v_f_195_, lean_object* v_a_u2081_196_, lean_object* v_a_u2082_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v_f_195_, v_a_u2081_196_, v_a_u2082_197_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___boxed(lean_object* v_f_209_, lean_object* v_a_u2081_210_, lean_object* v_a_u2082_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0(v_f_209_, v_a_u2081_210_, v_a_u2082_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(lean_object* v_p_226_, lean_object* v_q_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1));
v___x_236_ = lean_box(0);
v___x_237_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v___x_235_, v___x_236_, v_a_229_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_object* v_a_238_; lean_object* v___x_239_; 
v_a_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_a_238_);
lean_dec_ref_known(v___x_237_, 1);
v___x_239_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v_a_238_, v_p_226_, v_q_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
return v___x_239_;
}
else
{
lean_dec_ref(v_q_227_);
lean_dec_ref(v_p_226_);
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___boxed(lean_object* v_p_240_, lean_object* v_q_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_p_240_, v_q_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS(lean_object* v_p_250_, lean_object* v_q_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_p_250_, v_q_251_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___boxed(lean_object* v_p_263_, lean_object* v_q_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS(v_p_263_, v_q_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
lean_dec(v_a_271_);
lean_dec_ref(v_a_270_);
lean_dec(v_a_269_);
lean_dec_ref(v_a_268_);
lean_dec(v_a_267_);
lean_dec_ref(v_a_266_);
lean_dec(v_a_265_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg(lean_object* v_u_279_, lean_object* v_00_u03b1_280_, lean_object* v_p_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_289_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg___closed__1));
v___x_290_ = lean_box(0);
v___x_291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_291_, 0, v_u_279_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v___x_289_, v___x_291_, v_a_283_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_294_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
lean_inc(v_a_293_);
lean_dec_ref_known(v___x_292_, 1);
v___x_294_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v_a_293_, v_00_u03b1_280_, v_p_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_);
return v___x_294_;
}
else
{
lean_dec_ref(v_p_281_);
lean_dec_ref(v_00_u03b1_280_);
return v___x_292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg___boxed(lean_object* v_u_295_, lean_object* v_00_u03b1_296_, lean_object* v_p_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg(v_u_295_, v_00_u03b1_296_, v_p_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS(lean_object* v_u_306_, lean_object* v_00_u03b1_307_, lean_object* v_p_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg(v_u_306_, v_00_u03b1_307_, v_p_308_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___boxed(lean_object* v_u_320_, lean_object* v_00_u03b1_321_, lean_object* v_p_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS(v_u_320_, v_00_u03b1_321_, v_p_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_a_323_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___redArg(lean_object* v_e_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
if (lean_obj_tag(v_e_336_) == 10)
{
lean_object* v_expr_344_; lean_object* v___x_345_; 
v_expr_344_ = lean_ctor_get(v_e_336_, 1);
lean_inc_ref_n(v_expr_344_, 2);
lean_dec_ref_known(v_e_336_, 2);
v___x_345_ = l_Lean_Meta_Sym_mkEqRefl(v_expr_344_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_355_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_355_ == 0)
{
v___x_348_ = v___x_345_;
v_isShared_349_ = v_isSharedCheck_355_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_345_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_355_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
uint8_t v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_350_ = 0;
v___x_351_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_351_, 0, v_expr_344_);
lean_ctor_set(v___x_351_, 1, v_a_346_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*2, v___x_350_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*2 + 1, v___x_350_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 0, v___x_351_);
v___x_353_ = v___x_348_;
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
lean_dec_ref(v_expr_344_);
v_a_356_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_345_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_345_);
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
else
{
lean_object* v___x_364_; lean_object* v___x_365_; 
lean_dec_ref(v_e_336_);
v___x_364_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___redArg___boxed(lean_object* v_e_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v_e_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData(lean_object* v_e_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v_e_375_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___boxed(lean_object* v_e_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Meta_Grind_NormSym_eraseMData(v_e_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
return v_res_398_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_hasEtaReducibleArg(lean_object* v_a_399_){
_start:
{
if (lean_obj_tag(v_a_399_) == 5)
{
lean_object* v_fn_400_; lean_object* v_arg_401_; uint8_t v___x_402_; 
v_fn_400_ = lean_ctor_get(v_a_399_, 0);
v_arg_401_ = lean_ctor_get(v_a_399_, 1);
v___x_402_ = l_Lean_Meta_Sym_isEtaReducible(v_arg_401_);
if (v___x_402_ == 0)
{
v_a_399_ = v_fn_400_;
goto _start;
}
else
{
return v___x_402_;
}
}
else
{
uint8_t v___x_404_; 
v___x_404_ = 0;
return v___x_404_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_hasEtaReducibleArg___boxed(lean_object* v_a_405_){
_start:
{
uint8_t v_res_406_; lean_object* v_r_407_; 
v_res_406_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_hasEtaReducibleArg(v_a_405_);
lean_dec_ref(v_a_405_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go___redArg(lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
if (lean_obj_tag(v_a_408_) == 5)
{
lean_object* v_fn_416_; lean_object* v_arg_417_; lean_object* v___x_418_; 
v_fn_416_ = lean_ctor_get(v_a_408_, 0);
lean_inc_ref(v_fn_416_);
v_arg_417_ = lean_ctor_get(v_a_408_, 1);
lean_inc_ref(v_arg_417_);
lean_dec_ref_known(v_a_408_, 2);
v___x_418_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go___redArg(v_fn_416_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref_known(v___x_418_, 1);
v___x_420_ = l_Lean_Meta_Sym_etaReduce(v_arg_417_);
lean_dec_ref(v_arg_417_);
v___x_421_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_a_419_, v___x_420_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
return v___x_421_;
}
else
{
lean_dec_ref(v_arg_417_);
return v___x_418_;
}
}
else
{
lean_object* v___x_422_; 
v___x_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_422_, 0, v_a_408_);
return v___x_422_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go___redArg___boxed(lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go___redArg(v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go(lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go___redArg(v_a_432_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go___boxed(lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go(v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
lean_dec(v_a_449_);
lean_dec_ref(v_a_448_);
lean_dec(v_a_447_);
lean_dec_ref(v_a_446_);
lean_dec(v_a_445_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_etaReduce___redArg(lean_object* v_e_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; uint8_t v___x_509_; 
v___x_509_ = l_Lean_Expr_isApp(v_e_459_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec_ref(v_e_459_);
v___x_510_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_510_, 0, v___x_509_);
lean_ctor_set_uint8(v___x_510_, 1, v___x_509_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
else
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_Expr_getAppFn(v_e_459_);
if (lean_obj_tag(v___x_512_) == 4)
{
lean_object* v_declName_513_; lean_object* v___x_514_; uint8_t v___x_515_; 
v_declName_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_declName_513_);
lean_dec_ref_known(v___x_512_, 2);
v___x_514_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg___closed__1));
v___x_515_ = lean_name_eq(v_declName_513_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_516_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_etaReduce___redArg___closed__1));
v___x_517_ = lean_name_eq(v_declName_513_, v___x_516_);
lean_dec(v_declName_513_);
if (v___x_517_ == 0)
{
v___y_468_ = v_a_460_;
v___y_469_ = v_a_461_;
v___y_470_ = v_a_462_;
v___y_471_ = v_a_463_;
v___y_472_ = v_a_464_;
v___y_473_ = v_a_465_;
goto v___jp_467_;
}
else
{
lean_dec_ref(v_e_459_);
goto v___jp_506_;
}
}
else
{
lean_dec(v_declName_513_);
lean_dec_ref(v_e_459_);
goto v___jp_506_;
}
}
else
{
lean_dec_ref(v___x_512_);
v___y_468_ = v_a_460_;
v___y_469_ = v_a_461_;
v___y_470_ = v_a_462_;
v___y_471_ = v_a_463_;
v___y_472_ = v_a_464_;
v___y_473_ = v_a_465_;
goto v___jp_467_;
}
}
v___jp_467_:
{
uint8_t v___x_474_; 
v___x_474_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_hasEtaReducibleArg(v_e_459_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; 
lean_dec_ref(v_e_459_);
v___x_475_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_475_, 0, v___x_474_);
lean_ctor_set_uint8(v___x_475_, 1, v___x_474_);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
else
{
lean_object* v___x_477_; 
v___x_477_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go___redArg(v_e_459_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_479_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc_n(v_a_478_, 2);
lean_dec_ref_known(v___x_477_, 1);
v___x_479_ = l_Lean_Meta_Sym_mkEqRefl(v_a_478_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_489_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_489_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_489_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_489_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
uint8_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_484_ = 0;
v___x_485_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_485_, 0, v_a_478_);
lean_ctor_set(v___x_485_, 1, v_a_480_);
lean_ctor_set_uint8(v___x_485_, sizeof(void*)*2, v___x_484_);
lean_ctor_set_uint8(v___x_485_, sizeof(void*)*2 + 1, v___x_484_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_485_);
v___x_487_ = v___x_482_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
lean_dec(v_a_478_);
v_a_490_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_479_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_479_);
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
v_a_498_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_477_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_477_);
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
}
v___jp_506_:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
return v___x_508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_etaReduce___redArg___boxed(lean_object* v_e_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_Meta_Grind_NormSym_etaReduce___redArg(v_e_518_, v_a_519_, v_a_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
lean_dec(v_a_524_);
lean_dec_ref(v_a_523_);
lean_dec(v_a_522_);
lean_dec_ref(v_a_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_etaReduce(lean_object* v_e_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Meta_Grind_NormSym_etaReduce___redArg(v_e_527_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_etaReduce___boxed(lean_object* v_e_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_Meta_Grind_NormSym_etaReduce(v_e_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(lean_object* v_e_558_){
_start:
{
lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_563_ = l_Lean_Expr_cleanupAnnotations(v_e_558_);
v___x_564_ = l_Lean_Expr_isApp(v___x_563_);
if (v___x_564_ == 0)
{
lean_dec_ref(v___x_563_);
goto v___jp_560_;
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_565_ = l_Lean_Expr_appFnCleanup___redArg(v___x_563_);
v___x_566_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__3));
v___x_567_ = l_Lean_Expr_isConstOf(v___x_565_, v___x_566_);
lean_dec_ref(v___x_565_);
if (v___x_567_ == 0)
{
goto v___jp_560_;
}
else
{
uint8_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_568_ = 0;
v___x_569_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_567_, v___x_568_);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
v___jp_560_:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___boxed(lean_object* v_e_571_, lean_object* v_a_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(v_e_571_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond(lean_object* v_e_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(v_e_574_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___boxed(lean_object* v_e_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_Meta_Grind_NormSym_preMatchCond(v_e_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
lean_dec(v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
lean_dec(v_a_589_);
lean_dec_ref(v_a_588_);
lean_dec(v_a_587_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(lean_object* v_declName_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___x_601_; lean_object* v_env_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_601_ = lean_st_ref_get(v___y_599_);
v_env_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc_ref(v_env_602_);
lean_dec(v___x_601_);
v___x_603_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_602_, v_declName_598_);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg___boxed(lean_object* v_declName_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(v_declName_605_, v___y_606_);
lean_dec(v___y_606_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0(lean_object* v_declName_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v___x_620_; 
v___x_620_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(v_declName_609_, v___y_618_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___boxed(lean_object* v_declName_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0(v_declName_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(lean_object* v_e_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
if (lean_obj_tag(v_e_638_) == 5)
{
lean_object* v_fn_652_; lean_object* v_arg_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v_fn_652_ = lean_ctor_get(v_e_638_, 0);
lean_inc_ref(v_fn_652_);
v_arg_653_ = lean_ctor_get(v_e_638_, 1);
lean_inc_ref(v_arg_653_);
lean_inc_ref(v_e_638_);
v___x_654_ = l_Lean_Expr_cleanupAnnotations(v_e_638_);
v___x_655_ = l_Lean_Expr_isApp(v___x_654_);
if (v___x_655_ == 0)
{
lean_dec_ref(v___x_654_);
lean_dec_ref(v_arg_653_);
lean_dec_ref_known(v_e_638_, 2);
lean_dec_ref(v_fn_652_);
goto v___jp_649_;
}
else
{
lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_656_ = l_Lean_Expr_appFnCleanup___redArg(v___x_654_);
v___x_657_ = l_Lean_Expr_isApp(v___x_656_);
if (v___x_657_ == 0)
{
lean_dec_ref(v___x_656_);
lean_dec_ref(v_arg_653_);
lean_dec_ref_known(v_e_638_, 2);
lean_dec_ref(v_fn_652_);
goto v___jp_649_;
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_658_ = l_Lean_Expr_appFnCleanup___redArg(v___x_656_);
v___x_659_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___closed__1));
v___x_660_ = l_Lean_Expr_isConstOf(v___x_658_, v___x_659_);
lean_dec_ref(v___x_658_);
if (v___x_660_ == 0)
{
lean_dec_ref(v_arg_653_);
lean_dec_ref_known(v_e_638_, 2);
lean_dec_ref(v_fn_652_);
goto v___jp_649_;
}
else
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_Expr_getAppFn(v_arg_653_);
if (lean_obj_tag(v___x_661_) == 4)
{
lean_object* v_declName_662_; lean_object* v___x_663_; lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_705_; 
v_declName_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_declName_662_);
lean_dec_ref_known(v___x_661_, 2);
v___x_663_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(v_declName_662_, v_a_647_);
v_a_664_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_705_ == 0)
{
v___x_666_ = v___x_663_;
v_isShared_667_ = v_isSharedCheck_705_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_705_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
if (lean_obj_tag(v_a_664_) == 1)
{
lean_object* v_val_668_; lean_object* v_numParams_669_; lean_object* v_numDiscrs_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
lean_del_object(v___x_666_);
v_val_668_ = lean_ctor_get(v_a_664_, 0);
lean_inc(v_val_668_);
lean_dec_ref_known(v_a_664_, 1);
v_numParams_669_ = lean_ctor_get(v_val_668_, 0);
lean_inc(v_numParams_669_);
v_numDiscrs_670_ = lean_ctor_get(v_val_668_, 1);
lean_inc(v_numDiscrs_670_);
lean_dec(v_val_668_);
v___x_671_ = lean_unsigned_to_nat(1u);
v___x_672_ = lean_nat_add(v_numParams_669_, v___x_671_);
lean_dec(v_numParams_669_);
v___x_673_ = lean_nat_add(v___x_672_, v_numDiscrs_670_);
lean_dec(v_numDiscrs_670_);
lean_inc_ref(v_arg_653_);
v___x_674_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_arg_653_, v___x_672_, v___x_673_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
lean_dec(v___x_673_);
lean_dec(v___x_672_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_676_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_674_, 1);
v___x_676_ = l_Lean_Meta_Sym_Simp_mkCongrArg___redArg(v_e_638_, v_fn_652_, v_arg_653_, v_a_675_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_699_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_699_ == 0)
{
v___x_679_ = v___x_676_;
v_isShared_680_ = v_isSharedCheck_699_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_676_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_699_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
if (lean_obj_tag(v_a_677_) == 0)
{
uint8_t v_contextDependent_681_; lean_object* v___x_682_; lean_object* v___x_684_; 
v_contextDependent_681_ = lean_ctor_get_uint8(v_a_677_, 1);
lean_dec_ref_known(v_a_677_, 0);
v___x_682_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_660_, v_contextDependent_681_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v___x_682_);
v___x_684_ = v___x_679_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
else
{
lean_object* v_e_x27_686_; lean_object* v_proof_687_; uint8_t v_contextDependent_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_698_; 
v_e_x27_686_ = lean_ctor_get(v_a_677_, 0);
v_proof_687_ = lean_ctor_get(v_a_677_, 1);
v_contextDependent_688_ = lean_ctor_get_uint8(v_a_677_, sizeof(void*)*2 + 1);
v_isSharedCheck_698_ = !lean_is_exclusive(v_a_677_);
if (v_isSharedCheck_698_ == 0)
{
v___x_690_ = v_a_677_;
v_isShared_691_ = v_isSharedCheck_698_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_proof_687_);
lean_inc(v_e_x27_686_);
lean_dec(v_a_677_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_698_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_e_x27_686_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_proof_687_);
lean_ctor_set_uint8(v_reuseFailAlloc_697_, sizeof(void*)*2 + 1, v_contextDependent_688_);
v___x_693_ = v_reuseFailAlloc_697_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_695_; 
lean_ctor_set_uint8(v___x_693_, sizeof(void*)*2, v___x_660_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 0, v___x_693_);
v___x_695_ = v___x_679_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
}
else
{
return v___x_676_;
}
}
else
{
lean_dec_ref(v_arg_653_);
lean_dec_ref_known(v_e_638_, 2);
lean_dec_ref(v_fn_652_);
return v___x_674_;
}
}
else
{
uint8_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
lean_dec(v_a_664_);
lean_dec_ref(v_arg_653_);
lean_dec_ref(v_fn_652_);
lean_dec_ref_known(v_e_638_, 2);
v___x_700_ = 0;
v___x_701_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_660_, v___x_700_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 0, v___x_701_);
v___x_703_ = v___x_666_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
else
{
uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
lean_dec_ref(v___x_661_);
lean_dec_ref(v_arg_653_);
lean_dec_ref_known(v_e_638_, 2);
lean_dec_ref(v_fn_652_);
v___x_706_ = 0;
v___x_707_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_660_, v___x_706_);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
return v___x_708_;
}
}
}
}
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec_ref(v_e_638_);
v___x_709_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
v___jp_649_:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___boxed(lean_object* v_e_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(v_e_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
return v_res_722_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(lean_object* v_declName_746_){
_start:
{
lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_747_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__2));
v___x_748_ = lean_name_eq(v_declName_746_, v___x_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__4));
v___x_750_ = lean_name_eq(v_declName_746_, v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; uint8_t v___x_752_; 
v___x_751_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__6));
v___x_752_ = lean_name_eq(v_declName_746_, v___x_751_);
if (v___x_752_ == 0)
{
lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__9));
v___x_754_ = lean_name_eq(v_declName_746_, v___x_753_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__12));
v___x_756_ = lean_name_eq(v_declName_746_, v___x_755_);
return v___x_756_;
}
else
{
return v___x_754_;
}
}
else
{
return v___x_752_;
}
}
else
{
return v___x_750_;
}
}
else
{
return v___x_748_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___boxed(lean_object* v_declName_757_){
_start:
{
uint8_t v_res_758_; lean_object* v_r_759_; 
v_res_758_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(v_declName_757_);
lean_dec(v_declName_757_);
v_r_759_ = lean_box(v_res_758_);
return v_r_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(lean_object* v_u_760_, lean_object* v___y_761_){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = l_Lean_Expr_sort___override(v_u_760_);
v___x_764_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_763_, v___y_761_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg___boxed(lean_object* v_u_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v_u_765_, v___y_766_);
lean_dec(v___y_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1(lean_object* v_u_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v_u_769_, v___y_774_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___boxed(lean_object* v_u_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1(v_u_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(lean_object* v_f_793_, lean_object* v_a_u2081_794_, lean_object* v_a_u2082_795_, lean_object* v_a_u2083_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v_f_793_, v_a_u2081_794_, v_a_u2082_795_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_806_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref_known(v___x_804_, 1);
v___x_806_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_a_805_, v_a_u2083_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
return v___x_806_;
}
else
{
lean_dec_ref(v_a_u2083_796_);
return v___x_804_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg___boxed(lean_object* v_f_807_, lean_object* v_a_u2081_808_, lean_object* v_a_u2082_809_, lean_object* v_a_u2083_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v_f_807_, v_a_u2081_808_, v_a_u2082_809_, v_a_u2083_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
return v_res_818_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__5(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_box(0);
v___x_830_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__4));
v___x_831_ = l_Lean_mkConst(v___x_830_, v___x_829_);
return v___x_831_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__8(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_837_ = lean_box(0);
v___x_838_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__7));
v___x_839_ = l_Lean_mkConst(v___x_838_, v___x_837_);
return v___x_839_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__17(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_856_ = lean_box(0);
v___x_857_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__16));
v___x_858_ = l_Lean_mkConst(v___x_857_, v___x_856_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__20(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_864_ = lean_box(0);
v___x_865_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__19));
v___x_866_ = l_Lean_mkConst(v___x_865_, v___x_864_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpEq(lean_object* v_e_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_881_ = l_Lean_Expr_cleanupAnnotations(v_e_867_);
v___x_882_ = l_Lean_Expr_isApp(v___x_881_);
if (v___x_882_ == 0)
{
lean_dec_ref(v___x_881_);
goto v___jp_878_;
}
else
{
lean_object* v_arg_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v_arg_883_ = lean_ctor_get(v___x_881_, 1);
lean_inc_ref(v_arg_883_);
v___x_884_ = l_Lean_Expr_appFnCleanup___redArg(v___x_881_);
v___x_885_ = l_Lean_Expr_isApp(v___x_884_);
if (v___x_885_ == 0)
{
lean_dec_ref(v___x_884_);
lean_dec_ref(v_arg_883_);
goto v___jp_878_;
}
else
{
lean_object* v_arg_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v_arg_886_ = lean_ctor_get(v___x_884_, 1);
lean_inc_ref(v_arg_886_);
v___x_887_ = l_Lean_Expr_appFnCleanup___redArg(v___x_884_);
v___x_888_ = l_Lean_Expr_isApp(v___x_887_);
if (v___x_888_ == 0)
{
lean_dec_ref(v___x_887_);
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
goto v___jp_878_;
}
else
{
lean_object* v_arg_889_; lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; 
v_arg_889_ = lean_ctor_get(v___x_887_, 1);
lean_inc_ref(v_arg_889_);
v___x_890_ = l_Lean_Expr_appFnCleanup___redArg(v___x_887_);
v___x_891_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__1));
v___x_892_ = l_Lean_Expr_isConstOf(v___x_890_, v___x_891_);
if (v___x_892_ == 0)
{
lean_dec_ref(v___x_890_);
lean_dec_ref(v_arg_889_);
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
goto v___jp_878_;
}
else
{
lean_object* v___x_893_; 
lean_inc_ref(v_arg_889_);
v___x_893_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_889_, v_a_874_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_1060_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_896_ = v___x_893_;
v_isShared_897_ = v_isSharedCheck_1060_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_893_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_1060_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_903_ = l_Lean_Expr_cleanupAnnotations(v_a_894_);
v___x_904_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__2));
v___x_905_ = l_Lean_Expr_isConstOf(v___x_903_, v___x_904_);
lean_dec_ref(v___x_903_);
if (v___x_905_ == 0)
{
size_t v___x_906_; size_t v___x_907_; uint8_t v___x_908_; 
lean_del_object(v___x_896_);
v___x_906_ = lean_ptr_addr(v_arg_886_);
v___x_907_ = lean_ptr_addr(v_arg_883_);
v___x_908_ = lean_usize_dec_eq(v___x_906_, v___x_907_);
if (v___x_908_ == 0)
{
uint8_t v___x_909_; 
lean_dec_ref(v___x_890_);
lean_dec_ref(v_arg_889_);
lean_inc_ref(v_arg_883_);
v___x_909_ = l_Lean_Expr_isTrue(v_arg_883_);
if (v___x_909_ == 0)
{
uint8_t v___x_910_; 
v___x_910_ = l_Lean_Expr_isFalse(v_arg_883_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; 
lean_dec_ref(v_arg_886_);
v___x_911_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_911_, 0, v___x_910_);
lean_ctor_set_uint8(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
else
{
lean_object* v___x_913_; 
lean_inc_ref(v_arg_886_);
v___x_913_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_886_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_924_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_924_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_924_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_924_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_918_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpEq___closed__5, &l_Lean_Meta_Grind_NormSym_simpEq___closed__5_once, _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__5);
v___x_919_ = l_Lean_Expr_app___override(v___x_918_, v_arg_886_);
v___x_920_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_920_, 0, v_a_914_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
lean_ctor_set_uint8(v___x_920_, sizeof(void*)*2, v___x_909_);
lean_ctor_set_uint8(v___x_920_, sizeof(void*)*2 + 1, v___x_909_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_920_);
v___x_922_ = v___x_916_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v_arg_886_);
v_a_925_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_913_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_913_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec_ref(v_arg_883_);
v___x_933_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpEq___closed__8, &l_Lean_Meta_Grind_NormSym_simpEq___closed__8_once, _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__8);
lean_inc_ref(v_arg_886_);
v___x_934_ = l_Lean_Expr_app___override(v___x_933_, v_arg_886_);
v___x_935_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_935_, 0, v_arg_886_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*2, v___x_892_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*2 + 1, v___x_908_);
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
return v___x_936_;
}
}
else
{
lean_object* v___x_937_; 
lean_dec_ref(v_arg_883_);
v___x_937_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_871_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_950_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_950_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_950_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_950_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_942_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__10));
v___x_943_ = l_Lean_Expr_constLevels_x21(v___x_890_);
lean_dec_ref(v___x_890_);
v___x_944_ = l_Lean_mkConst(v___x_942_, v___x_943_);
v___x_945_ = l_Lean_mkAppB(v___x_944_, v_arg_889_, v_arg_886_);
v___x_946_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_946_, 0, v_a_938_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
lean_ctor_set_uint8(v___x_946_, sizeof(void*)*2, v___x_892_);
lean_ctor_set_uint8(v___x_946_, sizeof(void*)*2 + 1, v___x_905_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_946_);
v___x_948_ = v___x_940_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
lean_dec_ref(v___x_890_);
lean_dec_ref(v_arg_889_);
lean_dec_ref(v_arg_886_);
v_a_951_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_937_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_937_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
else
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_Expr_getAppFn(v_arg_883_);
if (lean_obj_tag(v___x_959_) == 4)
{
lean_object* v_declName_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_declName_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_declName_960_);
lean_dec_ref_known(v___x_959_, 2);
v___x_961_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__12));
v___x_962_ = lean_name_eq(v_declName_960_, v___x_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_963_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__14));
v___x_964_ = lean_name_eq(v_declName_960_, v___x_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_986_; 
lean_del_object(v___x_896_);
v___x_986_ = l_Lean_Expr_getAppFn(v_arg_886_);
if (lean_obj_tag(v___x_986_) == 4)
{
lean_object* v_declName_987_; uint8_t v___x_988_; 
v_declName_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_declName_987_);
lean_dec_ref_known(v___x_986_, 2);
v___x_988_ = lean_name_eq(v_declName_987_, v___x_961_);
if (v___x_988_ == 0)
{
uint8_t v___x_989_; 
v___x_989_ = lean_name_eq(v_declName_987_, v___x_963_);
if (v___x_989_ == 0)
{
uint8_t v___x_1052_; 
v___x_1052_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(v_declName_987_);
lean_dec(v_declName_987_);
if (v___x_1052_ == 0)
{
uint8_t v___x_1053_; 
v___x_1053_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(v_declName_960_);
lean_dec(v_declName_960_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec_ref(v___x_890_);
lean_dec_ref(v_arg_889_);
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
v___x_1054_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1054_, 0, v___x_1053_);
lean_ctor_set_uint8(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
else
{
goto v___jp_990_;
}
}
else
{
lean_dec(v_declName_960_);
goto v___jp_990_;
}
}
else
{
lean_dec(v_declName_987_);
lean_dec(v_declName_960_);
goto v___jp_965_;
}
v___jp_990_:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_871_);
if (lean_obj_tag(v___x_991_) == 0)
{
lean_object* v_a_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_a_992_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_a_992_);
lean_dec_ref_known(v___x_991_, 1);
v___x_993_ = lean_box(0);
v___x_994_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v___x_993_, v_a_872_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_996_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec_ref_known(v___x_994_, 1);
lean_inc(v_a_992_);
lean_inc_ref(v_arg_886_);
lean_inc_ref(v_arg_889_);
lean_inc_ref(v___x_890_);
v___x_996_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v___x_890_, v_arg_889_, v_arg_886_, v_a_992_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_998_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 1);
lean_inc_ref(v_arg_883_);
lean_inc_ref(v___x_890_);
v___x_998_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v___x_890_, v_arg_889_, v_arg_883_, v_a_992_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1000_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 1);
v___x_1000_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v___x_890_, v_a_995_, v_a_997_, v_a_999_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1011_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1011_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1011_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1005_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpEq___closed__20, &l_Lean_Meta_Grind_NormSym_simpEq___closed__20_once, _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__20);
v___x_1006_ = l_Lean_mkAppB(v___x_1005_, v_arg_886_, v_arg_883_);
v___x_1007_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1007_, 0, v_a_1001_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
lean_ctor_set_uint8(v___x_1007_, sizeof(void*)*2, v___x_989_);
lean_ctor_set_uint8(v___x_1007_, sizeof(void*)*2 + 1, v___x_989_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___x_1007_);
v___x_1009_ = v___x_1003_;
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
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
v_a_1012_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_1000_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1000_);
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
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_dec(v_a_997_);
lean_dec(v_a_995_);
lean_dec_ref(v___x_890_);
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
v_a_1020_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_998_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_998_);
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
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_dec(v_a_995_);
lean_dec(v_a_992_);
lean_dec_ref(v___x_890_);
lean_dec_ref(v_arg_889_);
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
v_a_1028_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_996_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_996_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec(v_a_992_);
lean_dec_ref(v___x_890_);
lean_dec_ref(v_arg_889_);
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
v_a_1036_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_994_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_994_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec_ref(v___x_890_);
lean_dec_ref(v_arg_889_);
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
v_a_1044_ = lean_ctor_get(v___x_991_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_991_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_991_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_991_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
else
{
lean_dec(v_declName_987_);
lean_dec(v_declName_960_);
goto v___jp_965_;
}
}
else
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
lean_dec_ref(v___x_986_);
lean_dec(v_declName_960_);
lean_dec_ref(v___x_890_);
lean_dec_ref(v_arg_889_);
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
v___x_1056_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1056_, 0, v___x_964_);
lean_ctor_set_uint8(v___x_1056_, 1, v___x_964_);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
return v___x_1057_;
}
}
else
{
lean_dec(v_declName_960_);
lean_dec_ref(v___x_890_);
lean_dec_ref(v_arg_889_);
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
goto v___jp_898_;
}
v___jp_965_:
{
lean_object* v___x_966_; 
lean_inc_ref(v_arg_886_);
lean_inc_ref(v_arg_883_);
v___x_966_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v___x_890_, v_arg_889_, v_arg_883_, v_arg_886_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_977_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_977_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_977_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_977_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_975_; 
v___x_971_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpEq___closed__17, &l_Lean_Meta_Grind_NormSym_simpEq___closed__17_once, _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__17);
v___x_972_ = l_Lean_mkAppB(v___x_971_, v_arg_886_, v_arg_883_);
v___x_973_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_973_, 0, v_a_967_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
lean_ctor_set_uint8(v___x_973_, sizeof(void*)*2, v___x_964_);
lean_ctor_set_uint8(v___x_973_, sizeof(void*)*2 + 1, v___x_964_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_973_);
v___x_975_ = v___x_969_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
v_a_978_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_966_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_966_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
else
{
lean_dec(v_declName_960_);
lean_dec_ref(v___x_890_);
lean_dec_ref(v_arg_889_);
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
goto v___jp_898_;
}
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
lean_dec_ref(v___x_959_);
lean_del_object(v___x_896_);
lean_dec_ref(v___x_890_);
lean_dec_ref(v_arg_889_);
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
v___x_1058_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
}
v___jp_898_:
{
lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_899_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 0, v___x_899_);
v___x_901_ = v___x_896_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec_ref(v___x_890_);
lean_dec_ref(v_arg_889_);
lean_dec_ref(v_arg_886_);
lean_dec_ref(v_arg_883_);
v_a_1061_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_893_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_893_);
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
}
}
}
v___jp_878_:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
return v___x_880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpEq___boxed(lean_object* v_e_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_Meta_Grind_NormSym_simpEq(v_e_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(lean_object* v_f_1081_, lean_object* v_a_u2081_1082_, lean_object* v_a_u2082_1083_, lean_object* v_a_u2083_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v_f_1081_, v_a_u2081_1082_, v_a_u2082_1083_, v_a_u2083_1084_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___boxed(lean_object* v_f_1096_, lean_object* v_a_u2081_1097_, lean_object* v_a_u2082_1098_, lean_object* v_a_u2083_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v_f_1096_, v_a_u2081_1097_, v_a_u2082_1098_, v_a_u2083_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___redArg(lean_object* v_f_1111_, lean_object* v_a_u2081_1112_, lean_object* v_a_u2082_1113_, lean_object* v_a_u2083_1114_, lean_object* v_a_u2084_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v_f_1111_, v_a_u2081_1112_, v_a_u2082_1113_, v_a_u2083_1114_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v_a_1124_; lean_object* v___x_1125_; 
v_a_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_a_1124_);
lean_dec_ref_known(v___x_1123_, 1);
v___x_1125_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_a_1124_, v_a_u2084_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
return v___x_1125_;
}
else
{
lean_dec_ref(v_a_u2084_1115_);
return v___x_1123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___redArg___boxed(lean_object* v_f_1126_, lean_object* v_a_u2081_1127_, lean_object* v_a_u2082_1128_, lean_object* v_a_u2083_1129_, lean_object* v_a_u2084_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___redArg(v_f_1126_, v_a_u2081_1127_, v_a_u2082_1128_, v_a_u2083_1129_, v_a_u2084_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0(lean_object* v_f_1139_, lean_object* v_a_u2081_1140_, lean_object* v_a_u2082_1141_, lean_object* v_a_u2083_1142_, lean_object* v_a_u2084_1143_, lean_object* v_a_u2085_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___redArg(v_f_1139_, v_a_u2081_1140_, v_a_u2082_1141_, v_a_u2083_1142_, v_a_u2084_1143_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1155_) == 0)
{
lean_object* v_a_1156_; lean_object* v___x_1157_; 
v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_a_1156_);
lean_dec_ref_known(v___x_1155_, 1);
v___x_1157_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_a_1156_, v_a_u2085_1144_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
return v___x_1157_;
}
else
{
lean_dec_ref(v_a_u2085_1144_);
return v___x_1155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___boxed(lean_object* v_f_1158_, lean_object* v_a_u2081_1159_, lean_object* v_a_u2082_1160_, lean_object* v_a_u2083_1161_, lean_object* v_a_u2084_1162_, lean_object* v_a_u2085_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0(v_f_1158_, v_a_u2081_1159_, v_a_u2082_1160_, v_a_u2083_1161_, v_a_u2084_1162_, v_a_u2085_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1167_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpDIte(lean_object* v_e_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1198_ = l_Lean_Expr_cleanupAnnotations(v_e_1184_);
v___x_1199_ = l_Lean_Expr_isApp(v___x_1198_);
if (v___x_1199_ == 0)
{
lean_dec_ref(v___x_1198_);
goto v___jp_1195_;
}
else
{
lean_object* v_arg_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v_arg_1200_ = lean_ctor_get(v___x_1198_, 1);
lean_inc_ref(v_arg_1200_);
v___x_1201_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1198_);
v___x_1202_ = l_Lean_Expr_isApp(v___x_1201_);
if (v___x_1202_ == 0)
{
lean_dec_ref(v___x_1201_);
lean_dec_ref(v_arg_1200_);
goto v___jp_1195_;
}
else
{
lean_object* v_arg_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v_arg_1203_ = lean_ctor_get(v___x_1201_, 1);
lean_inc_ref(v_arg_1203_);
v___x_1204_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1201_);
v___x_1205_ = l_Lean_Expr_isApp(v___x_1204_);
if (v___x_1205_ == 0)
{
lean_dec_ref(v___x_1204_);
lean_dec_ref(v_arg_1203_);
lean_dec_ref(v_arg_1200_);
goto v___jp_1195_;
}
else
{
lean_object* v_arg_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v_arg_1206_ = lean_ctor_get(v___x_1204_, 1);
lean_inc_ref(v_arg_1206_);
v___x_1207_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1204_);
v___x_1208_ = l_Lean_Expr_isApp(v___x_1207_);
if (v___x_1208_ == 0)
{
lean_dec_ref(v___x_1207_);
lean_dec_ref(v_arg_1206_);
lean_dec_ref(v_arg_1203_);
lean_dec_ref(v_arg_1200_);
goto v___jp_1195_;
}
else
{
lean_object* v_arg_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v_arg_1209_ = lean_ctor_get(v___x_1207_, 1);
lean_inc_ref(v_arg_1209_);
v___x_1210_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1207_);
v___x_1211_ = l_Lean_Expr_isApp(v___x_1210_);
if (v___x_1211_ == 0)
{
lean_dec_ref(v___x_1210_);
lean_dec_ref(v_arg_1209_);
lean_dec_ref(v_arg_1206_);
lean_dec_ref(v_arg_1203_);
lean_dec_ref(v_arg_1200_);
goto v___jp_1195_;
}
else
{
lean_object* v_arg_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; uint8_t v___x_1215_; 
v_arg_1212_ = lean_ctor_get(v___x_1210_, 1);
lean_inc_ref(v_arg_1212_);
v___x_1213_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1210_);
v___x_1214_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpDIte___closed__1));
v___x_1215_ = l_Lean_Expr_isConstOf(v___x_1213_, v___x_1214_);
if (v___x_1215_ == 0)
{
lean_dec_ref(v___x_1213_);
lean_dec_ref(v_arg_1212_);
lean_dec_ref(v_arg_1209_);
lean_dec_ref(v_arg_1206_);
lean_dec_ref(v_arg_1203_);
lean_dec_ref(v_arg_1200_);
goto v___jp_1195_;
}
else
{
if (lean_obj_tag(v_arg_1203_) == 6)
{
lean_object* v_body_1216_; uint8_t v___x_1217_; 
v_body_1216_ = lean_ctor_get(v_arg_1203_, 2);
lean_inc_ref(v_body_1216_);
lean_dec_ref_known(v_arg_1203_, 3);
v___x_1217_ = l_Lean_Expr_hasLooseBVars(v_body_1216_);
if (v___x_1217_ == 0)
{
if (lean_obj_tag(v_arg_1200_) == 6)
{
lean_object* v_body_1218_; uint8_t v___x_1219_; 
v_body_1218_ = lean_ctor_get(v_arg_1200_, 2);
lean_inc_ref(v_body_1218_);
lean_dec_ref_known(v_arg_1200_, 3);
v___x_1219_ = l_Lean_Expr_hasLooseBVars(v_body_1218_);
if (v___x_1219_ == 0)
{
lean_object* v_us_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v_us_1220_ = l_Lean_Expr_constLevels_x21(v___x_1213_);
lean_dec_ref(v___x_1213_);
v___x_1221_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpDIte___closed__3));
lean_inc(v_us_1220_);
v___x_1222_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v___x_1221_, v_us_1220_, v_a_1189_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; lean_object* v___x_1224_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref_known(v___x_1222_, 1);
lean_inc_ref(v_body_1218_);
lean_inc_ref(v_body_1216_);
lean_inc_ref(v_arg_1206_);
lean_inc_ref(v_arg_1209_);
lean_inc_ref(v_arg_1212_);
v___x_1224_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0(v_a_1223_, v_arg_1212_, v_arg_1209_, v_arg_1206_, v_body_1216_, v_body_1218_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1236_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1227_ = v___x_1224_;
v_isShared_1228_ = v_isSharedCheck_1236_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1224_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1236_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1229_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpDIte___closed__5));
v___x_1230_ = l_Lean_mkConst(v___x_1229_, v_us_1220_);
v___x_1231_ = l_Lean_mkApp5(v___x_1230_, v_arg_1209_, v_arg_1212_, v_body_1216_, v_body_1218_, v_arg_1206_);
v___x_1232_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1232_, 0, v_a_1225_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
lean_ctor_set_uint8(v___x_1232_, sizeof(void*)*2, v___x_1219_);
lean_ctor_set_uint8(v___x_1232_, sizeof(void*)*2 + 1, v___x_1219_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1232_);
v___x_1234_ = v___x_1227_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec(v_us_1220_);
lean_dec_ref(v_body_1218_);
lean_dec_ref(v_body_1216_);
lean_dec_ref(v_arg_1212_);
lean_dec_ref(v_arg_1209_);
lean_dec_ref(v_arg_1206_);
v_a_1237_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1224_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1224_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec(v_us_1220_);
lean_dec_ref(v_body_1218_);
lean_dec_ref(v_body_1216_);
lean_dec_ref(v_arg_1212_);
lean_dec_ref(v_arg_1209_);
lean_dec_ref(v_arg_1206_);
v_a_1245_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1222_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1222_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
else
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec_ref(v_body_1218_);
lean_dec_ref(v_body_1216_);
lean_dec_ref(v___x_1213_);
lean_dec_ref(v_arg_1212_);
lean_dec_ref(v_arg_1209_);
lean_dec_ref(v_arg_1206_);
v___x_1253_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1253_, 0, v___x_1217_);
lean_ctor_set_uint8(v___x_1253_, 1, v___x_1217_);
v___x_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
return v___x_1254_;
}
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_dec_ref(v_body_1216_);
lean_dec_ref(v___x_1213_);
lean_dec_ref(v_arg_1212_);
lean_dec_ref(v_arg_1209_);
lean_dec_ref(v_arg_1206_);
lean_dec_ref(v_arg_1200_);
v___x_1255_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1255_, 0, v___x_1217_);
lean_ctor_set_uint8(v___x_1255_, 1, v___x_1217_);
v___x_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
return v___x_1256_;
}
}
else
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
lean_dec_ref(v_body_1216_);
lean_dec_ref(v___x_1213_);
lean_dec_ref(v_arg_1212_);
lean_dec_ref(v_arg_1209_);
lean_dec_ref(v_arg_1206_);
lean_dec_ref(v_arg_1200_);
v___x_1257_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
return v___x_1258_;
}
}
else
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec_ref(v___x_1213_);
lean_dec_ref(v_arg_1212_);
lean_dec_ref(v_arg_1209_);
lean_dec_ref(v_arg_1206_);
lean_dec_ref(v_arg_1203_);
lean_dec_ref(v_arg_1200_);
v___x_1259_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
return v___x_1260_;
}
}
}
}
}
}
}
v___jp_1195_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
return v___x_1197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpDIte___boxed(lean_object* v_e_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_Meta_Grind_NormSym_simpDIte(v_e_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
lean_dec(v_a_1262_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0(lean_object* v_f_1273_, lean_object* v_a_u2081_1274_, lean_object* v_a_u2082_1275_, lean_object* v_a_u2083_1276_, lean_object* v_a_u2084_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___redArg(v_f_1273_, v_a_u2081_1274_, v_a_u2082_1275_, v_a_u2083_1276_, v_a_u2084_1277_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___boxed(lean_object* v_f_1289_, lean_object* v_a_u2081_1290_, lean_object* v_a_u2082_1291_, lean_object* v_a_u2083_1292_, lean_object* v_a_u2084_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0(v_f_1289_, v_a_u2081_1290_, v_a_u2082_1291_, v_a_u2083_1292_, v_a_u2084_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v___y_1294_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(lean_object* v_x_1305_, uint8_t v_bi_1306_, lean_object* v_t_1307_, lean_object* v_b_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v___y_1317_; lean_object* v___x_1320_; uint8_t v_debug_1321_; 
v___x_1320_ = lean_st_ref_get(v___y_1310_);
v_debug_1321_ = lean_ctor_get_uint8(v___x_1320_, sizeof(void*)*12);
lean_dec(v___x_1320_);
if (v_debug_1321_ == 0)
{
v___y_1317_ = v___y_1310_;
goto v___jp_1316_;
}
else
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1307_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v___x_1323_; 
lean_dec_ref_known(v___x_1322_, 1);
v___x_1323_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_dec_ref_known(v___x_1323_, 1);
v___y_1317_ = v___y_1310_;
goto v___jp_1316_;
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec_ref(v_b_1308_);
lean_dec_ref(v_t_1307_);
lean_dec(v_x_1305_);
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1323_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1323_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_dec_ref(v_b_1308_);
lean_dec_ref(v_t_1307_);
lean_dec(v_x_1305_);
v_a_1332_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1322_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1322_);
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
v___jp_1316_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = l_Lean_Expr_lam___override(v_x_1305_, v_t_1307_, v_b_1308_, v_bi_1306_);
v___x_1319_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1318_, v___y_1317_);
return v___x_1319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg___boxed(lean_object* v_x_1340_, lean_object* v_bi_1341_, lean_object* v_t_1342_, lean_object* v_b_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
uint8_t v_bi_boxed_1351_; lean_object* v_res_1352_; 
v_bi_boxed_1351_ = lean_unbox(v_bi_1341_);
v_res_1352_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_x_1340_, v_bi_boxed_1351_, v_t_1342_, v_b_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0(lean_object* v_x_1353_, uint8_t v_bi_1354_, lean_object* v_t_1355_, lean_object* v_b_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_x_1353_, v_bi_1354_, v_t_1355_, v_b_1356_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___boxed(lean_object* v_x_1368_, lean_object* v_bi_1369_, lean_object* v_t_1370_, lean_object* v_b_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
uint8_t v_bi_boxed_1382_; lean_object* v_res_1383_; 
v_bi_boxed_1382_ = lean_unbox(v_bi_1369_);
v_res_1383_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0(v_x_1368_, v_bi_boxed_1382_, v_t_1370_, v_b_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(lean_object* v_idx_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1387_ = l_Lean_Expr_bvar___override(v_idx_1384_);
v___x_1388_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1387_, v___y_1385_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg___boxed(lean_object* v_idx_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(v_idx_1389_, v___y_1390_);
lean_dec(v___y_1390_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1(lean_object* v_idx_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(v_idx_1393_, v___y_1398_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___boxed(lean_object* v_idx_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1(v_idx_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
lean_dec_ref(v___y_1409_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(lean_object* v_x_1417_, uint8_t v_bi_1418_, lean_object* v_t_1419_, lean_object* v_b_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v___y_1429_; lean_object* v___x_1432_; uint8_t v_debug_1433_; 
v___x_1432_ = lean_st_ref_get(v___y_1422_);
v_debug_1433_ = lean_ctor_get_uint8(v___x_1432_, sizeof(void*)*12);
lean_dec(v___x_1432_);
if (v_debug_1433_ == 0)
{
v___y_1429_ = v___y_1422_;
goto v___jp_1428_;
}
else
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1419_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v___x_1435_; 
lean_dec_ref_known(v___x_1434_, 1);
v___x_1435_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_dec_ref_known(v___x_1435_, 1);
v___y_1429_ = v___y_1422_;
goto v___jp_1428_;
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec_ref(v_b_1420_);
lean_dec_ref(v_t_1419_);
lean_dec(v_x_1417_);
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec_ref(v_b_1420_);
lean_dec_ref(v_t_1419_);
lean_dec(v_x_1417_);
v_a_1444_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1434_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1434_);
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
v___jp_1428_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = l_Lean_Expr_forallE___override(v_x_1417_, v_t_1419_, v_b_1420_, v_bi_1418_);
v___x_1431_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1430_, v___y_1429_);
return v___x_1431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg___boxed(lean_object* v_x_1452_, lean_object* v_bi_1453_, lean_object* v_t_1454_, lean_object* v_b_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
uint8_t v_bi_boxed_1463_; lean_object* v_res_1464_; 
v_bi_boxed_1463_ = lean_unbox(v_bi_1453_);
v_res_1464_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_x_1452_, v_bi_boxed_1463_, v_t_1454_, v_b_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2(lean_object* v_x_1465_, uint8_t v_bi_1466_, lean_object* v_t_1467_, lean_object* v_b_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_x_1465_, v_bi_1466_, v_t_1467_, v_b_1468_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___boxed(lean_object* v_x_1480_, lean_object* v_bi_1481_, lean_object* v_t_1482_, lean_object* v_b_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
uint8_t v_bi_boxed_1494_; lean_object* v_res_1495_; 
v_bi_boxed_1494_ = lean_unbox(v_bi_1481_);
v_res_1495_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2(v_x_1480_, v_bi_boxed_1494_, v_t_1482_, v_b_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
return v_res_1495_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__4(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = lean_box(0);
v___x_1507_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__3));
v___x_1508_ = l_Lean_mkConst(v___x_1507_, v___x_1506_);
return v___x_1508_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__11(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1520_ = lean_box(0);
v___x_1521_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__10));
v___x_1522_ = l_Lean_mkConst(v___x_1521_, v___x_1520_);
return v___x_1522_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__14(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1527_ = lean_box(0);
v___x_1528_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__13));
v___x_1529_ = l_Lean_mkConst(v___x_1528_, v___x_1527_);
return v___x_1529_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__17(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1534_ = lean_box(0);
v___x_1535_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__16));
v___x_1536_ = l_Lean_mkConst(v___x_1535_, v___x_1534_);
return v___x_1536_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__20(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1542_ = lean_box(0);
v___x_1543_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__19));
v___x_1544_ = l_Lean_mkConst(v___x_1543_, v___x_1542_);
return v___x_1544_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__23(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1550_ = lean_box(0);
v___x_1551_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__22));
v___x_1552_ = l_Lean_mkConst(v___x_1551_, v___x_1550_);
return v___x_1552_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__26(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1558_ = lean_box(0);
v___x_1559_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__25));
v___x_1560_ = l_Lean_mkConst(v___x_1559_, v___x_1558_);
return v___x_1560_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__33(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1574_ = lean_box(0);
v___x_1575_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__32));
v___x_1576_ = l_Lean_mkConst(v___x_1575_, v___x_1574_);
return v___x_1576_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__36(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1582_ = lean_box(0);
v___x_1583_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__35));
v___x_1584_ = l_Lean_mkConst(v___x_1583_, v___x_1582_);
return v___x_1584_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__39(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1590_ = lean_box(0);
v___x_1591_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__38));
v___x_1592_ = l_Lean_mkConst(v___x_1591_, v___x_1590_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_pushNot(lean_object* v_e_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v___y_1605_; lean_object* v___y_1606_; lean_object* v___y_1607_; lean_object* v___y_1608_; uint8_t v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; lean_object* v___y_1614_; lean_object* v___y_1615_; lean_object* v___y_1616_; lean_object* v___y_1617_; uint8_t v___y_1618_; lean_object* v___x_1676_; uint8_t v___x_1677_; 
v___x_1676_ = l_Lean_Expr_cleanupAnnotations(v_e_1593_);
v___x_1677_ = l_Lean_Expr_isApp(v___x_1676_);
if (v___x_1677_ == 0)
{
lean_dec_ref(v___x_1676_);
goto v___jp_1673_;
}
else
{
lean_object* v_arg_1678_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___x_1739_; lean_object* v___x_1740_; uint8_t v___x_1741_; 
v_arg_1678_ = lean_ctor_get(v___x_1676_, 1);
lean_inc_ref(v_arg_1678_);
v___x_1739_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1676_);
v___x_1740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS___closed__1));
v___x_1741_ = l_Lean_Expr_isConstOf(v___x_1739_, v___x_1740_);
lean_dec_ref(v___x_1739_);
if (v___x_1741_ == 0)
{
lean_dec_ref(v_arg_1678_);
goto v___jp_1673_;
}
else
{
lean_object* v___x_1742_; 
lean_inc_ref(v_arg_1678_);
v___x_1742_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1678_, v_a_1600_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_2126_; 
v_a_1743_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_1745_ = v___x_1742_;
v_isShared_1746_ = v_isSharedCheck_2126_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1742_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_2126_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1747_ = l_Lean_Expr_cleanupAnnotations(v_a_1743_);
v___x_1748_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__6));
v___x_1749_ = l_Lean_Expr_isConstOf(v___x_1747_, v___x_1748_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; uint8_t v___x_1751_; 
v___x_1750_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_1751_ = l_Lean_Expr_isConstOf(v___x_1747_, v___x_1750_);
if (v___x_1751_ == 0)
{
uint8_t v___x_1752_; 
v___x_1752_ = l_Lean_Expr_isApp(v___x_1747_);
if (v___x_1752_ == 0)
{
lean_dec_ref(v___x_1747_);
lean_del_object(v___x_1745_);
v___y_1680_ = v_a_1594_;
v___y_1681_ = v_a_1595_;
v___y_1682_ = v_a_1596_;
v___y_1683_ = v_a_1597_;
v___y_1684_ = v_a_1598_;
v___y_1685_ = v_a_1599_;
v___y_1686_ = v_a_1600_;
v___y_1687_ = v_a_1601_;
v___y_1688_ = v_a_1602_;
goto v___jp_1679_;
}
else
{
lean_object* v_arg_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v_arg_1753_ = lean_ctor_get(v___x_1747_, 1);
lean_inc_ref(v_arg_1753_);
v___x_1754_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1747_);
v___x_1755_ = l_Lean_Expr_isConstOf(v___x_1754_, v___x_1740_);
if (v___x_1755_ == 0)
{
uint8_t v___x_1756_; 
lean_del_object(v___x_1745_);
v___x_1756_ = l_Lean_Expr_isApp(v___x_1754_);
if (v___x_1756_ == 0)
{
lean_dec_ref(v___x_1754_);
lean_dec_ref(v_arg_1753_);
v___y_1680_ = v_a_1594_;
v___y_1681_ = v_a_1595_;
v___y_1682_ = v_a_1596_;
v___y_1683_ = v_a_1597_;
v___y_1684_ = v_a_1598_;
v___y_1685_ = v_a_1599_;
v___y_1686_ = v_a_1600_;
v___y_1687_ = v_a_1601_;
v___y_1688_ = v_a_1602_;
goto v___jp_1679_;
}
else
{
lean_object* v_arg_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v_arg_1757_ = lean_ctor_get(v___x_1754_, 1);
lean_inc_ref(v_arg_1757_);
v___x_1758_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1754_);
v___x_1759_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg___closed__1));
v___x_1760_ = l_Lean_Expr_isConstOf(v___x_1758_, v___x_1759_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; uint8_t v___x_1762_; 
v___x_1761_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1));
v___x_1762_ = l_Lean_Expr_isConstOf(v___x_1758_, v___x_1761_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; uint8_t v___x_1764_; 
v___x_1763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS___closed__1));
v___x_1764_ = l_Lean_Expr_isConstOf(v___x_1758_, v___x_1763_);
if (v___x_1764_ == 0)
{
uint8_t v___x_1765_; 
v___x_1765_ = l_Lean_Expr_isApp(v___x_1758_);
if (v___x_1765_ == 0)
{
lean_dec_ref(v___x_1758_);
lean_dec_ref(v_arg_1757_);
lean_dec_ref(v_arg_1753_);
v___y_1680_ = v_a_1594_;
v___y_1681_ = v_a_1595_;
v___y_1682_ = v_a_1596_;
v___y_1683_ = v_a_1597_;
v___y_1684_ = v_a_1598_;
v___y_1685_ = v_a_1599_;
v___y_1686_ = v_a_1600_;
v___y_1687_ = v_a_1601_;
v___y_1688_ = v_a_1602_;
goto v___jp_1679_;
}
else
{
lean_object* v_arg_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v_arg_1766_ = lean_ctor_get(v___x_1758_, 1);
lean_inc_ref(v_arg_1766_);
v___x_1767_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1758_);
v___x_1768_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__1));
v___x_1769_ = l_Lean_Expr_isConstOf(v___x_1767_, v___x_1768_);
if (v___x_1769_ == 0)
{
uint8_t v___x_1770_; 
v___x_1770_ = l_Lean_Expr_isApp(v___x_1767_);
if (v___x_1770_ == 0)
{
lean_dec_ref(v___x_1767_);
lean_dec_ref(v_arg_1766_);
lean_dec_ref(v_arg_1757_);
lean_dec_ref(v_arg_1753_);
v___y_1680_ = v_a_1594_;
v___y_1681_ = v_a_1595_;
v___y_1682_ = v_a_1596_;
v___y_1683_ = v_a_1597_;
v___y_1684_ = v_a_1598_;
v___y_1685_ = v_a_1599_;
v___y_1686_ = v_a_1600_;
v___y_1687_ = v_a_1601_;
v___y_1688_ = v_a_1602_;
goto v___jp_1679_;
}
else
{
lean_object* v_arg_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v_arg_1771_ = lean_ctor_get(v___x_1767_, 1);
lean_inc_ref(v_arg_1771_);
v___x_1772_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1767_);
v___x_1773_ = l_Lean_Expr_isApp(v___x_1772_);
if (v___x_1773_ == 0)
{
lean_dec_ref(v___x_1772_);
lean_dec_ref(v_arg_1771_);
lean_dec_ref(v_arg_1766_);
lean_dec_ref(v_arg_1757_);
lean_dec_ref(v_arg_1753_);
v___y_1680_ = v_a_1594_;
v___y_1681_ = v_a_1595_;
v___y_1682_ = v_a_1596_;
v___y_1683_ = v_a_1597_;
v___y_1684_ = v_a_1598_;
v___y_1685_ = v_a_1599_;
v___y_1686_ = v_a_1600_;
v___y_1687_ = v_a_1601_;
v___y_1688_ = v_a_1602_;
goto v___jp_1679_;
}
else
{
lean_object* v_arg_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v_arg_1774_ = lean_ctor_get(v___x_1772_, 1);
lean_inc_ref(v_arg_1774_);
v___x_1775_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1772_);
v___x_1776_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpDIte___closed__3));
v___x_1777_ = l_Lean_Expr_isConstOf(v___x_1775_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_dec_ref(v___x_1775_);
lean_dec_ref(v_arg_1774_);
lean_dec_ref(v_arg_1771_);
lean_dec_ref(v_arg_1766_);
lean_dec_ref(v_arg_1757_);
lean_dec_ref(v_arg_1753_);
v___y_1680_ = v_a_1594_;
v___y_1681_ = v_a_1595_;
v___y_1682_ = v_a_1596_;
v___y_1683_ = v_a_1597_;
v___y_1684_ = v_a_1598_;
v___y_1685_ = v_a_1599_;
v___y_1686_ = v_a_1600_;
v___y_1687_ = v_a_1601_;
v___y_1688_ = v_a_1602_;
goto v___jp_1679_;
}
else
{
lean_object* v___x_1778_; 
lean_dec_ref(v_arg_1678_);
lean_inc_ref(v_arg_1757_);
v___x_1778_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1757_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1780_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref_known(v___x_1778_, 1);
lean_inc_ref(v_arg_1753_);
v___x_1780_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1753_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1782_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1781_);
lean_dec_ref_known(v___x_1780_, 1);
lean_inc_ref(v_arg_1766_);
lean_inc_ref(v_arg_1771_);
v___x_1782_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0(v___x_1775_, v_arg_1774_, v_arg_1771_, v_arg_1766_, v_a_1779_, v_a_1781_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1793_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1785_ = v___x_1782_;
v_isShared_1786_ = v_isSharedCheck_1793_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1782_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1793_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1791_; 
v___x_1787_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__11, &l_Lean_Meta_Grind_NormSym_pushNot___closed__11_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__11);
v___x_1788_ = l_Lean_mkApp4(v___x_1787_, v_arg_1771_, v_arg_1766_, v_arg_1757_, v_arg_1753_);
v___x_1789_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1789_, 0, v_a_1783_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*2, v___x_1769_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*2 + 1, v___x_1769_);
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 0, v___x_1789_);
v___x_1791_ = v___x_1785_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_dec_ref(v_arg_1771_);
lean_dec_ref(v_arg_1766_);
lean_dec_ref(v_arg_1757_);
lean_dec_ref(v_arg_1753_);
v_a_1794_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1782_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1782_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
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
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
lean_dec(v_a_1779_);
lean_dec_ref(v___x_1775_);
lean_dec_ref(v_arg_1774_);
lean_dec_ref(v_arg_1771_);
lean_dec_ref(v_arg_1766_);
lean_dec_ref(v_arg_1757_);
lean_dec_ref(v_arg_1753_);
v_a_1802_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1780_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1780_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
lean_dec_ref(v___x_1775_);
lean_dec_ref(v_arg_1774_);
lean_dec_ref(v_arg_1771_);
lean_dec_ref(v_arg_1766_);
lean_dec_ref(v_arg_1757_);
lean_dec_ref(v_arg_1753_);
v_a_1810_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1778_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1778_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
}
}
}
else
{
uint8_t v___x_1818_; 
lean_dec_ref(v_arg_1678_);
v___x_1818_ = l_Lean_Expr_isProp(v_arg_1766_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1753_, v_a_1600_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1893_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1822_ = v___x_1819_;
v_isShared_1823_ = v_isSharedCheck_1893_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1893_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1824_ = l_Lean_Expr_cleanupAnnotations(v_a_1820_);
v___x_1825_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__14));
v___x_1826_ = l_Lean_Expr_isConstOf(v___x_1824_, v___x_1825_);
if (v___x_1826_ == 0)
{
lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1827_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__12));
v___x_1828_ = l_Lean_Expr_isConstOf(v___x_1824_, v___x_1827_);
lean_dec_ref(v___x_1824_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; lean_object* v___x_1831_; 
lean_dec_ref(v___x_1767_);
lean_dec_ref(v_arg_1766_);
lean_dec_ref(v_arg_1757_);
v___x_1829_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1829_, 0, v___x_1818_);
lean_ctor_set_uint8(v___x_1829_, 1, v___x_1818_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v___x_1829_);
v___x_1831_ = v___x_1822_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
else
{
lean_object* v___x_1833_; 
lean_del_object(v___x_1822_);
v___x_1833_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_1597_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1835_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1833_, 1);
lean_inc_ref(v_arg_1757_);
v___x_1835_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v___x_1767_, v_arg_1766_, v_arg_1757_, v_a_1834_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1846_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1846_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1846_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1840_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__14, &l_Lean_Meta_Grind_NormSym_pushNot___closed__14_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__14);
v___x_1841_ = l_Lean_Expr_app___override(v___x_1840_, v_arg_1757_);
v___x_1842_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1842_, 0, v_a_1836_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
lean_ctor_set_uint8(v___x_1842_, sizeof(void*)*2, v___x_1818_);
lean_ctor_set_uint8(v___x_1842_, sizeof(void*)*2 + 1, v___x_1818_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1842_);
v___x_1844_ = v___x_1838_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
else
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1854_; 
lean_dec_ref(v_arg_1757_);
v_a_1847_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1849_ = v___x_1835_;
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1835_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1854_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1852_; 
if (v_isShared_1850_ == 0)
{
v___x_1852_ = v___x_1849_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_a_1847_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec_ref(v___x_1767_);
lean_dec_ref(v_arg_1766_);
lean_dec_ref(v_arg_1757_);
v_a_1855_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1833_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1833_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
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
}
else
{
lean_object* v___x_1863_; 
lean_dec_ref(v___x_1824_);
lean_del_object(v___x_1822_);
v___x_1863_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_1597_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1865_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref_known(v___x_1863_, 1);
lean_inc_ref(v_arg_1757_);
v___x_1865_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v___x_1767_, v_arg_1766_, v_arg_1757_, v_a_1864_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1876_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1876_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1876_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1870_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__17, &l_Lean_Meta_Grind_NormSym_pushNot___closed__17_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__17);
v___x_1871_ = l_Lean_Expr_app___override(v___x_1870_, v_arg_1757_);
v___x_1872_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1872_, 0, v_a_1866_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
lean_ctor_set_uint8(v___x_1872_, sizeof(void*)*2, v___x_1818_);
lean_ctor_set_uint8(v___x_1872_, sizeof(void*)*2 + 1, v___x_1818_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v___x_1872_);
v___x_1874_ = v___x_1868_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec_ref(v_arg_1757_);
v_a_1877_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1865_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1865_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec_ref(v___x_1767_);
lean_dec_ref(v_arg_1766_);
lean_dec_ref(v_arg_1757_);
v_a_1885_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1863_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1863_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec_ref(v___x_1767_);
lean_dec_ref(v_arg_1766_);
lean_dec_ref(v_arg_1757_);
v_a_1894_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1819_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1819_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
else
{
lean_object* v___x_1902_; 
lean_inc_ref(v_arg_1753_);
v___x_1902_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1753_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1904_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref_known(v___x_1902_, 1);
lean_inc_ref(v_arg_1757_);
v___x_1904_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v___x_1767_, v_arg_1766_, v_arg_1757_, v_a_1903_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1915_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1907_ = v___x_1904_;
v_isShared_1908_ = v_isSharedCheck_1915_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1904_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1915_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1909_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__20, &l_Lean_Meta_Grind_NormSym_pushNot___closed__20_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__20);
v___x_1910_ = l_Lean_mkAppB(v___x_1909_, v_arg_1757_, v_arg_1753_);
v___x_1911_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1911_, 0, v_a_1905_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
lean_ctor_set_uint8(v___x_1911_, sizeof(void*)*2, v___x_1764_);
lean_ctor_set_uint8(v___x_1911_, sizeof(void*)*2 + 1, v___x_1764_);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1911_);
v___x_1913_ = v___x_1907_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec_ref(v_arg_1757_);
lean_dec_ref(v_arg_1753_);
v_a_1916_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1904_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1904_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
else
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
lean_dec_ref(v___x_1767_);
lean_dec_ref(v_arg_1766_);
lean_dec_ref(v_arg_1757_);
lean_dec_ref(v_arg_1753_);
v_a_1924_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1926_ = v___x_1902_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1902_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1924_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1932_; 
lean_dec_ref(v___x_1758_);
lean_dec_ref(v_arg_1678_);
lean_inc_ref(v_arg_1757_);
v___x_1932_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1757_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1934_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
lean_inc_ref(v_arg_1753_);
v___x_1934_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1753_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1936_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref_known(v___x_1934_, 1);
v___x_1936_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_a_1933_, v_a_1935_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1947_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1947_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1947_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1945_; 
v___x_1941_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__23, &l_Lean_Meta_Grind_NormSym_pushNot___closed__23_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__23);
v___x_1942_ = l_Lean_mkAppB(v___x_1941_, v_arg_1757_, v_arg_1753_);
v___x_1943_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1943_, 0, v_a_1937_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
lean_ctor_set_uint8(v___x_1943_, sizeof(void*)*2, v___x_1762_);
lean_ctor_set_uint8(v___x_1943_, sizeof(void*)*2 + 1, v___x_1762_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1943_);
v___x_1945_ = v___x_1939_;
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
else
{
lean_object* v_a_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1955_; 
lean_dec_ref(v_arg_1757_);
lean_dec_ref(v_arg_1753_);
v_a_1948_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1950_ = v___x_1936_;
v_isShared_1951_ = v_isSharedCheck_1955_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_a_1948_);
lean_dec(v___x_1936_);
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
else
{
lean_object* v_a_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec(v_a_1933_);
lean_dec_ref(v_arg_1757_);
lean_dec_ref(v_arg_1753_);
v_a_1956_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1934_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_a_1956_);
lean_dec(v___x_1934_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_a_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_dec_ref(v_arg_1757_);
lean_dec_ref(v_arg_1753_);
v_a_1964_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1932_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1932_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
else
{
lean_object* v___x_1972_; 
lean_dec_ref(v___x_1758_);
lean_dec_ref(v_arg_1678_);
lean_inc_ref(v_arg_1757_);
v___x_1972_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1757_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1974_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v___x_1972_, 1);
lean_inc_ref(v_arg_1753_);
v___x_1974_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1753_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1976_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref_known(v___x_1974_, 1);
v___x_1976_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v_a_1973_, v_a_1975_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1987_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1979_ = v___x_1976_;
v_isShared_1980_ = v_isSharedCheck_1987_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1976_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1987_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1985_; 
v___x_1981_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__26, &l_Lean_Meta_Grind_NormSym_pushNot___closed__26_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__26);
v___x_1982_ = l_Lean_mkAppB(v___x_1981_, v_arg_1757_, v_arg_1753_);
v___x_1983_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1983_, 0, v_a_1977_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
lean_ctor_set_uint8(v___x_1983_, sizeof(void*)*2, v___x_1760_);
lean_ctor_set_uint8(v___x_1983_, sizeof(void*)*2 + 1, v___x_1760_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v___x_1983_);
v___x_1985_ = v___x_1979_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec_ref(v_arg_1757_);
lean_dec_ref(v_arg_1753_);
v_a_1988_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1976_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1976_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
else
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
lean_dec(v_a_1973_);
lean_dec_ref(v_arg_1757_);
lean_dec_ref(v_arg_1753_);
v_a_1996_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1974_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1974_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_dec_ref(v_arg_1757_);
lean_dec_ref(v_arg_1753_);
v_a_2004_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_1972_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_1972_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_dec_ref(v___x_1758_);
lean_dec_ref(v_arg_1678_);
v___x_2012_ = lean_unsigned_to_nat(0u);
v___x_2013_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(v___x_2012_, v_a_1598_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
v___x_2015_ = lean_unsigned_to_nat(1u);
v___x_2016_ = lean_mk_empty_array_with_capacity(v___x_2015_);
v___x_2017_ = lean_array_push(v___x_2016_, v_a_2014_);
lean_inc_ref(v_arg_1753_);
v___x_2018_ = l_Lean_Meta_Sym_betaS(v_arg_1753_, v___x_2017_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2020_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2019_);
lean_dec_ref_known(v___x_2018_, 1);
v___x_2020_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_a_2019_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; lean_object* v___x_2024_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v___x_2020_, 1);
v___x_2022_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__28));
v___x_2023_ = 0;
lean_inc_ref(v_arg_1757_);
v___x_2024_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v___x_2022_, v___x_2023_, v_arg_1757_, v_a_2021_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2026_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2024_, 1);
lean_inc_ref(v_arg_1757_);
v___x_2026_ = l_Lean_Meta_Sym_getLevel___redArg(v_arg_1757_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2040_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2029_ = v___x_2026_;
v_isShared_2030_ = v_isSharedCheck_2040_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2026_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2040_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2031_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__30));
v___x_2032_ = lean_box(0);
v___x_2033_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2033_, 0, v_a_2027_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v___x_2034_ = l_Lean_mkConst(v___x_2031_, v___x_2033_);
v___x_2035_ = l_Lean_mkAppB(v___x_2034_, v_arg_1757_, v_arg_1753_);
v___x_2036_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2036_, 0, v_a_2025_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*2, v___x_1755_);
lean_ctor_set_uint8(v___x_2036_, sizeof(void*)*2 + 1, v___x_1755_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 0, v___x_2036_);
v___x_2038_ = v___x_2029_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec(v_a_2025_);
lean_dec_ref(v_arg_1757_);
lean_dec_ref(v_arg_1753_);
v_a_2041_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2026_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2026_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec_ref(v_arg_1757_);
lean_dec_ref(v_arg_1753_);
v_a_2049_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2024_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2024_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec_ref(v_arg_1757_);
lean_dec_ref(v_arg_1753_);
v_a_2057_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2020_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2020_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_dec_ref(v_arg_1757_);
lean_dec_ref(v_arg_1753_);
v_a_2065_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2018_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2018_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec_ref(v_arg_1757_);
lean_dec_ref(v_arg_1753_);
v_a_2073_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2013_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2013_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2085_; 
lean_dec_ref(v___x_1754_);
lean_dec_ref(v_arg_1678_);
v___x_2081_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__33, &l_Lean_Meta_Grind_NormSym_pushNot___closed__33_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__33);
lean_inc_ref(v_arg_1753_);
v___x_2082_ = l_Lean_Expr_app___override(v___x_2081_, v_arg_1753_);
v___x_2083_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2083_, 0, v_arg_1753_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
lean_ctor_set_uint8(v___x_2083_, sizeof(void*)*2, v___x_1751_);
lean_ctor_set_uint8(v___x_2083_, sizeof(void*)*2 + 1, v___x_1751_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 0, v___x_2083_);
v___x_2085_ = v___x_1745_;
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
}
else
{
lean_object* v___x_2087_; 
lean_dec_ref(v___x_1747_);
lean_del_object(v___x_1745_);
lean_dec_ref(v_arg_1678_);
v___x_2087_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_1597_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2097_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2090_ = v___x_2087_;
v_isShared_2091_ = v_isSharedCheck_2097_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2087_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2097_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2092_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__36, &l_Lean_Meta_Grind_NormSym_pushNot___closed__36_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__36);
v___x_2093_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2093_, 0, v_a_2088_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
lean_ctor_set_uint8(v___x_2093_, sizeof(void*)*2, v___x_1749_);
lean_ctor_set_uint8(v___x_2093_, sizeof(void*)*2 + 1, v___x_1749_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v___x_2093_);
v___x_2095_ = v___x_2090_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
v_a_2098_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2087_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2087_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
}
else
{
lean_object* v___x_2106_; 
lean_dec_ref(v___x_1747_);
lean_del_object(v___x_1745_);
lean_dec_ref(v_arg_1678_);
v___x_2106_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_1597_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2117_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2109_ = v___x_2106_;
v_isShared_2110_ = v_isSharedCheck_2117_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2106_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2117_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; uint8_t v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2115_; 
v___x_2111_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__39, &l_Lean_Meta_Grind_NormSym_pushNot___closed__39_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__39);
v___x_2112_ = 0;
v___x_2113_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2113_, 0, v_a_2107_);
lean_ctor_set(v___x_2113_, 1, v___x_2111_);
lean_ctor_set_uint8(v___x_2113_, sizeof(void*)*2, v___x_2112_);
lean_ctor_set_uint8(v___x_2113_, sizeof(void*)*2 + 1, v___x_2112_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2113_);
v___x_2115_ = v___x_2109_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
v_a_2118_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2106_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2106_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec_ref(v_arg_1678_);
v_a_2127_ = lean_ctor_get(v___x_1742_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_1742_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_1742_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
v___jp_1679_:
{
if (lean_obj_tag(v_arg_1678_) == 7)
{
lean_object* v_binderName_1689_; lean_object* v_binderType_1690_; lean_object* v_body_1691_; uint8_t v_binderInfo_1692_; lean_object* v___x_1693_; 
v_binderName_1689_ = lean_ctor_get(v_arg_1678_, 0);
lean_inc(v_binderName_1689_);
v_binderType_1690_ = lean_ctor_get(v_arg_1678_, 1);
lean_inc_ref_n(v_binderType_1690_, 2);
v_body_1691_ = lean_ctor_get(v_arg_1678_, 2);
lean_inc_ref(v_body_1691_);
v_binderInfo_1692_ = lean_ctor_get_uint8(v_arg_1678_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_arg_1678_, 3);
v___x_1693_ = l_Lean_Meta_isProp(v_binderType_1690_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; uint8_t v___x_1695_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref_known(v___x_1693_, 1);
v___x_1695_ = l_Lean_Expr_hasLooseBVars(v_body_1691_);
if (v___x_1695_ == 0)
{
uint8_t v___x_1696_; 
v___x_1696_ = lean_unbox(v_a_1694_);
if (v___x_1696_ == 0)
{
uint8_t v___x_1697_; 
v___x_1697_ = lean_unbox(v_a_1694_);
lean_dec(v_a_1694_);
v___y_1605_ = v_binderType_1690_;
v___y_1606_ = v___y_1680_;
v___y_1607_ = v___y_1681_;
v___y_1608_ = v___y_1686_;
v___y_1609_ = v_binderInfo_1692_;
v___y_1610_ = v___y_1687_;
v___y_1611_ = v___y_1685_;
v___y_1612_ = v___y_1688_;
v___y_1613_ = v___y_1683_;
v___y_1614_ = v_binderName_1689_;
v___y_1615_ = v_body_1691_;
v___y_1616_ = v___y_1684_;
v___y_1617_ = v___y_1682_;
v___y_1618_ = v___x_1697_;
goto v___jp_1604_;
}
else
{
lean_object* v___x_1698_; 
lean_dec(v_a_1694_);
lean_dec(v_binderName_1689_);
lean_inc_ref(v_body_1691_);
v___x_1698_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_body_1691_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1700_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1698_, 1);
lean_inc_ref(v_binderType_1690_);
v___x_1700_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v_binderType_1690_, v_a_1699_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1700_) == 0)
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1711_; 
v_a_1701_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1703_ = v___x_1700_;
v_isShared_1704_ = v_isSharedCheck_1711_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1700_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1711_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1705_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__4, &l_Lean_Meta_Grind_NormSym_pushNot___closed__4_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__4);
v___x_1706_ = l_Lean_mkAppB(v___x_1705_, v_binderType_1690_, v_body_1691_);
v___x_1707_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1707_, 0, v_a_1701_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
lean_ctor_set_uint8(v___x_1707_, sizeof(void*)*2, v___x_1695_);
lean_ctor_set_uint8(v___x_1707_, sizeof(void*)*2 + 1, v___x_1695_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1707_);
v___x_1709_ = v___x_1703_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec_ref(v_body_1691_);
lean_dec_ref(v_binderType_1690_);
v_a_1712_ = lean_ctor_get(v___x_1700_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1700_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1700_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1700_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
lean_dec_ref(v_body_1691_);
lean_dec_ref(v_binderType_1690_);
v_a_1720_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1698_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1698_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
}
else
{
uint8_t v___x_1728_; 
lean_dec(v_a_1694_);
v___x_1728_ = 0;
v___y_1605_ = v_binderType_1690_;
v___y_1606_ = v___y_1680_;
v___y_1607_ = v___y_1681_;
v___y_1608_ = v___y_1686_;
v___y_1609_ = v_binderInfo_1692_;
v___y_1610_ = v___y_1687_;
v___y_1611_ = v___y_1685_;
v___y_1612_ = v___y_1688_;
v___y_1613_ = v___y_1683_;
v___y_1614_ = v_binderName_1689_;
v___y_1615_ = v_body_1691_;
v___y_1616_ = v___y_1684_;
v___y_1617_ = v___y_1682_;
v___y_1618_ = v___x_1728_;
goto v___jp_1604_;
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec_ref(v_body_1691_);
lean_dec_ref(v_binderType_1690_);
lean_dec(v_binderName_1689_);
v_a_1729_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1693_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1693_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_dec_ref(v_arg_1678_);
v___x_1737_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
return v___x_1738_;
}
}
}
v___jp_1604_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
lean_inc_ref(v___y_1615_);
lean_inc_ref(v___y_1605_);
lean_inc(v___y_1614_);
v___x_1619_ = l_Lean_mkLambda(v___y_1614_, v___y_1609_, v___y_1605_, v___y_1615_);
v___x_1620_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v___y_1615_, v___y_1606_, v___y_1607_, v___y_1617_, v___y_1613_, v___y_1616_, v___y_1611_, v___y_1608_, v___y_1610_, v___y_1612_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1622_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v___x_1620_, 1);
lean_inc_ref(v___y_1605_);
v___x_1622_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v___y_1614_, v___y_1609_, v___y_1605_, v_a_1621_, v___y_1613_, v___y_1616_, v___y_1611_, v___y_1608_, v___y_1610_, v___y_1612_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1624_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v___x_1622_, 1);
lean_inc_ref(v___y_1605_);
v___x_1624_ = l_Lean_Meta_Sym_getLevel___redArg(v___y_1605_, v___y_1616_, v___y_1611_, v___y_1608_, v___y_1610_, v___y_1612_);
if (lean_obj_tag(v___x_1624_) == 0)
{
lean_object* v_a_1625_; lean_object* v___x_1626_; 
v_a_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc_n(v_a_1625_, 2);
lean_dec_ref_known(v___x_1624_, 1);
lean_inc_ref(v___y_1605_);
v___x_1626_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg(v_a_1625_, v___y_1605_, v_a_1623_, v___y_1613_, v___y_1616_, v___y_1611_, v___y_1608_, v___y_1610_, v___y_1612_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1640_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1629_ = v___x_1626_;
v_isShared_1630_ = v_isSharedCheck_1640_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1626_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1640_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1638_; 
v___x_1631_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__1));
v___x_1632_ = lean_box(0);
v___x_1633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1633_, 0, v_a_1625_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = l_Lean_mkConst(v___x_1631_, v___x_1633_);
v___x_1635_ = l_Lean_mkAppB(v___x_1634_, v___y_1605_, v___x_1619_);
v___x_1636_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1636_, 0, v_a_1627_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
lean_ctor_set_uint8(v___x_1636_, sizeof(void*)*2, v___y_1618_);
lean_ctor_set_uint8(v___x_1636_, sizeof(void*)*2 + 1, v___y_1618_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v___x_1636_);
v___x_1638_ = v___x_1629_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec(v_a_1625_);
lean_dec_ref(v___x_1619_);
lean_dec_ref(v___y_1605_);
v_a_1641_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1626_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1626_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
else
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
lean_dec(v_a_1623_);
lean_dec_ref(v___x_1619_);
lean_dec_ref(v___y_1605_);
v_a_1649_ = lean_ctor_get(v___x_1624_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1624_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1624_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec_ref(v___x_1619_);
lean_dec_ref(v___y_1605_);
v_a_1657_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1622_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1622_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec_ref(v___x_1619_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1605_);
v_a_1665_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1620_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1620_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
v___jp_1673_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
return v___x_1675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_pushNot___boxed(lean_object* v_e_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Lean_Meta_Grind_NormSym_pushNot(v_e_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
lean_dec(v_a_2144_);
lean_dec_ref(v_a_2143_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
lean_dec(v_a_2136_);
return v_res_2146_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2(void){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2152_ = lean_box(0);
v___x_2153_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__1));
v___x_2154_ = l_Lean_mkConst(v___x_2153_, v___x_2152_);
return v___x_2154_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2160_ = lean_box(0);
v___x_2161_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__4));
v___x_2162_ = l_Lean_mkConst(v___x_2161_, v___x_2160_);
return v___x_2162_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = lean_box(0);
v___x_2167_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__7));
v___x_2168_ = l_Lean_mkConst(v___x_2167_, v___x_2166_);
return v___x_2168_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11(void){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = lean_box(0);
v___x_2173_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__10));
v___x_2174_ = l_Lean_mkConst(v___x_2173_, v___x_2172_);
return v___x_2174_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2180_ = lean_box(0);
v___x_2181_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__13));
v___x_2182_ = l_Lean_mkConst(v___x_2181_, v___x_2180_);
return v___x_2182_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17(void){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2186_ = lean_box(0);
v___x_2187_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__16));
v___x_2188_ = l_Lean_mkConst(v___x_2187_, v___x_2186_);
return v___x_2188_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2192_ = lean_box(0);
v___x_2193_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__19));
v___x_2194_ = l_Lean_mkConst(v___x_2193_, v___x_2192_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg(lean_object* v_e_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
lean_object* v___x_2209_; uint8_t v___x_2210_; 
v___x_2209_ = l_Lean_Expr_cleanupAnnotations(v_e_2195_);
v___x_2210_ = l_Lean_Expr_isApp(v___x_2209_);
if (v___x_2210_ == 0)
{
lean_dec_ref(v___x_2209_);
goto v___jp_2206_;
}
else
{
lean_object* v_arg_2211_; lean_object* v___x_2212_; uint8_t v___x_2213_; 
v_arg_2211_ = lean_ctor_get(v___x_2209_, 1);
lean_inc_ref(v_arg_2211_);
v___x_2212_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2209_);
v___x_2213_ = l_Lean_Expr_isApp(v___x_2212_);
if (v___x_2213_ == 0)
{
lean_dec_ref(v___x_2212_);
lean_dec_ref(v_arg_2211_);
goto v___jp_2206_;
}
else
{
lean_object* v_arg_2214_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___x_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v_arg_2214_ = lean_ctor_get(v___x_2212_, 1);
lean_inc_ref(v_arg_2214_);
v___x_2333_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2212_);
v___x_2334_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1));
v___x_2335_ = l_Lean_Expr_isConstOf(v___x_2333_, v___x_2334_);
lean_dec_ref(v___x_2333_);
if (v___x_2335_ == 0)
{
lean_dec_ref(v_arg_2214_);
lean_dec_ref(v_arg_2211_);
goto v___jp_2206_;
}
else
{
lean_object* v___x_2336_; 
lean_inc_ref(v_arg_2214_);
v___x_2336_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_2214_, v_a_2199_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2396_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2396_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2396_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; 
v___x_2341_ = l_Lean_Expr_cleanupAnnotations(v_a_2337_);
v___x_2342_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__6));
v___x_2343_ = l_Lean_Expr_isConstOf(v___x_2341_, v___x_2342_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; uint8_t v___x_2345_; 
v___x_2344_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_2345_ = l_Lean_Expr_isConstOf(v___x_2341_, v___x_2344_);
if (v___x_2345_ == 0)
{
uint8_t v___x_2346_; 
lean_del_object(v___x_2339_);
v___x_2346_ = l_Lean_Expr_isApp(v___x_2341_);
if (v___x_2346_ == 0)
{
lean_dec_ref(v___x_2341_);
v___y_2216_ = v_a_2196_;
v___y_2217_ = v_a_2197_;
v___y_2218_ = v_a_2198_;
v___y_2219_ = v_a_2199_;
v___y_2220_ = v_a_2200_;
v___y_2221_ = v_a_2201_;
goto v___jp_2215_;
}
else
{
lean_object* v_arg_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v_arg_2347_ = lean_ctor_get(v___x_2341_, 1);
lean_inc_ref(v_arg_2347_);
v___x_2348_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2341_);
v___x_2349_ = l_Lean_Expr_isApp(v___x_2348_);
if (v___x_2349_ == 0)
{
lean_dec_ref(v___x_2348_);
lean_dec_ref(v_arg_2347_);
v___y_2216_ = v_a_2196_;
v___y_2217_ = v_a_2197_;
v___y_2218_ = v_a_2198_;
v___y_2219_ = v_a_2199_;
v___y_2220_ = v_a_2200_;
v___y_2221_ = v_a_2201_;
goto v___jp_2215_;
}
else
{
lean_object* v_arg_2350_; lean_object* v___x_2351_; uint8_t v___x_2352_; 
v_arg_2350_ = lean_ctor_get(v___x_2348_, 1);
lean_inc_ref(v_arg_2350_);
v___x_2351_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2348_);
v___x_2352_ = l_Lean_Expr_isConstOf(v___x_2351_, v___x_2334_);
lean_dec_ref(v___x_2351_);
if (v___x_2352_ == 0)
{
lean_dec_ref(v_arg_2350_);
lean_dec_ref(v_arg_2347_);
v___y_2216_ = v_a_2196_;
v___y_2217_ = v_a_2197_;
v___y_2218_ = v_a_2198_;
v___y_2219_ = v_a_2199_;
v___y_2220_ = v_a_2200_;
v___y_2221_ = v_a_2201_;
goto v___jp_2215_;
}
else
{
lean_object* v___x_2353_; 
lean_dec_ref(v_arg_2214_);
lean_inc_ref(v_arg_2211_);
lean_inc_ref(v_arg_2347_);
v___x_2353_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_arg_2347_, v_arg_2211_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2355_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___x_2353_, 1);
lean_inc_ref(v_arg_2350_);
v___x_2355_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_arg_2350_, v_a_2354_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2366_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2358_ = v___x_2355_;
v_isShared_2359_ = v_isSharedCheck_2366_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2355_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2366_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2364_; 
v___x_2360_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14);
v___x_2361_ = l_Lean_mkApp3(v___x_2360_, v_arg_2350_, v_arg_2347_, v_arg_2211_);
v___x_2362_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2362_, 0, v_a_2356_);
lean_ctor_set(v___x_2362_, 1, v___x_2361_);
lean_ctor_set_uint8(v___x_2362_, sizeof(void*)*2, v___x_2345_);
lean_ctor_set_uint8(v___x_2362_, sizeof(void*)*2 + 1, v___x_2345_);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v___x_2362_);
v___x_2364_ = v___x_2358_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_dec_ref(v_arg_2350_);
lean_dec_ref(v_arg_2347_);
lean_dec_ref(v_arg_2211_);
v_a_2367_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2355_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2355_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec_ref(v_arg_2350_);
lean_dec_ref(v_arg_2347_);
lean_dec_ref(v_arg_2211_);
v_a_2375_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2353_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2353_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2387_; 
lean_dec_ref(v___x_2341_);
v___x_2383_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17);
v___x_2384_ = l_Lean_Expr_app___override(v___x_2383_, v_arg_2211_);
v___x_2385_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2385_, 0, v_arg_2214_);
lean_ctor_set(v___x_2385_, 1, v___x_2384_);
lean_ctor_set_uint8(v___x_2385_, sizeof(void*)*2, v___x_2343_);
lean_ctor_set_uint8(v___x_2385_, sizeof(void*)*2 + 1, v___x_2343_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2385_);
v___x_2387_ = v___x_2339_;
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
lean_object* v___x_2389_; lean_object* v___x_2390_; uint8_t v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2394_; 
lean_dec_ref(v___x_2341_);
lean_dec_ref(v_arg_2214_);
v___x_2389_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20);
lean_inc_ref(v_arg_2211_);
v___x_2390_ = l_Lean_Expr_app___override(v___x_2389_, v_arg_2211_);
v___x_2391_ = 0;
v___x_2392_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2392_, 0, v_arg_2211_);
lean_ctor_set(v___x_2392_, 1, v___x_2390_);
lean_ctor_set_uint8(v___x_2392_, sizeof(void*)*2, v___x_2391_);
lean_ctor_set_uint8(v___x_2392_, sizeof(void*)*2 + 1, v___x_2391_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 0, v___x_2392_);
v___x_2394_ = v___x_2339_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2392_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
lean_dec_ref(v_arg_2214_);
lean_dec_ref(v_arg_2211_);
v_a_2397_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2336_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2336_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
v___jp_2215_:
{
lean_object* v___x_2222_; 
lean_inc_ref(v_arg_2211_);
v___x_2222_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_2211_, v___y_2219_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2324_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2225_ = v___x_2222_;
v_isShared_2226_ = v_isSharedCheck_2324_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2222_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2324_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; uint8_t v___x_2229_; 
v___x_2227_ = l_Lean_Expr_cleanupAnnotations(v_a_2223_);
v___x_2228_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__6));
v___x_2229_ = l_Lean_Expr_isConstOf(v___x_2227_, v___x_2228_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; uint8_t v___x_2231_; 
v___x_2230_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_2231_ = l_Lean_Expr_isConstOf(v___x_2227_, v___x_2230_);
if (v___x_2231_ == 0)
{
uint8_t v___x_2232_; 
lean_dec_ref(v_arg_2211_);
v___x_2232_ = l_Lean_Expr_isApp(v___x_2227_);
if (v___x_2232_ == 0)
{
lean_dec_ref(v___x_2227_);
lean_del_object(v___x_2225_);
lean_dec_ref(v_arg_2214_);
goto v___jp_2203_;
}
else
{
lean_object* v_arg_2233_; lean_object* v___x_2234_; uint8_t v___x_2235_; 
v_arg_2233_ = lean_ctor_get(v___x_2227_, 1);
lean_inc_ref(v_arg_2233_);
v___x_2234_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2227_);
v___x_2235_ = l_Lean_Expr_isApp(v___x_2234_);
if (v___x_2235_ == 0)
{
lean_dec_ref(v___x_2234_);
lean_dec_ref(v_arg_2233_);
lean_del_object(v___x_2225_);
lean_dec_ref(v_arg_2214_);
goto v___jp_2203_;
}
else
{
lean_object* v_arg_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; 
v_arg_2236_ = lean_ctor_get(v___x_2234_, 1);
lean_inc_ref(v_arg_2236_);
v___x_2237_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2234_);
v___x_2238_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1));
v___x_2239_ = l_Lean_Expr_isConstOf(v___x_2237_, v___x_2238_);
lean_dec_ref(v___x_2237_);
if (v___x_2239_ == 0)
{
lean_dec_ref(v_arg_2236_);
lean_dec_ref(v_arg_2233_);
lean_del_object(v___x_2225_);
lean_dec_ref(v_arg_2214_);
goto v___jp_2203_;
}
else
{
uint8_t v___x_2240_; 
v___x_2240_ = l_Lean_Expr_isForall(v_arg_2214_);
if (v___x_2240_ == 0)
{
uint8_t v___x_2241_; 
v___x_2241_ = l_Lean_Expr_isForall(v_arg_2236_);
if (v___x_2241_ == 0)
{
uint8_t v___x_2242_; 
v___x_2242_ = l_Lean_Expr_isForall(v_arg_2233_);
if (v___x_2242_ == 0)
{
lean_object* v___x_2243_; lean_object* v___x_2245_; 
lean_dec_ref(v_arg_2236_);
lean_dec_ref(v_arg_2233_);
lean_dec_ref(v_arg_2214_);
v___x_2243_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2243_, 0, v___x_2242_);
lean_ctor_set_uint8(v___x_2243_, 1, v___x_2242_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v___x_2243_);
v___x_2245_ = v___x_2225_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
else
{
lean_object* v___x_2247_; 
lean_del_object(v___x_2225_);
lean_inc_ref(v_arg_2214_);
lean_inc_ref(v_arg_2236_);
v___x_2247_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_arg_2236_, v_arg_2214_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; lean_object* v___x_2249_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_a_2248_);
lean_dec_ref_known(v___x_2247_, 1);
lean_inc_ref(v_arg_2233_);
v___x_2249_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_arg_2233_, v_a_2248_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2260_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2252_ = v___x_2249_;
v_isShared_2253_ = v_isSharedCheck_2260_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2249_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2260_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2258_; 
v___x_2254_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2);
v___x_2255_ = l_Lean_mkApp3(v___x_2254_, v_arg_2214_, v_arg_2236_, v_arg_2233_);
v___x_2256_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2256_, 0, v_a_2250_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*2, v___x_2241_);
lean_ctor_set_uint8(v___x_2256_, sizeof(void*)*2 + 1, v___x_2241_);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v___x_2256_);
v___x_2258_ = v___x_2252_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2256_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
lean_dec_ref(v_arg_2236_);
lean_dec_ref(v_arg_2233_);
lean_dec_ref(v_arg_2214_);
v_a_2261_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2249_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2249_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_dec_ref(v_arg_2236_);
lean_dec_ref(v_arg_2233_);
lean_dec_ref(v_arg_2214_);
v_a_2269_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2247_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2247_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
}
else
{
lean_object* v___x_2277_; 
lean_del_object(v___x_2225_);
lean_inc_ref(v_arg_2233_);
lean_inc_ref(v_arg_2214_);
v___x_2277_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_arg_2214_, v_arg_2233_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2279_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2278_);
lean_dec_ref_known(v___x_2277_, 1);
lean_inc_ref(v_arg_2236_);
v___x_2279_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_arg_2236_, v_a_2278_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2290_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2282_ = v___x_2279_;
v_isShared_2283_ = v_isSharedCheck_2290_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2290_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2284_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5);
v___x_2285_ = l_Lean_mkApp3(v___x_2284_, v_arg_2214_, v_arg_2236_, v_arg_2233_);
v___x_2286_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2286_, 0, v_a_2280_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
lean_ctor_set_uint8(v___x_2286_, sizeof(void*)*2, v___x_2240_);
lean_ctor_set_uint8(v___x_2286_, sizeof(void*)*2 + 1, v___x_2240_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v___x_2286_);
v___x_2288_ = v___x_2282_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec_ref(v_arg_2236_);
lean_dec_ref(v_arg_2233_);
lean_dec_ref(v_arg_2214_);
v_a_2291_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2279_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2279_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec_ref(v_arg_2236_);
lean_dec_ref(v_arg_2233_);
lean_dec_ref(v_arg_2214_);
v_a_2299_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2277_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2277_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
else
{
lean_object* v___x_2307_; lean_object* v___x_2309_; 
lean_dec_ref(v_arg_2236_);
lean_dec_ref(v_arg_2233_);
lean_dec_ref(v_arg_2214_);
v___x_2307_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2307_, 0, v___x_2231_);
lean_ctor_set_uint8(v___x_2307_, 1, v___x_2231_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v___x_2307_);
v___x_2309_ = v___x_2225_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2307_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
}
else
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2315_; 
lean_dec_ref(v___x_2227_);
v___x_2311_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8);
v___x_2312_ = l_Lean_Expr_app___override(v___x_2311_, v_arg_2214_);
v___x_2313_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2313_, 0, v_arg_2211_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
lean_ctor_set_uint8(v___x_2313_, sizeof(void*)*2, v___x_2229_);
lean_ctor_set_uint8(v___x_2313_, sizeof(void*)*2 + 1, v___x_2229_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v___x_2313_);
v___x_2315_ = v___x_2225_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
else
{
lean_object* v___x_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2322_; 
lean_dec_ref(v___x_2227_);
lean_dec_ref(v_arg_2211_);
v___x_2317_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11);
lean_inc_ref(v_arg_2214_);
v___x_2318_ = l_Lean_Expr_app___override(v___x_2317_, v_arg_2214_);
v___x_2319_ = 0;
v___x_2320_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2320_, 0, v_arg_2214_);
lean_ctor_set(v___x_2320_, 1, v___x_2318_);
lean_ctor_set_uint8(v___x_2320_, sizeof(void*)*2, v___x_2319_);
lean_ctor_set_uint8(v___x_2320_, sizeof(void*)*2 + 1, v___x_2319_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v___x_2320_);
v___x_2322_ = v___x_2225_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2320_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec_ref(v_arg_2214_);
lean_dec_ref(v_arg_2211_);
v_a_2325_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2222_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2222_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
}
v___jp_2203_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2204_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
return v___x_2205_;
}
v___jp_2206_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
return v___x_2208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___boxed(lean_object* v_e_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_Meta_Grind_NormSym_simpOr___redArg(v_e_2405_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr(lean_object* v_e_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_Meta_Grind_NormSym_simpOr___redArg(v_e_2414_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr___boxed(lean_object* v_e_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_Lean_Meta_Grind_NormSym_simpOr(v_e_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
lean_dec(v_a_2435_);
lean_dec_ref(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec(v_a_2427_);
return v_res_2437_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2438_ = lean_box(0);
v___x_2439_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__6));
v___x_2440_ = l_Lean_mkConst(v___x_2439_, v___x_2438_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0(uint8_t v___x_2441_, uint8_t v___x_2442_, lean_object* v_h_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v___y_2455_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2464_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0, &l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0);
lean_inc_ref(v_h_2443_);
v___x_2465_ = l_Lean_Meta_mkNoConfusion(v___x_2464_, v_h_2443_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; uint8_t v___x_2470_; lean_object* v___x_2471_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___x_2465_, 1);
v___x_2467_ = lean_unsigned_to_nat(1u);
v___x_2468_ = lean_mk_empty_array_with_capacity(v___x_2467_);
v___x_2469_ = lean_array_push(v___x_2468_, v_h_2443_);
v___x_2470_ = 1;
v___x_2471_ = l_Lean_Meta_mkLambdaFVars(v___x_2469_, v_a_2466_, v___x_2441_, v___x_2442_, v___x_2441_, v___x_2442_, v___x_2470_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec_ref(v___x_2469_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v___x_2473_; uint8_t v_transparency_2474_; uint8_t v___x_2475_; uint8_t v___x_2476_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
lean_inc(v_a_2472_);
lean_dec_ref_known(v___x_2471_, 1);
v___x_2473_ = l_Lean_Meta_Context_config(v___y_2449_);
v_transparency_2474_ = lean_ctor_get_uint8(v___x_2473_, 9);
lean_dec_ref(v___x_2473_);
v___x_2475_ = 1;
v___x_2476_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2474_, v___x_2475_);
if (v___x_2476_ == 0)
{
lean_object* v_keyedConfig_2477_; uint8_t v_trackZetaDelta_2478_; lean_object* v_zetaDeltaSet_2479_; lean_object* v_lctx_2480_; lean_object* v_localInstances_2481_; lean_object* v_defEqCtx_x3f_2482_; lean_object* v_synthPendingDepth_2483_; lean_object* v_customCanUnfoldPredicate_x3f_2484_; uint8_t v_univApprox_2485_; uint8_t v_inTypeClassResolution_2486_; uint8_t v_cacheInferType_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v_keyedConfig_2477_ = lean_ctor_get(v___y_2449_, 0);
v_trackZetaDelta_2478_ = lean_ctor_get_uint8(v___y_2449_, sizeof(void*)*7);
v_zetaDeltaSet_2479_ = lean_ctor_get(v___y_2449_, 1);
v_lctx_2480_ = lean_ctor_get(v___y_2449_, 2);
v_localInstances_2481_ = lean_ctor_get(v___y_2449_, 3);
v_defEqCtx_x3f_2482_ = lean_ctor_get(v___y_2449_, 4);
v_synthPendingDepth_2483_ = lean_ctor_get(v___y_2449_, 5);
v_customCanUnfoldPredicate_x3f_2484_ = lean_ctor_get(v___y_2449_, 6);
v_univApprox_2485_ = lean_ctor_get_uint8(v___y_2449_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2486_ = lean_ctor_get_uint8(v___y_2449_, sizeof(void*)*7 + 2);
v_cacheInferType_2487_ = lean_ctor_get_uint8(v___y_2449_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2477_);
v___x_2488_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2475_, v_keyedConfig_2477_);
lean_inc(v_customCanUnfoldPredicate_x3f_2484_);
lean_inc(v_synthPendingDepth_2483_);
lean_inc(v_defEqCtx_x3f_2482_);
lean_inc_ref(v_localInstances_2481_);
lean_inc_ref(v_lctx_2480_);
lean_inc(v_zetaDeltaSet_2479_);
v___x_2489_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2489_, 0, v___x_2488_);
lean_ctor_set(v___x_2489_, 1, v_zetaDeltaSet_2479_);
lean_ctor_set(v___x_2489_, 2, v_lctx_2480_);
lean_ctor_set(v___x_2489_, 3, v_localInstances_2481_);
lean_ctor_set(v___x_2489_, 4, v_defEqCtx_x3f_2482_);
lean_ctor_set(v___x_2489_, 5, v_synthPendingDepth_2483_);
lean_ctor_set(v___x_2489_, 6, v_customCanUnfoldPredicate_x3f_2484_);
lean_ctor_set_uint8(v___x_2489_, sizeof(void*)*7, v_trackZetaDelta_2478_);
lean_ctor_set_uint8(v___x_2489_, sizeof(void*)*7 + 1, v_univApprox_2485_);
lean_ctor_set_uint8(v___x_2489_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2486_);
lean_ctor_set_uint8(v___x_2489_, sizeof(void*)*7 + 3, v_cacheInferType_2487_);
v___x_2490_ = l_Lean_Meta_mkEqFalse_x27(v_a_2472_, v___x_2489_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec_ref_known(v___x_2489_, 7);
v___y_2455_ = v___x_2490_;
goto v___jp_2454_;
}
else
{
lean_object* v___x_2491_; 
v___x_2491_ = l_Lean_Meta_mkEqFalse_x27(v_a_2472_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
v___y_2455_ = v___x_2491_;
goto v___jp_2454_;
}
}
else
{
return v___x_2471_;
}
}
else
{
lean_dec_ref(v_h_2443_);
return v___x_2465_;
}
v___jp_2454_:
{
if (lean_obj_tag(v___y_2455_) == 0)
{
return v___y_2455_;
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
v_a_2456_ = lean_ctor_get(v___y_2455_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___y_2455_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___y_2455_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___y_2455_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___boxed(lean_object* v___x_2492_, lean_object* v___x_2493_, lean_object* v_h_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
uint8_t v___x_16179__boxed_2505_; uint8_t v___x_16180__boxed_2506_; lean_object* v_res_2507_; 
v___x_16179__boxed_2505_ = lean_unbox(v___x_2492_);
v___x_16180__boxed_2506_ = lean_unbox(v___x_2493_);
v_res_2507_ = l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0(v___x_16179__boxed_2505_, v___x_16180__boxed_2506_, v_h_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0(lean_object* v_k_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v_b_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v___x_2520_; 
lean_inc(v___y_2518_);
lean_inc_ref(v___y_2517_);
lean_inc(v___y_2516_);
lean_inc_ref(v___y_2515_);
lean_inc(v___y_2513_);
lean_inc_ref(v___y_2512_);
lean_inc(v___y_2511_);
lean_inc_ref(v___y_2510_);
lean_inc(v___y_2509_);
v___x_2520_ = lean_apply_11(v_k_2508_, v_b_2514_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, lean_box(0));
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v_b_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0(v_k_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v_b_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(lean_object* v_name_2534_, uint8_t v_bi_2535_, lean_object* v_type_2536_, lean_object* v_k_2537_, uint8_t v_kind_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v___f_2549_; lean_object* v___x_2550_; 
lean_inc(v___y_2543_);
lean_inc_ref(v___y_2542_);
lean_inc(v___y_2541_);
lean_inc_ref(v___y_2540_);
lean_inc(v___y_2539_);
v___f_2549_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_2549_, 0, v_k_2537_);
lean_closure_set(v___f_2549_, 1, v___y_2539_);
lean_closure_set(v___f_2549_, 2, v___y_2540_);
lean_closure_set(v___f_2549_, 3, v___y_2541_);
lean_closure_set(v___f_2549_, 4, v___y_2542_);
lean_closure_set(v___f_2549_, 5, v___y_2543_);
v___x_2550_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2534_, v_bi_2535_, v_type_2536_, v___f_2549_, v_kind_2538_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_);
if (lean_obj_tag(v___x_2550_) == 0)
{
return v___x_2550_;
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2550_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2550_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___boxed(lean_object* v_name_2559_, lean_object* v_bi_2560_, lean_object* v_type_2561_, lean_object* v_k_2562_, lean_object* v_kind_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
uint8_t v_bi_boxed_2574_; uint8_t v_kind_boxed_2575_; lean_object* v_res_2576_; 
v_bi_boxed_2574_ = lean_unbox(v_bi_2560_);
v_kind_boxed_2575_ = lean_unbox(v_kind_2563_);
v_res_2576_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(v_name_2559_, v_bi_boxed_2574_, v_type_2561_, v_k_2562_, v_kind_boxed_2575_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(lean_object* v_name_2577_, lean_object* v_type_2578_, lean_object* v_k_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
uint8_t v___x_2590_; uint8_t v___x_2591_; lean_object* v___x_2592_; 
v___x_2590_ = 0;
v___x_2591_ = 0;
v___x_2592_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(v_name_2577_, v___x_2590_, v_type_2578_, v_k_2579_, v___x_2591_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg___boxed(lean_object* v_name_2593_, lean_object* v_type_2594_, lean_object* v_k_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_name_2593_, v_type_2594_, v_k_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq(lean_object* v_e_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_){
_start:
{
lean_object* v___x_2624_; uint8_t v___x_2625_; 
lean_inc_ref(v_e_2610_);
v___x_2624_ = l_Lean_Expr_cleanupAnnotations(v_e_2610_);
v___x_2625_ = l_Lean_Expr_isApp(v___x_2624_);
if (v___x_2625_ == 0)
{
lean_dec_ref(v___x_2624_);
lean_dec_ref(v_e_2610_);
goto v___jp_2621_;
}
else
{
lean_object* v_arg_2626_; lean_object* v___x_2627_; uint8_t v___x_2628_; 
v_arg_2626_ = lean_ctor_get(v___x_2624_, 1);
lean_inc_ref(v_arg_2626_);
v___x_2627_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2624_);
v___x_2628_ = l_Lean_Expr_isApp(v___x_2627_);
if (v___x_2628_ == 0)
{
lean_dec_ref(v___x_2627_);
lean_dec_ref(v_arg_2626_);
lean_dec_ref(v_e_2610_);
goto v___jp_2621_;
}
else
{
lean_object* v_arg_2629_; lean_object* v___x_2630_; uint8_t v___x_2631_; 
v_arg_2629_ = lean_ctor_get(v___x_2627_, 1);
lean_inc_ref(v_arg_2629_);
v___x_2630_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2627_);
v___x_2631_ = l_Lean_Expr_isApp(v___x_2630_);
if (v___x_2631_ == 0)
{
lean_dec_ref(v___x_2630_);
lean_dec_ref(v_arg_2629_);
lean_dec_ref(v_arg_2626_);
lean_dec_ref(v_e_2610_);
goto v___jp_2621_;
}
else
{
lean_object* v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; 
v___x_2632_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2630_);
v___x_2633_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__1));
v___x_2634_ = l_Lean_Expr_isConstOf(v___x_2632_, v___x_2633_);
lean_dec_ref(v___x_2632_);
if (v___x_2634_ == 0)
{
lean_dec_ref(v_arg_2629_);
lean_dec_ref(v_arg_2626_);
lean_dec_ref(v_e_2610_);
goto v___jp_2621_;
}
else
{
lean_object* v___x_2635_; 
v___x_2635_ = l_Lean_Meta_isConstructorApp_x3f(v_arg_2629_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2705_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2638_ = v___x_2635_;
v_isShared_2639_ = v_isSharedCheck_2705_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2635_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2705_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
if (lean_obj_tag(v_a_2636_) == 1)
{
lean_object* v_val_2640_; lean_object* v___x_2641_; 
lean_del_object(v___x_2638_);
v_val_2640_ = lean_ctor_get(v_a_2636_, 0);
lean_inc(v_val_2640_);
lean_dec_ref_known(v_a_2636_, 1);
v___x_2641_ = l_Lean_Meta_isConstructorApp_x3f(v_arg_2626_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2692_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2644_ = v___x_2641_;
v_isShared_2645_ = v_isSharedCheck_2692_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2641_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2692_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
if (lean_obj_tag(v_a_2642_) == 1)
{
lean_object* v_toConstantVal_2646_; lean_object* v_val_2647_; lean_object* v_toConstantVal_2648_; lean_object* v_name_2649_; lean_object* v_name_2650_; uint8_t v___x_2651_; 
v_toConstantVal_2646_ = lean_ctor_get(v_val_2640_, 0);
lean_inc_ref(v_toConstantVal_2646_);
lean_dec(v_val_2640_);
v_val_2647_ = lean_ctor_get(v_a_2642_, 0);
lean_inc(v_val_2647_);
lean_dec_ref_known(v_a_2642_, 1);
v_toConstantVal_2648_ = lean_ctor_get(v_val_2647_, 0);
lean_inc_ref(v_toConstantVal_2648_);
lean_dec(v_val_2647_);
v_name_2649_ = lean_ctor_get(v_toConstantVal_2646_, 0);
lean_inc(v_name_2649_);
lean_dec_ref(v_toConstantVal_2646_);
v_name_2650_ = lean_ctor_get(v_toConstantVal_2648_, 0);
lean_inc(v_name_2650_);
lean_dec_ref(v_toConstantVal_2648_);
v___x_2651_ = lean_name_eq(v_name_2649_, v_name_2650_);
lean_dec(v_name_2650_);
lean_dec(v_name_2649_);
if (v___x_2651_ == 0)
{
lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___f_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
lean_del_object(v___x_2644_);
v___x_2652_ = lean_box(v___x_2651_);
v___x_2653_ = lean_box(v___x_2634_);
v___f_2654_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2654_, 0, v___x_2652_);
lean_closure_set(v___f_2654_, 1, v___x_2653_);
v___x_2655_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_reduceCtorEq___closed__1));
v___x_2656_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v___x_2655_, v_e_2610_, v___f_2654_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2658_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2614_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2667_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2661_ = v___x_2658_;
v_isShared_2662_ = v_isSharedCheck_2667_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2658_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2667_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2663_; lean_object* v___x_2665_; 
v___x_2663_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2663_, 0, v_a_2659_);
lean_ctor_set(v___x_2663_, 1, v_a_2657_);
lean_ctor_set_uint8(v___x_2663_, sizeof(void*)*2, v___x_2634_);
lean_ctor_set_uint8(v___x_2663_, sizeof(void*)*2 + 1, v___x_2651_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___x_2663_);
v___x_2665_ = v___x_2661_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2663_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec(v_a_2657_);
v_a_2668_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2658_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2658_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
v_a_2676_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2656_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2656_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
else
{
lean_object* v___x_2684_; lean_object* v___x_2686_; 
lean_dec_ref(v_e_2610_);
v___x_2684_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v___x_2684_);
v___x_2686_ = v___x_2644_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2684_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
else
{
lean_object* v___x_2688_; lean_object* v___x_2690_; 
lean_dec(v_a_2642_);
lean_dec(v_val_2640_);
lean_dec_ref(v_e_2610_);
v___x_2688_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v___x_2688_);
v___x_2690_ = v___x_2644_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2688_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_dec(v_val_2640_);
lean_dec_ref(v_e_2610_);
v_a_2693_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2641_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2641_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
else
{
lean_object* v___x_2701_; lean_object* v___x_2703_; 
lean_dec(v_a_2636_);
lean_dec_ref(v_arg_2626_);
lean_dec_ref(v_e_2610_);
v___x_2701_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_2639_ == 0)
{
lean_ctor_set(v___x_2638_, 0, v___x_2701_);
v___x_2703_ = v___x_2638_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
else
{
lean_object* v_a_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2713_; 
lean_dec_ref(v_arg_2626_);
lean_dec_ref(v_e_2610_);
v_a_2706_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2713_ == 0)
{
v___x_2708_ = v___x_2635_;
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_a_2706_);
lean_dec(v___x_2635_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2713_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2711_; 
if (v_isShared_2709_ == 0)
{
v___x_2711_ = v___x_2708_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
v___x_2711_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
return v___x_2711_;
}
}
}
}
}
}
}
v___jp_2621_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2622_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
return v___x_2623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___boxed(lean_object* v_e_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_Meta_Grind_NormSym_reduceCtorEq(v_e_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0(lean_object* v_00_u03b1_2726_, lean_object* v_name_2727_, uint8_t v_bi_2728_, lean_object* v_type_2729_, lean_object* v_k_2730_, uint8_t v_kind_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(v_name_2727_, v_bi_2728_, v_type_2729_, v_k_2730_, v_kind_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2743_, lean_object* v_name_2744_, lean_object* v_bi_2745_, lean_object* v_type_2746_, lean_object* v_k_2747_, lean_object* v_kind_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
uint8_t v_bi_boxed_2759_; uint8_t v_kind_boxed_2760_; lean_object* v_res_2761_; 
v_bi_boxed_2759_ = lean_unbox(v_bi_2745_);
v_kind_boxed_2760_ = lean_unbox(v_kind_2748_);
v_res_2761_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0(v_00_u03b1_2743_, v_name_2744_, v_bi_boxed_2759_, v_type_2746_, v_k_2747_, v_kind_boxed_2760_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0(lean_object* v_00_u03b1_2762_, lean_object* v_name_2763_, lean_object* v_type_2764_, lean_object* v_k_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_name_2763_, v_type_2764_, v_k_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___boxed(lean_object* v_00_u03b1_2777_, lean_object* v_name_2778_, lean_object* v_type_2779_, lean_object* v_k_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0(v_00_u03b1_2777_, v_name_2778_, v_type_2779_, v_k_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec(v___y_2781_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(lean_object* v_e_2792_){
_start:
{
if (lean_obj_tag(v_e_2792_) == 7)
{
lean_object* v_binderName_2793_; lean_object* v_binderType_2794_; lean_object* v_body_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v_binderName_2793_ = lean_ctor_get(v_e_2792_, 0);
v_binderType_2794_ = lean_ctor_get(v_e_2792_, 1);
v_body_2795_ = lean_ctor_get(v_e_2792_, 2);
lean_inc_ref(v_body_2795_);
lean_inc_ref(v_binderType_2794_);
v___x_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2796_, 0, v_binderType_2794_);
lean_ctor_set(v___x_2796_, 1, v_body_2795_);
lean_inc(v_binderName_2793_);
v___x_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2797_, 0, v_binderName_2793_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
v___x_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
return v___x_2798_;
}
else
{
lean_object* v___x_2799_; lean_object* v___x_2800_; uint8_t v___x_2801_; 
v___x_2799_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS___closed__1));
v___x_2800_ = lean_unsigned_to_nat(1u);
v___x_2801_ = l_Lean_Expr_isAppOfArity(v_e_2792_, v___x_2799_, v___x_2800_);
if (v___x_2801_ == 0)
{
lean_object* v___x_2802_; 
v___x_2802_ = lean_box(0);
return v___x_2802_;
}
else
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2803_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__28));
v___x_2804_ = l_Lean_Expr_appArg_x21(v_e_2792_);
v___x_2805_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0, &l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0);
v___x_2806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2804_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
v___x_2807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2803_);
lean_ctor_set(v___x_2807_, 1, v___x_2806_);
v___x_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
return v___x_2808_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f___boxed(lean_object* v_e_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(v_e_2809_);
lean_dec_ref(v_e_2809_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0(lean_object* v_fst_2811_, lean_object* v_a_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = lean_expr_instantiate1(v_fst_2811_, v_a_2812_);
v___x_2824_ = l_Lean_Meta_getLevel(v___x_2823_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0___boxed(lean_object* v_fst_2825_, lean_object* v_a_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0(v_fst_2825_, v_a_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec_ref(v_a_2826_);
lean_dec_ref(v_fst_2825_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f(lean_object* v_e_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_){
_start:
{
if (lean_obj_tag(v_e_2848_) == 7)
{
lean_object* v_binderName_2862_; lean_object* v_binderType_2863_; lean_object* v_body_2864_; uint8_t v_binderInfo_2865_; lean_object* v___x_2866_; uint8_t v___x_2867_; 
v_binderName_2862_ = lean_ctor_get(v_e_2848_, 0);
lean_inc(v_binderName_2862_);
v_binderType_2863_ = lean_ctor_get(v_e_2848_, 1);
lean_inc_ref(v_binderType_2863_);
v_body_2864_ = lean_ctor_get(v_e_2848_, 2);
lean_inc_ref(v_body_2864_);
v_binderInfo_2865_ = lean_ctor_get_uint8(v_e_2848_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2848_, 3);
v___x_2866_ = l_Lean_Expr_cleanupAnnotations(v_body_2864_);
v___x_2867_ = l_Lean_Expr_isApp(v___x_2866_);
if (v___x_2867_ == 0)
{
lean_dec_ref(v___x_2866_);
lean_dec_ref(v_binderType_2863_);
lean_dec(v_binderName_2862_);
goto v___jp_2859_;
}
else
{
lean_object* v_arg_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; 
v_arg_2868_ = lean_ctor_get(v___x_2866_, 1);
lean_inc_ref(v_arg_2868_);
v___x_2869_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2866_);
v___x_2870_ = l_Lean_Expr_isApp(v___x_2869_);
if (v___x_2870_ == 0)
{
lean_dec_ref(v___x_2869_);
lean_dec_ref(v_arg_2868_);
lean_dec_ref(v_binderType_2863_);
lean_dec(v_binderName_2862_);
goto v___jp_2859_;
}
else
{
lean_object* v_arg_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; uint8_t v___x_2874_; 
v_arg_2871_ = lean_ctor_get(v___x_2869_, 1);
lean_inc_ref(v_arg_2871_);
v___x_2872_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2869_);
v___x_2873_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1));
v___x_2874_ = l_Lean_Expr_isConstOf(v___x_2872_, v___x_2873_);
lean_dec_ref(v___x_2872_);
if (v___x_2874_ == 0)
{
lean_dec_ref(v_arg_2871_);
lean_dec_ref(v_arg_2868_);
lean_dec_ref(v_binderType_2863_);
lean_dec(v_binderName_2862_);
goto v___jp_2859_;
}
else
{
lean_object* v___x_2875_; 
v___x_2875_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(v_arg_2871_);
if (lean_obj_tag(v___x_2875_) == 1)
{
lean_object* v_val_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2982_; 
lean_dec_ref(v_arg_2871_);
v_val_2876_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2878_ = v___x_2875_;
v_isShared_2879_ = v_isSharedCheck_2982_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_val_2876_);
lean_dec(v___x_2875_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2982_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v_snd_2880_; lean_object* v_fst_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2981_; 
v_snd_2880_ = lean_ctor_get(v_val_2876_, 1);
v_fst_2881_ = lean_ctor_get(v_val_2876_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_val_2876_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2883_ = v_val_2876_;
v_isShared_2884_ = v_isSharedCheck_2981_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_snd_2880_);
lean_inc(v_fst_2881_);
lean_dec(v_val_2876_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2981_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v_fst_2885_; lean_object* v_snd_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2980_; 
v_fst_2885_ = lean_ctor_get(v_snd_2880_, 0);
v_snd_2886_ = lean_ctor_get(v_snd_2880_, 1);
v_isSharedCheck_2980_ = !lean_is_exclusive(v_snd_2880_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2888_ = v_snd_2880_;
v_isShared_2889_ = v_isSharedCheck_2980_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_snd_2886_);
lean_inc(v_fst_2885_);
lean_dec(v_snd_2880_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2980_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___f_2890_; lean_object* v_p_2891_; uint8_t v___x_2892_; lean_object* v___x_2893_; lean_object* v_q_2894_; lean_object* v_00_u03b2_2895_; lean_object* v___x_2896_; 
lean_inc_n(v_fst_2885_, 3);
v___f_2890_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2890_, 0, v_fst_2885_);
lean_inc_ref(v_arg_2868_);
lean_inc_ref_n(v_binderType_2863_, 4);
lean_inc_n(v_binderName_2862_, 3);
v_p_2891_ = l_Lean_mkLambda(v_binderName_2862_, v_binderInfo_2865_, v_binderType_2863_, v_arg_2868_);
v___x_2892_ = 0;
lean_inc(v_snd_2886_);
lean_inc(v_fst_2881_);
v___x_2893_ = l_Lean_mkLambda(v_fst_2881_, v___x_2892_, v_fst_2885_, v_snd_2886_);
v_q_2894_ = l_Lean_mkLambda(v_binderName_2862_, v_binderInfo_2865_, v_binderType_2863_, v___x_2893_);
v_00_u03b2_2895_ = l_Lean_mkLambda(v_binderName_2862_, v_binderInfo_2865_, v_binderType_2863_, v_fst_2885_);
v___x_2896_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2863_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2898_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_a_2897_);
lean_dec_ref_known(v___x_2896_, 1);
lean_inc_ref(v_binderType_2863_);
lean_inc(v_binderName_2862_);
v___x_2898_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_binderName_2862_, v_binderType_2863_, v___f_2890_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_a_2899_);
lean_dec_ref_known(v___x_2898_, 1);
v___x_2900_ = lean_unsigned_to_nat(0u);
v___x_2901_ = lean_unsigned_to_nat(1u);
v___x_2902_ = lean_expr_lift_loose_bvars(v_arg_2868_, v___x_2900_, v___x_2901_);
lean_dec_ref(v_arg_2868_);
v___x_2903_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2902_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2905_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v___x_2905_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_snd_2886_, v_a_2904_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2907_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref_known(v___x_2905_, 1);
v___x_2907_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_fst_2881_, v___x_2892_, v_fst_2885_, v_a_2906_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v___x_2909_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2908_);
lean_dec_ref_known(v___x_2907_, 1);
lean_inc_ref(v_binderType_2863_);
v___x_2909_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_binderName_2862_, v_binderInfo_2865_, v_binderType_2863_, v_a_2908_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2931_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2912_ = v___x_2909_;
v_isShared_2913_ = v_isSharedCheck_2931_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2909_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2931_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2917_; 
v___x_2914_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__1));
v___x_2915_ = lean_box(0);
if (v_isShared_2884_ == 0)
{
lean_ctor_set_tag(v___x_2883_, 1);
lean_ctor_set(v___x_2883_, 1, v___x_2915_);
lean_ctor_set(v___x_2883_, 0, v_a_2899_);
v___x_2917_ = v___x_2883_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2899_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v___x_2915_);
v___x_2917_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2922_; 
v___x_2918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2918_, 0, v_a_2897_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
v___x_2919_ = l_Lean_mkConst(v___x_2914_, v___x_2918_);
v___x_2920_ = l_Lean_mkApp4(v___x_2919_, v_binderType_2863_, v_00_u03b2_2895_, v_p_2891_, v_q_2894_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 1, v___x_2920_);
lean_ctor_set(v___x_2888_, 0, v_a_2910_);
v___x_2922_ = v___x_2888_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2910_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v___x_2920_);
v___x_2922_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2924_; 
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v___x_2922_);
v___x_2924_ = v___x_2878_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v___x_2922_);
v___x_2924_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
lean_object* v___x_2926_; 
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 0, v___x_2924_);
v___x_2926_ = v___x_2912_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v___x_2924_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
}
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
lean_dec(v_a_2899_);
lean_dec(v_a_2897_);
lean_dec_ref(v_00_u03b2_2895_);
lean_dec_ref(v_q_2894_);
lean_dec_ref(v_p_2891_);
lean_del_object(v___x_2888_);
lean_del_object(v___x_2883_);
lean_del_object(v___x_2878_);
lean_dec_ref(v_binderType_2863_);
v_a_2932_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2934_ = v___x_2909_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2909_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
else
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2947_; 
lean_dec(v_a_2899_);
lean_dec(v_a_2897_);
lean_dec_ref(v_00_u03b2_2895_);
lean_dec_ref(v_q_2894_);
lean_dec_ref(v_p_2891_);
lean_del_object(v___x_2888_);
lean_del_object(v___x_2883_);
lean_del_object(v___x_2878_);
lean_dec_ref(v_binderType_2863_);
lean_dec(v_binderName_2862_);
v_a_2940_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2942_ = v___x_2907_;
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2907_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
lean_dec(v_a_2899_);
lean_dec(v_a_2897_);
lean_dec_ref(v_00_u03b2_2895_);
lean_dec_ref(v_q_2894_);
lean_dec_ref(v_p_2891_);
lean_del_object(v___x_2888_);
lean_dec(v_fst_2885_);
lean_del_object(v___x_2883_);
lean_dec(v_fst_2881_);
lean_del_object(v___x_2878_);
lean_dec_ref(v_binderType_2863_);
lean_dec(v_binderName_2862_);
v_a_2948_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2905_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2905_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
else
{
lean_object* v_a_2956_; lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2963_; 
lean_dec(v_a_2899_);
lean_dec(v_a_2897_);
lean_dec_ref(v_00_u03b2_2895_);
lean_dec_ref(v_q_2894_);
lean_dec_ref(v_p_2891_);
lean_del_object(v___x_2888_);
lean_dec(v_snd_2886_);
lean_dec(v_fst_2885_);
lean_del_object(v___x_2883_);
lean_dec(v_fst_2881_);
lean_del_object(v___x_2878_);
lean_dec_ref(v_binderType_2863_);
lean_dec(v_binderName_2862_);
v_a_2956_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2963_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2958_ = v___x_2903_;
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
else
{
lean_inc(v_a_2956_);
lean_dec(v___x_2903_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2963_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v_a_2956_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_dec(v_a_2897_);
lean_dec_ref(v_00_u03b2_2895_);
lean_dec_ref(v_q_2894_);
lean_dec_ref(v_p_2891_);
lean_del_object(v___x_2888_);
lean_dec(v_snd_2886_);
lean_dec(v_fst_2885_);
lean_del_object(v___x_2883_);
lean_dec(v_fst_2881_);
lean_del_object(v___x_2878_);
lean_dec_ref(v_arg_2868_);
lean_dec_ref(v_binderType_2863_);
lean_dec(v_binderName_2862_);
v_a_2964_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2898_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2898_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
else
{
lean_object* v_a_2972_; lean_object* v___x_2974_; uint8_t v_isShared_2975_; uint8_t v_isSharedCheck_2979_; 
lean_dec_ref(v_00_u03b2_2895_);
lean_dec_ref(v_q_2894_);
lean_dec_ref(v_p_2891_);
lean_dec_ref(v___f_2890_);
lean_del_object(v___x_2888_);
lean_dec(v_snd_2886_);
lean_dec(v_fst_2885_);
lean_del_object(v___x_2883_);
lean_dec(v_fst_2881_);
lean_del_object(v___x_2878_);
lean_dec_ref(v_arg_2868_);
lean_dec_ref(v_binderType_2863_);
lean_dec(v_binderName_2862_);
v_a_2972_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2979_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2979_ == 0)
{
v___x_2974_ = v___x_2896_;
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
else
{
lean_inc(v_a_2972_);
lean_dec(v___x_2896_);
v___x_2974_ = lean_box(0);
v_isShared_2975_ = v_isSharedCheck_2979_;
goto v_resetjp_2973_;
}
v_resetjp_2973_:
{
lean_object* v___x_2977_; 
if (v_isShared_2975_ == 0)
{
v___x_2977_ = v___x_2974_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_a_2972_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2983_; 
lean_dec(v___x_2875_);
v___x_2983_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(v_arg_2868_);
lean_dec_ref(v_arg_2868_);
if (lean_obj_tag(v___x_2983_) == 1)
{
lean_object* v_val_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_3090_; 
v_val_2984_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_2986_ = v___x_2983_;
v_isShared_2987_ = v_isSharedCheck_3090_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_val_2984_);
lean_dec(v___x_2983_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_3090_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v_snd_2988_; lean_object* v_fst_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3089_; 
v_snd_2988_ = lean_ctor_get(v_val_2984_, 1);
v_fst_2989_ = lean_ctor_get(v_val_2984_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v_val_2984_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_2991_ = v_val_2984_;
v_isShared_2992_ = v_isSharedCheck_3089_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_snd_2988_);
lean_inc(v_fst_2989_);
lean_dec(v_val_2984_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3089_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v_fst_2993_; lean_object* v_snd_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3088_; 
v_fst_2993_ = lean_ctor_get(v_snd_2988_, 0);
v_snd_2994_ = lean_ctor_get(v_snd_2988_, 1);
v_isSharedCheck_3088_ = !lean_is_exclusive(v_snd_2988_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_2996_ = v_snd_2988_;
v_isShared_2997_ = v_isSharedCheck_3088_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_snd_2994_);
lean_inc(v_fst_2993_);
lean_dec(v_snd_2988_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3088_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___f_2998_; lean_object* v_p_2999_; uint8_t v___x_3000_; lean_object* v___x_3001_; lean_object* v_q_3002_; lean_object* v_00_u03b2_3003_; lean_object* v___x_3004_; 
lean_inc_n(v_fst_2993_, 3);
v___f_2998_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2998_, 0, v_fst_2993_);
lean_inc_ref(v_arg_2871_);
lean_inc_ref_n(v_binderType_2863_, 4);
lean_inc_n(v_binderName_2862_, 3);
v_p_2999_ = l_Lean_mkLambda(v_binderName_2862_, v_binderInfo_2865_, v_binderType_2863_, v_arg_2871_);
v___x_3000_ = 0;
lean_inc(v_snd_2994_);
lean_inc(v_fst_2989_);
v___x_3001_ = l_Lean_mkLambda(v_fst_2989_, v___x_3000_, v_fst_2993_, v_snd_2994_);
v_q_3002_ = l_Lean_mkLambda(v_binderName_2862_, v_binderInfo_2865_, v_binderType_2863_, v___x_3001_);
v_00_u03b2_3003_ = l_Lean_mkLambda(v_binderName_2862_, v_binderInfo_2865_, v_binderType_2863_, v_fst_2993_);
v___x_3004_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2863_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3006_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3004_, 1);
lean_inc_ref(v_binderType_2863_);
lean_inc(v_binderName_2862_);
v___x_3006_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_binderName_2862_, v_binderType_2863_, v___f_2998_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
v___x_3008_ = lean_unsigned_to_nat(0u);
v___x_3009_ = lean_unsigned_to_nat(1u);
v___x_3010_ = lean_expr_lift_loose_bvars(v_arg_2871_, v___x_3008_, v___x_3009_);
lean_dec_ref(v_arg_2871_);
v___x_3011_ = l_Lean_Meta_Sym_shareCommonInc(v___x_3010_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3013_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3011_, 1);
v___x_3013_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_a_3012_, v_snd_2994_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3015_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_a_3014_);
lean_dec_ref_known(v___x_3013_, 1);
v___x_3015_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_fst_2989_, v___x_3000_, v_fst_2993_, v_a_3014_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3017_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3015_, 1);
lean_inc_ref(v_binderType_2863_);
v___x_3017_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_binderName_2862_, v_binderInfo_2865_, v_binderType_2863_, v_a_3016_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3039_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3020_ = v___x_3017_;
v_isShared_3021_ = v_isSharedCheck_3039_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3017_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3039_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3025_; 
v___x_3022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__3));
v___x_3023_ = lean_box(0);
if (v_isShared_2992_ == 0)
{
lean_ctor_set_tag(v___x_2991_, 1);
lean_ctor_set(v___x_2991_, 1, v___x_3023_);
lean_ctor_set(v___x_2991_, 0, v_a_3007_);
v___x_3025_ = v___x_2991_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3007_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3030_; 
v___x_3026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3026_, 0, v_a_3005_);
lean_ctor_set(v___x_3026_, 1, v___x_3025_);
v___x_3027_ = l_Lean_mkConst(v___x_3022_, v___x_3026_);
v___x_3028_ = l_Lean_mkApp4(v___x_3027_, v_binderType_2863_, v_00_u03b2_3003_, v_p_2999_, v_q_3002_);
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 1, v___x_3028_);
lean_ctor_set(v___x_2996_, 0, v_a_3018_);
v___x_3030_ = v___x_2996_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3018_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3032_; 
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 0, v___x_3030_);
v___x_3032_ = v___x_2986_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3030_);
v___x_3032_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
lean_object* v___x_3034_; 
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 0, v___x_3032_);
v___x_3034_ = v___x_3020_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
}
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
lean_dec(v_a_3007_);
lean_dec(v_a_3005_);
lean_dec_ref(v_00_u03b2_3003_);
lean_dec_ref(v_q_3002_);
lean_dec_ref(v_p_2999_);
lean_del_object(v___x_2996_);
lean_del_object(v___x_2991_);
lean_del_object(v___x_2986_);
lean_dec_ref(v_binderType_2863_);
v_a_3040_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_3017_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_3017_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3043_ == 0)
{
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_dec(v_a_3007_);
lean_dec(v_a_3005_);
lean_dec_ref(v_00_u03b2_3003_);
lean_dec_ref(v_q_3002_);
lean_dec_ref(v_p_2999_);
lean_del_object(v___x_2996_);
lean_del_object(v___x_2991_);
lean_del_object(v___x_2986_);
lean_dec_ref(v_binderType_2863_);
lean_dec(v_binderName_2862_);
v_a_3048_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_3015_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3015_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec(v_a_3007_);
lean_dec(v_a_3005_);
lean_dec_ref(v_00_u03b2_3003_);
lean_dec_ref(v_q_3002_);
lean_dec_ref(v_p_2999_);
lean_del_object(v___x_2996_);
lean_dec(v_fst_2993_);
lean_del_object(v___x_2991_);
lean_dec(v_fst_2989_);
lean_del_object(v___x_2986_);
lean_dec_ref(v_binderType_2863_);
lean_dec(v_binderName_2862_);
v_a_3056_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3013_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3013_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec(v_a_3007_);
lean_dec(v_a_3005_);
lean_dec_ref(v_00_u03b2_3003_);
lean_dec_ref(v_q_3002_);
lean_dec_ref(v_p_2999_);
lean_del_object(v___x_2996_);
lean_dec(v_snd_2994_);
lean_dec(v_fst_2993_);
lean_del_object(v___x_2991_);
lean_dec(v_fst_2989_);
lean_del_object(v___x_2986_);
lean_dec_ref(v_binderType_2863_);
lean_dec(v_binderName_2862_);
v_a_3064_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3011_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3011_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
else
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
lean_dec(v_a_3005_);
lean_dec_ref(v_00_u03b2_3003_);
lean_dec_ref(v_q_3002_);
lean_dec_ref(v_p_2999_);
lean_del_object(v___x_2996_);
lean_dec(v_snd_2994_);
lean_dec(v_fst_2993_);
lean_del_object(v___x_2991_);
lean_dec(v_fst_2989_);
lean_del_object(v___x_2986_);
lean_dec_ref(v_arg_2871_);
lean_dec_ref(v_binderType_2863_);
lean_dec(v_binderName_2862_);
v_a_3072_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_3006_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3006_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3075_ == 0)
{
v___x_3077_ = v___x_3074_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3072_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec_ref(v_00_u03b2_3003_);
lean_dec_ref(v_q_3002_);
lean_dec_ref(v_p_2999_);
lean_dec_ref(v___f_2998_);
lean_del_object(v___x_2996_);
lean_dec(v_snd_2994_);
lean_dec(v_fst_2993_);
lean_del_object(v___x_2991_);
lean_dec(v_fst_2989_);
lean_del_object(v___x_2986_);
lean_dec_ref(v_arg_2871_);
lean_dec_ref(v_binderType_2863_);
lean_dec(v_binderName_2862_);
v_a_3080_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3004_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3004_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
lean_dec(v___x_2983_);
lean_dec_ref(v_arg_2871_);
lean_dec_ref(v_binderType_2863_);
lean_dec(v_binderName_2862_);
v___x_3091_ = lean_box(0);
v___x_3092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3092_, 0, v___x_3091_);
return v___x_3092_;
}
}
}
}
}
}
else
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
lean_dec_ref(v_e_2848_);
v___x_3093_ = lean_box(0);
v___x_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
return v___x_3094_;
}
v___jp_2859_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_box(0);
v___x_2861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
return v___x_2861_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___boxed(lean_object* v_e_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_, lean_object* v_a_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f(v_e_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_);
lean_dec(v_a_3104_);
lean_dec_ref(v_a_3103_);
lean_dec(v_a_3102_);
lean_dec_ref(v_a_3101_);
lean_dec(v_a_3100_);
lean_dec_ref(v_a_3099_);
lean_dec(v_a_3098_);
lean_dec_ref(v_a_3097_);
lean_dec(v_a_3096_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg(lean_object* v_fvarId_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3110_ = l_Lean_Expr_fvar___override(v_fvarId_3107_);
v___x_3111_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_3110_, v___y_3108_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg___boxed(lean_object* v_fvarId_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg(v_fvarId_3112_, v___y_3113_);
lean_dec(v___y_3113_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___lam__0(lean_object* v___y_3116_, lean_object* v_k_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v_b_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3128_ = l_Lean_Expr_fvarId_x21(v_b_3122_);
v___x_3129_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg(v___x_3128_, v___y_3116_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v_a_3130_; lean_object* v___x_3131_; 
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
lean_inc(v_a_3130_);
lean_dec_ref_known(v___x_3129_, 1);
lean_inc(v___y_3126_);
lean_inc_ref(v___y_3125_);
lean_inc(v___y_3124_);
lean_inc_ref(v___y_3123_);
lean_inc(v___y_3116_);
lean_inc_ref(v___y_3121_);
lean_inc(v___y_3120_);
lean_inc_ref(v___y_3119_);
lean_inc(v___y_3118_);
v___x_3131_ = lean_apply_11(v_k_3117_, v_a_3130_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3116_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, lean_box(0));
return v___x_3131_;
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec_ref(v_k_3117_);
v_a_3132_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3129_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3129_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v___y_3140_, lean_object* v_k_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v_b_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_){
_start:
{
lean_object* v_res_3152_; 
v_res_3152_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___lam__0(v___y_3140_, v_k_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v_b_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
lean_dec_ref(v_b_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec(v___y_3142_);
lean_dec(v___y_3140_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg(lean_object* v_k_3153_, lean_object* v_name_3154_, uint8_t v_bi_3155_, lean_object* v_type_3156_, uint8_t v_kind_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
lean_object* v___f_3168_; lean_object* v___x_3169_; 
lean_inc_ref(v___y_3161_);
lean_inc(v___y_3160_);
lean_inc_ref(v___y_3159_);
lean_inc(v___y_3158_);
lean_inc(v___y_3162_);
v___f_3168_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_3168_, 0, v___y_3162_);
lean_closure_set(v___f_3168_, 1, v_k_3153_);
lean_closure_set(v___f_3168_, 2, v___y_3158_);
lean_closure_set(v___f_3168_, 3, v___y_3159_);
lean_closure_set(v___f_3168_, 4, v___y_3160_);
lean_closure_set(v___f_3168_, 5, v___y_3161_);
v___x_3169_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3154_, v_bi_3155_, v_type_3156_, v___f_3168_, v_kind_3157_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
if (lean_obj_tag(v___x_3169_) == 0)
{
return v___x_3169_;
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3169_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3169_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3175_; 
if (v_isShared_3173_ == 0)
{
v___x_3175_ = v___x_3172_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___boxed(lean_object* v_k_3178_, lean_object* v_name_3179_, lean_object* v_bi_3180_, lean_object* v_type_3181_, lean_object* v_kind_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
uint8_t v_bi_boxed_3193_; uint8_t v_kind_boxed_3194_; lean_object* v_res_3195_; 
v_bi_boxed_3193_ = lean_unbox(v_bi_3180_);
v_kind_boxed_3194_ = lean_unbox(v_kind_3182_);
v_res_3195_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg(v_k_3178_, v_name_3179_, v_bi_boxed_3193_, v_type_3181_, v_kind_boxed_3194_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg(lean_object* v_name_3196_, uint8_t v_bi_3197_, lean_object* v_type_3198_, lean_object* v_k_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
uint8_t v___x_3210_; lean_object* v___x_3211_; 
v___x_3210_ = 0;
v___x_3211_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg(v_k_3199_, v_name_3196_, v_bi_3197_, v_type_3198_, v___x_3210_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg___boxed(lean_object* v_name_3212_, lean_object* v_bi_3213_, lean_object* v_type_3214_, lean_object* v_k_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
uint8_t v_bi_boxed_3226_; lean_object* v_res_3227_; 
v_bi_boxed_3226_ = lean_unbox(v_bi_3213_);
v_res_3227_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg(v_name_3212_, v_bi_boxed_3226_, v_type_3214_, v_k_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
lean_dec(v___y_3216_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___lam__0___boxed(lean_object* v_xs_3228_, lean_object* v_body_3229_, lean_object* v_x_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___lam__0(v_xs_3228_, v_body_3229_, v_x_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec(v___y_3231_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go(lean_object* v_xs_3242_, lean_object* v_e_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_){
_start:
{
if (lean_obj_tag(v_e_3243_) == 7)
{
lean_object* v_binderName_3254_; lean_object* v_binderType_3255_; lean_object* v_body_3256_; uint8_t v_binderInfo_3257_; uint8_t v___x_3258_; 
v_binderName_3254_ = lean_ctor_get(v_e_3243_, 0);
v_binderType_3255_ = lean_ctor_get(v_e_3243_, 1);
v_body_3256_ = lean_ctor_get(v_e_3243_, 2);
v_binderInfo_3257_ = lean_ctor_get_uint8(v_e_3243_, sizeof(void*)*3 + 8);
v___x_3258_ = l_Lean_Expr_isForall(v_body_3256_);
if (v___x_3258_ == 0)
{
lean_object* v___x_3259_; lean_object* v___x_3260_; uint8_t v___x_3261_; 
v___x_3259_ = lean_array_get_size(v_xs_3242_);
v___x_3260_ = lean_unsigned_to_nat(0u);
v___x_3261_ = lean_nat_dec_eq(v___x_3259_, v___x_3260_);
if (v___x_3261_ == 0)
{
uint8_t v___x_3262_; lean_object* v___x_3263_; 
v___x_3262_ = 1;
lean_inc_ref(v_xs_3242_);
v___x_3263_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_3243_, v___x_3260_, v___x_3259_, v_xs_3242_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v_a_3264_; lean_object* v___x_3265_; 
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc_n(v_a_3264_, 2);
lean_dec_ref_known(v___x_3263_, 1);
v___x_3265_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f(v_a_3264_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3350_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3268_ = v___x_3265_;
v_isShared_3269_ = v_isSharedCheck_3350_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3265_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3350_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
if (lean_obj_tag(v_a_3266_) == 1)
{
lean_object* v_val_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3345_; 
lean_del_object(v___x_3268_);
v_val_3270_ = lean_ctor_get(v_a_3266_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v_a_3266_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3272_ = v_a_3266_;
v_isShared_3273_ = v_isSharedCheck_3345_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_val_3270_);
lean_dec(v_a_3266_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3345_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v_fst_3274_; lean_object* v_snd_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3344_; 
v_fst_3274_ = lean_ctor_get(v_val_3270_, 0);
v_snd_3275_ = lean_ctor_get(v_val_3270_, 1);
v_isSharedCheck_3344_ = !lean_is_exclusive(v_val_3270_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3277_ = v_val_3270_;
v_isShared_3278_ = v_isSharedCheck_3344_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_snd_3275_);
lean_inc(v_fst_3274_);
lean_dec(v_val_3270_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3344_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3279_; 
lean_inc_ref(v_xs_3242_);
v___x_3279_ = l_Lean_Meta_Sym_Simp_mkForallCongrFor(v_xs_3242_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_a_3280_; uint8_t v___x_3281_; lean_object* v___x_3282_; 
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_a_3280_);
lean_dec_ref_known(v___x_3279_, 1);
v___x_3281_ = 1;
v___x_3282_ = l_Lean_Meta_mkLambdaFVars(v_xs_3242_, v_a_3264_, v___x_3261_, v___x_3262_, v___x_3261_, v___x_3262_, v___x_3281_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v_a_3283_; lean_object* v___x_3284_; 
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_a_3283_);
lean_dec_ref_known(v___x_3282_, 1);
lean_inc(v_fst_3274_);
v___x_3284_ = l_Lean_Meta_mkLambdaFVars(v_xs_3242_, v_fst_3274_, v___x_3261_, v___x_3262_, v___x_3261_, v___x_3262_, v___x_3281_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; lean_object* v___x_3286_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3285_);
lean_dec_ref_known(v___x_3284_, 1);
v___x_3286_ = l_Lean_Meta_mkLambdaFVars(v_xs_3242_, v_snd_3275_, v___x_3261_, v___x_3262_, v___x_3261_, v___x_3262_, v___x_3281_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3287_);
lean_dec_ref_known(v___x_3286_, 1);
v___x_3288_ = l_Lean_mkApp3(v_a_3280_, v_a_3283_, v_a_3285_, v_a_3287_);
v___x_3289_ = l_Lean_Meta_Sym_mkForallFVarsS(v_xs_3242_, v_fst_3274_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3303_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3292_ = v___x_3289_;
v_isShared_3293_ = v_isSharedCheck_3303_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3289_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3303_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 1, v___x_3288_);
lean_ctor_set(v___x_3277_, 0, v_a_3290_);
v___x_3295_ = v___x_3277_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3290_);
lean_ctor_set(v_reuseFailAlloc_3302_, 1, v___x_3288_);
v___x_3295_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
lean_object* v___x_3297_; 
if (v_isShared_3273_ == 0)
{
lean_ctor_set(v___x_3272_, 0, v___x_3295_);
v___x_3297_ = v___x_3272_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3295_);
v___x_3297_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
lean_object* v___x_3299_; 
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v___x_3297_);
v___x_3299_ = v___x_3292_;
goto v_reusejp_3298_;
}
else
{
lean_object* v_reuseFailAlloc_3300_; 
v_reuseFailAlloc_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3297_);
v___x_3299_ = v_reuseFailAlloc_3300_;
goto v_reusejp_3298_;
}
v_reusejp_3298_:
{
return v___x_3299_;
}
}
}
}
}
else
{
lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3311_; 
lean_dec_ref(v___x_3288_);
lean_del_object(v___x_3277_);
lean_del_object(v___x_3272_);
v_a_3304_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3306_ = v___x_3289_;
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_dec(v___x_3289_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3309_; 
if (v_isShared_3307_ == 0)
{
v___x_3309_ = v___x_3306_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_a_3304_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
}
else
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3319_; 
lean_dec(v_a_3285_);
lean_dec(v_a_3283_);
lean_dec(v_a_3280_);
lean_del_object(v___x_3277_);
lean_dec(v_fst_3274_);
lean_del_object(v___x_3272_);
lean_dec_ref(v_xs_3242_);
v_a_3312_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3314_ = v___x_3286_;
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3286_);
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
else
{
lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3327_; 
lean_dec(v_a_3283_);
lean_dec(v_a_3280_);
lean_del_object(v___x_3277_);
lean_dec(v_snd_3275_);
lean_dec(v_fst_3274_);
lean_del_object(v___x_3272_);
lean_dec_ref(v_xs_3242_);
v_a_3320_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3327_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3327_ == 0)
{
v___x_3322_ = v___x_3284_;
v_isShared_3323_ = v_isSharedCheck_3327_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3284_);
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
else
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3335_; 
lean_dec(v_a_3280_);
lean_del_object(v___x_3277_);
lean_dec(v_snd_3275_);
lean_dec(v_fst_3274_);
lean_del_object(v___x_3272_);
lean_dec_ref(v_xs_3242_);
v_a_3328_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3335_ == 0)
{
v___x_3330_ = v___x_3282_;
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3282_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3335_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3333_; 
if (v_isShared_3331_ == 0)
{
v___x_3333_ = v___x_3330_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v_a_3328_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
}
else
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3343_; 
lean_del_object(v___x_3277_);
lean_dec(v_snd_3275_);
lean_dec(v_fst_3274_);
lean_del_object(v___x_3272_);
lean_dec(v_a_3264_);
lean_dec_ref(v_xs_3242_);
v_a_3336_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3338_ = v___x_3279_;
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3279_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3343_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v___x_3341_; 
if (v_isShared_3339_ == 0)
{
v___x_3341_ = v___x_3338_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_a_3336_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
}
}
}
else
{
lean_object* v___x_3346_; lean_object* v___x_3348_; 
lean_dec(v_a_3266_);
lean_dec(v_a_3264_);
lean_dec_ref(v_xs_3242_);
v___x_3346_ = lean_box(0);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 0, v___x_3346_);
v___x_3348_ = v___x_3268_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3346_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
else
{
lean_dec(v_a_3264_);
lean_dec_ref(v_xs_3242_);
return v___x_3265_;
}
}
else
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
lean_dec_ref(v_xs_3242_);
v_a_3351_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3263_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3263_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3356_; 
if (v_isShared_3354_ == 0)
{
v___x_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3351_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
else
{
lean_object* v___x_3359_; 
lean_dec_ref(v_xs_3242_);
v___x_3359_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f(v_e_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
return v___x_3359_;
}
}
else
{
lean_object* v___f_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
lean_inc_ref(v_body_3256_);
lean_inc_ref(v_binderType_3255_);
lean_inc(v_binderName_3254_);
lean_dec_ref_known(v_e_3243_, 3);
lean_inc_ref(v_xs_3242_);
v___f_3360_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___lam__0___boxed), 13, 2);
lean_closure_set(v___f_3360_, 0, v_xs_3242_);
lean_closure_set(v___f_3360_, 1, v_body_3256_);
v___x_3361_ = lean_unsigned_to_nat(0u);
v___x_3362_ = lean_array_get_size(v_xs_3242_);
v___x_3363_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_binderType_3255_, v___x_3361_, v___x_3362_, v_xs_3242_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3365_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3364_);
lean_dec_ref_known(v___x_3363_, 1);
v___x_3365_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg(v_binderName_3254_, v_binderInfo_3257_, v_a_3364_, v___f_3360_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
return v___x_3365_;
}
else
{
lean_object* v_a_3366_; lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3373_; 
lean_dec_ref(v___f_3360_);
lean_dec(v_binderName_3254_);
v_a_3366_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3368_ = v___x_3363_;
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
else
{
lean_inc(v_a_3366_);
lean_dec(v___x_3363_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3373_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3371_; 
if (v_isShared_3369_ == 0)
{
v___x_3371_ = v___x_3368_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_a_3366_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
}
else
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
lean_dec_ref(v_e_3243_);
lean_dec_ref(v_xs_3242_);
v___x_3374_ = lean_box(0);
v___x_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3374_);
return v___x_3375_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___lam__0(lean_object* v_xs_3376_, lean_object* v_body_3377_, lean_object* v_x_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3389_ = lean_array_push(v_xs_3376_, v_x_3378_);
v___x_3390_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go(v___x_3389_, v_body_3377_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___boxed(lean_object* v_xs_3391_, lean_object* v_e_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go(v_xs_3391_, v_e_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_);
lean_dec(v_a_3401_);
lean_dec_ref(v_a_3400_);
lean_dec(v_a_3399_);
lean_dec_ref(v_a_3398_);
lean_dec(v_a_3397_);
lean_dec_ref(v_a_3396_);
lean_dec(v_a_3395_);
lean_dec_ref(v_a_3394_);
lean_dec(v_a_3393_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0(lean_object* v_fvarId_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v___x_3412_; 
v___x_3412_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg(v_fvarId_3404_, v___y_3406_);
return v___x_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___boxed(lean_object* v_fvarId_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0(v_fvarId_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2(lean_object* v_00_u03b1_3422_, lean_object* v_k_3423_, lean_object* v_name_3424_, uint8_t v_bi_3425_, lean_object* v_type_3426_, uint8_t v_kind_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v___x_3438_; 
v___x_3438_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg(v_k_3423_, v_name_3424_, v_bi_3425_, v_type_3426_, v_kind_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3439_, lean_object* v_k_3440_, lean_object* v_name_3441_, lean_object* v_bi_3442_, lean_object* v_type_3443_, lean_object* v_kind_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
uint8_t v_bi_boxed_3455_; uint8_t v_kind_boxed_3456_; lean_object* v_res_3457_; 
v_bi_boxed_3455_ = lean_unbox(v_bi_3442_);
v_kind_boxed_3456_ = lean_unbox(v_kind_3444_);
v_res_3457_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2(v_00_u03b1_3439_, v_k_3440_, v_name_3441_, v_bi_boxed_3455_, v_type_3443_, v_kind_boxed_3456_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
lean_dec(v___y_3447_);
lean_dec_ref(v___y_3446_);
lean_dec(v___y_3445_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0(lean_object* v_00_u03b1_3458_, lean_object* v_name_3459_, uint8_t v_bi_3460_, lean_object* v_type_3461_, lean_object* v_k_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_){
_start:
{
lean_object* v___x_3473_; 
v___x_3473_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg(v_name_3459_, v_bi_3460_, v_type_3461_, v_k_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
return v___x_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___boxed(lean_object* v_00_u03b1_3474_, lean_object* v_name_3475_, lean_object* v_bi_3476_, lean_object* v_type_3477_, lean_object* v_k_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
uint8_t v_bi_boxed_3489_; lean_object* v_res_3490_; 
v_bi_boxed_3489_ = lean_unbox(v_bi_3476_);
v_res_3490_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0(v_00_u03b1_3474_, v_name_3475_, v_bi_boxed_3489_, v_type_3477_, v_k_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec(v___y_3485_);
lean_dec_ref(v___y_3484_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f(lean_object* v_e_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; uint8_t v___x_3512_; 
v___x_3510_ = l_Lean_Expr_getForallBody(v_e_3493_);
v___x_3511_ = l_Lean_Expr_cleanupAnnotations(v___x_3510_);
v___x_3512_ = l_Lean_Expr_isApp(v___x_3511_);
if (v___x_3512_ == 0)
{
lean_dec_ref(v___x_3511_);
lean_dec_ref(v_e_3493_);
goto v___jp_3504_;
}
else
{
lean_object* v_arg_3513_; lean_object* v___x_3514_; uint8_t v___x_3515_; 
v_arg_3513_ = lean_ctor_get(v___x_3511_, 1);
lean_inc_ref(v_arg_3513_);
v___x_3514_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3511_);
v___x_3515_ = l_Lean_Expr_isApp(v___x_3514_);
if (v___x_3515_ == 0)
{
lean_dec_ref(v___x_3514_);
lean_dec_ref(v_arg_3513_);
lean_dec_ref(v_e_3493_);
goto v___jp_3504_;
}
else
{
lean_object* v_arg_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; uint8_t v___x_3519_; 
v_arg_3516_ = lean_ctor_get(v___x_3514_, 1);
lean_inc_ref(v_arg_3516_);
v___x_3517_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3514_);
v___x_3518_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1));
v___x_3519_ = l_Lean_Expr_isConstOf(v___x_3517_, v___x_3518_);
lean_dec_ref(v___x_3517_);
if (v___x_3519_ == 0)
{
lean_dec_ref(v_arg_3516_);
lean_dec_ref(v_arg_3513_);
lean_dec_ref(v_e_3493_);
goto v___jp_3504_;
}
else
{
lean_object* v___x_3520_; 
v___x_3520_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(v_arg_3516_);
lean_dec_ref(v_arg_3516_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v___x_3521_; 
v___x_3521_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(v_arg_3513_);
lean_dec_ref(v_arg_3513_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
lean_dec_ref(v_e_3493_);
v___x_3522_ = lean_box(0);
v___x_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3522_);
return v___x_3523_;
}
else
{
lean_dec_ref_known(v___x_3521_, 1);
goto v___jp_3507_;
}
}
else
{
lean_dec_ref_known(v___x_3520_, 1);
lean_dec_ref(v_arg_3513_);
goto v___jp_3507_;
}
}
}
}
v___jp_3504_:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = lean_box(0);
v___x_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3505_);
return v___x_3506_;
}
v___jp_3507_:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3508_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f___closed__0));
v___x_3509_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go(v___x_3508_, v_e_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_);
return v___x_3509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f___boxed(lean_object* v_e_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f(v_e_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_);
lean_dec(v_a_3533_);
lean_dec_ref(v_a_3532_);
lean_dec(v_a_3531_);
lean_dec_ref(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_a_3528_);
lean_dec(v_a_3527_);
lean_dec_ref(v_a_3526_);
lean_dec(v_a_3525_);
return v_res_3535_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__2(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3541_ = lean_box(0);
v___x_3542_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__1));
v___x_3543_ = l_Lean_mkConst(v___x_3542_, v___x_3541_);
return v___x_3543_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__7(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3552_ = lean_box(0);
v___x_3553_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__6));
v___x_3554_ = l_Lean_mkConst(v___x_3553_, v___x_3552_);
return v___x_3554_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__10(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3560_ = lean_box(0);
v___x_3561_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__9));
v___x_3562_ = l_Lean_mkConst(v___x_3561_, v___x_3560_);
return v___x_3562_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__13(void){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3568_ = lean_box(0);
v___x_3569_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__12));
v___x_3570_ = l_Lean_mkConst(v___x_3569_, v___x_3568_);
return v___x_3570_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__18(void){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3580_ = lean_box(0);
v___x_3581_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__17));
v___x_3582_ = l_Lean_mkConst(v___x_3581_, v___x_3580_);
return v___x_3582_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__19(void){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3583_ = lean_unsigned_to_nat(0u);
v___x_3584_ = l_Lean_Level_ofNat(v___x_3583_);
return v___x_3584_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__20(void){
_start:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; 
v___x_3585_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__19, &l_Lean_Meta_Grind_NormSym_simpForall___closed__19_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__19);
v___x_3586_ = l_Lean_mkSort(v___x_3585_);
return v___x_3586_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__23(void){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3590_ = lean_box(0);
v___x_3591_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__22));
v___x_3592_ = l_Lean_mkConst(v___x_3591_, v___x_3590_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpForall(lean_object* v_e_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_){
_start:
{
lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; 
if (lean_obj_tag(v_e_3593_) == 7)
{
lean_object* v_binderName_3698_; lean_object* v_binderType_3699_; lean_object* v_body_3700_; uint8_t v_binderInfo_3701_; uint8_t v___x_3702_; 
v_binderName_3698_ = lean_ctor_get(v_e_3593_, 0);
v_binderType_3699_ = lean_ctor_get(v_e_3593_, 1);
v_body_3700_ = lean_ctor_get(v_e_3593_, 2);
v_binderInfo_3701_ = lean_ctor_get_uint8(v_e_3593_, sizeof(void*)*3 + 8);
v___x_3702_ = l_Lean_Expr_hasLooseBVars(v_body_3700_);
if (v___x_3702_ == 0)
{
uint8_t v___x_3703_; lean_object* v___x_3704_; 
v___x_3703_ = 1;
lean_inc_ref(v_binderType_3699_);
v___x_3704_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3699_, v_a_3600_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_a_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; uint8_t v___x_3708_; 
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3705_);
lean_dec_ref_known(v___x_3704_, 1);
v___x_3706_ = l_Lean_Expr_cleanupAnnotations(v_a_3705_);
v___x_3707_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__6));
v___x_3708_ = l_Lean_Expr_isConstOf(v___x_3706_, v___x_3707_);
if (v___x_3708_ == 0)
{
lean_object* v___x_3709_; uint8_t v___x_3710_; 
v___x_3709_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_3710_ = l_Lean_Expr_isConstOf(v___x_3706_, v___x_3709_);
lean_dec_ref(v___x_3706_);
if (v___x_3710_ == 0)
{
lean_object* v___x_3711_; 
lean_inc_ref(v_body_3700_);
v___x_3711_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_body_3700_, v_a_3600_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; lean_object* v___x_3713_; uint8_t v___x_3714_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_a_3712_);
lean_dec_ref_known(v___x_3711_, 1);
v___x_3713_ = l_Lean_Expr_cleanupAnnotations(v_a_3712_);
v___x_3714_ = l_Lean_Expr_isConstOf(v___x_3713_, v___x_3707_);
if (v___x_3714_ == 0)
{
uint8_t v___x_3715_; 
v___x_3715_ = l_Lean_Expr_isConstOf(v___x_3713_, v___x_3709_);
lean_dec_ref(v___x_3713_);
if (v___x_3715_ == 0)
{
lean_object* v___x_3716_; 
lean_inc_ref(v_binderType_3699_);
v___x_3716_ = l_Lean_Meta_isProp(v_binderType_3699_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v_a_3717_; size_t v___x_3718_; size_t v___x_3719_; uint8_t v___x_3720_; 
v_a_3717_ = lean_ctor_get(v___x_3716_, 0);
lean_inc(v_a_3717_);
lean_dec_ref_known(v___x_3716_, 1);
v___x_3718_ = lean_ptr_addr(v_binderType_3699_);
v___x_3719_ = lean_ptr_addr(v_body_3700_);
v___x_3720_ = lean_usize_dec_eq(v___x_3718_, v___x_3719_);
if (v___x_3720_ == 0)
{
lean_dec(v_a_3717_);
v___y_3605_ = v_a_3594_;
v___y_3606_ = v_a_3595_;
v___y_3607_ = v_a_3596_;
v___y_3608_ = v_a_3597_;
v___y_3609_ = v_a_3598_;
v___y_3610_ = v_a_3599_;
v___y_3611_ = v_a_3600_;
v___y_3612_ = v_a_3601_;
v___y_3613_ = v_a_3602_;
goto v___jp_3604_;
}
else
{
uint8_t v___x_3721_; 
v___x_3721_ = lean_unbox(v_a_3717_);
lean_dec(v_a_3717_);
if (v___x_3721_ == 0)
{
v___y_3605_ = v_a_3594_;
v___y_3606_ = v_a_3595_;
v___y_3607_ = v_a_3596_;
v___y_3608_ = v_a_3597_;
v___y_3609_ = v_a_3598_;
v___y_3610_ = v_a_3599_;
v___y_3611_ = v_a_3600_;
v___y_3612_ = v_a_3601_;
v___y_3613_ = v_a_3602_;
goto v___jp_3604_;
}
else
{
lean_object* v___x_3722_; 
lean_inc_ref(v_binderType_3699_);
lean_dec_ref_known(v_e_3593_, 3);
v___x_3722_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3597_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3733_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3725_ = v___x_3722_;
v_isShared_3726_ = v_isSharedCheck_3733_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3722_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3733_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3731_; 
v___x_3727_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__2, &l_Lean_Meta_Grind_NormSym_simpForall___closed__2_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__2);
v___x_3728_ = l_Lean_Expr_app___override(v___x_3727_, v_binderType_3699_);
v___x_3729_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3729_, 0, v_a_3723_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
lean_ctor_set_uint8(v___x_3729_, sizeof(void*)*2, v___x_3703_);
lean_ctor_set_uint8(v___x_3729_, sizeof(void*)*2 + 1, v___x_3715_);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 0, v___x_3729_);
v___x_3731_ = v___x_3725_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3729_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
lean_dec_ref(v_binderType_3699_);
v_a_3734_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3722_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3722_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
}
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
lean_dec_ref_known(v_e_3593_, 3);
v_a_3742_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3716_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3716_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
else
{
lean_object* v___x_3750_; 
lean_inc_ref(v_binderType_3699_);
lean_dec_ref_known(v_e_3593_, 3);
v___x_3750_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3597_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v_a_3751_; lean_object* v___x_3752_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
lean_inc(v_a_3751_);
lean_dec_ref_known(v___x_3750_, 1);
lean_inc_ref(v_binderType_3699_);
v___x_3752_ = l_Lean_Meta_getLevel(v_binderType_3699_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
if (lean_obj_tag(v___x_3752_) == 0)
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3766_; 
v_a_3753_ = lean_ctor_get(v___x_3752_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3755_ = v___x_3752_;
v_isShared_3756_ = v_isSharedCheck_3766_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3752_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3766_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3764_; 
v___x_3757_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__4));
v___x_3758_ = lean_box(0);
v___x_3759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3759_, 0, v_a_3753_);
lean_ctor_set(v___x_3759_, 1, v___x_3758_);
v___x_3760_ = l_Lean_mkConst(v___x_3757_, v___x_3759_);
v___x_3761_ = l_Lean_Expr_app___override(v___x_3760_, v_binderType_3699_);
v___x_3762_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3762_, 0, v_a_3751_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
lean_ctor_set_uint8(v___x_3762_, sizeof(void*)*2, v___x_3703_);
lean_ctor_set_uint8(v___x_3762_, sizeof(void*)*2 + 1, v___x_3714_);
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 0, v___x_3762_);
v___x_3764_ = v___x_3755_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___x_3762_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_dec(v_a_3751_);
lean_dec_ref(v_binderType_3699_);
v_a_3767_ = lean_ctor_get(v___x_3752_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3752_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3752_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3752_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
lean_dec_ref(v_binderType_3699_);
v_a_3775_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3750_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3750_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
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
}
else
{
lean_object* v___x_3783_; 
lean_dec_ref(v___x_3713_);
lean_inc_ref(v_binderType_3699_);
v___x_3783_ = l_Lean_Meta_isProp(v_binderType_3699_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_a_3784_; uint8_t v___x_3785_; 
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_a_3784_);
lean_dec_ref_known(v___x_3783_, 1);
v___x_3785_ = lean_unbox(v_a_3784_);
lean_dec(v_a_3784_);
if (v___x_3785_ == 0)
{
v___y_3605_ = v_a_3594_;
v___y_3606_ = v_a_3595_;
v___y_3607_ = v_a_3596_;
v___y_3608_ = v_a_3597_;
v___y_3609_ = v_a_3598_;
v___y_3610_ = v_a_3599_;
v___y_3611_ = v_a_3600_;
v___y_3612_ = v_a_3601_;
v___y_3613_ = v_a_3602_;
goto v___jp_3604_;
}
else
{
lean_object* v___x_3786_; 
lean_inc_ref_n(v_binderType_3699_, 2);
lean_dec_ref_known(v_e_3593_, 3);
v___x_3786_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_binderType_3699_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3797_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3789_ = v___x_3786_;
v_isShared_3790_ = v_isSharedCheck_3797_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3786_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3797_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3795_; 
v___x_3791_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__7, &l_Lean_Meta_Grind_NormSym_simpForall___closed__7_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__7);
v___x_3792_ = l_Lean_Expr_app___override(v___x_3791_, v_binderType_3699_);
v___x_3793_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3793_, 0, v_a_3787_);
lean_ctor_set(v___x_3793_, 1, v___x_3792_);
lean_ctor_set_uint8(v___x_3793_, sizeof(void*)*2, v___x_3710_);
lean_ctor_set_uint8(v___x_3793_, sizeof(void*)*2 + 1, v___x_3710_);
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 0, v___x_3793_);
v___x_3795_ = v___x_3789_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v___x_3793_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
else
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
lean_dec_ref(v_binderType_3699_);
v_a_3798_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3786_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3786_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_dec_ref_known(v_e_3593_, 3);
v_a_3806_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3783_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3783_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_dec_ref_known(v_e_3593_, 3);
v_a_3814_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3711_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3711_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
else
{
lean_object* v___x_3822_; 
lean_inc_ref(v_body_3700_);
v___x_3822_ = l_Lean_Meta_isProp(v_body_3700_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3834_; 
v_a_3823_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3825_ = v___x_3822_;
v_isShared_3826_ = v_isSharedCheck_3834_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3822_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3834_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
uint8_t v___x_3827_; 
v___x_3827_ = lean_unbox(v_a_3823_);
lean_dec(v_a_3823_);
if (v___x_3827_ == 0)
{
lean_del_object(v___x_3825_);
v___y_3605_ = v_a_3594_;
v___y_3606_ = v_a_3595_;
v___y_3607_ = v_a_3596_;
v___y_3608_ = v_a_3597_;
v___y_3609_ = v_a_3598_;
v___y_3610_ = v_a_3599_;
v___y_3611_ = v_a_3600_;
v___y_3612_ = v_a_3601_;
v___y_3613_ = v_a_3602_;
goto v___jp_3604_;
}
else
{
lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3832_; 
lean_inc_ref_n(v_body_3700_, 2);
lean_dec_ref_known(v_e_3593_, 3);
v___x_3828_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__10, &l_Lean_Meta_Grind_NormSym_simpForall___closed__10_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__10);
v___x_3829_ = l_Lean_Expr_app___override(v___x_3828_, v_body_3700_);
v___x_3830_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3830_, 0, v_body_3700_);
lean_ctor_set(v___x_3830_, 1, v___x_3829_);
lean_ctor_set_uint8(v___x_3830_, sizeof(void*)*2, v___x_3703_);
lean_ctor_set_uint8(v___x_3830_, sizeof(void*)*2 + 1, v___x_3708_);
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v___x_3830_);
v___x_3832_ = v___x_3825_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v___x_3830_);
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
else
{
lean_object* v_a_3835_; lean_object* v___x_3837_; uint8_t v_isShared_3838_; uint8_t v_isSharedCheck_3842_; 
lean_dec_ref_known(v_e_3593_, 3);
v_a_3835_ = lean_ctor_get(v___x_3822_, 0);
v_isSharedCheck_3842_ = !lean_is_exclusive(v___x_3822_);
if (v_isSharedCheck_3842_ == 0)
{
v___x_3837_ = v___x_3822_;
v_isShared_3838_ = v_isSharedCheck_3842_;
goto v_resetjp_3836_;
}
else
{
lean_inc(v_a_3835_);
lean_dec(v___x_3822_);
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
else
{
lean_object* v___x_3843_; 
lean_dec_ref(v___x_3706_);
lean_inc_ref(v_body_3700_);
v___x_3843_ = l_Lean_Meta_isProp(v_body_3700_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_object* v_a_3844_; uint8_t v___x_3845_; 
v_a_3844_ = lean_ctor_get(v___x_3843_, 0);
lean_inc(v_a_3844_);
lean_dec_ref_known(v___x_3843_, 1);
v___x_3845_ = lean_unbox(v_a_3844_);
lean_dec(v_a_3844_);
if (v___x_3845_ == 0)
{
v___y_3605_ = v_a_3594_;
v___y_3606_ = v_a_3595_;
v___y_3607_ = v_a_3596_;
v___y_3608_ = v_a_3597_;
v___y_3609_ = v_a_3598_;
v___y_3610_ = v_a_3599_;
v___y_3611_ = v_a_3600_;
v___y_3612_ = v_a_3601_;
v___y_3613_ = v_a_3602_;
goto v___jp_3604_;
}
else
{
lean_object* v___x_3846_; 
lean_inc_ref(v_body_3700_);
lean_dec_ref_known(v_e_3593_, 3);
v___x_3846_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3597_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3857_; 
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3849_ = v___x_3846_;
v_isShared_3850_ = v_isSharedCheck_3857_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3846_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3857_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3855_; 
v___x_3851_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__13, &l_Lean_Meta_Grind_NormSym_simpForall___closed__13_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__13);
v___x_3852_ = l_Lean_Expr_app___override(v___x_3851_, v_body_3700_);
v___x_3853_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3853_, 0, v_a_3847_);
lean_ctor_set(v___x_3853_, 1, v___x_3852_);
lean_ctor_set_uint8(v___x_3853_, sizeof(void*)*2, v___x_3703_);
lean_ctor_set_uint8(v___x_3853_, sizeof(void*)*2 + 1, v___x_3702_);
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 0, v___x_3853_);
v___x_3855_ = v___x_3849_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3853_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
else
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3865_; 
lean_dec_ref(v_body_3700_);
v_a_3858_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3860_ = v___x_3846_;
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3846_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3861_ == 0)
{
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
lean_dec_ref_known(v_e_3593_, 3);
v_a_3866_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v___x_3843_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3843_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3866_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
}
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_dec_ref_known(v_e_3593_, 3);
v_a_3874_ = lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3704_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3704_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
else
{
uint8_t v___x_3882_; lean_object* v___x_3883_; 
v___x_3882_ = 0;
lean_inc_ref(v_binderType_3699_);
v___x_3883_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3699_, v_a_3600_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; uint8_t v___x_3887_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3884_);
lean_dec_ref_known(v___x_3883_, 1);
v___x_3885_ = l_Lean_Expr_cleanupAnnotations(v_a_3884_);
v___x_3886_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__6));
v___x_3887_ = l_Lean_Expr_isConstOf(v___x_3885_, v___x_3886_);
if (v___x_3887_ == 0)
{
lean_object* v___x_3888_; uint8_t v___x_3889_; 
v___x_3888_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_3889_ = l_Lean_Expr_isConstOf(v___x_3885_, v___x_3888_);
lean_dec_ref(v___x_3885_);
if (v___x_3889_ == 0)
{
v___y_3605_ = v_a_3594_;
v___y_3606_ = v_a_3595_;
v___y_3607_ = v_a_3596_;
v___y_3608_ = v_a_3597_;
v___y_3609_ = v_a_3598_;
v___y_3610_ = v_a_3599_;
v___y_3611_ = v_a_3600_;
v___y_3612_ = v_a_3601_;
v___y_3613_ = v_a_3602_;
goto v___jp_3604_;
}
else
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3890_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__15));
v___x_3891_ = lean_box(0);
v___x_3892_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v___x_3890_, v___x_3891_, v_a_3598_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3893_);
lean_dec_ref_known(v___x_3892_, 1);
v___x_3894_ = lean_unsigned_to_nat(1u);
v___x_3895_ = lean_mk_empty_array_with_capacity(v___x_3894_);
v___x_3896_ = lean_array_push(v___x_3895_, v_a_3893_);
lean_inc_ref(v_body_3700_);
v___x_3897_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_body_3700_, v___x_3896_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; lean_object* v___x_3899_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc_n(v_a_3898_, 2);
lean_dec_ref_known(v___x_3897_, 1);
v___x_3899_ = l_Lean_Meta_isProp(v_a_3898_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3912_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3902_ = v___x_3899_;
v_isShared_3903_ = v_isSharedCheck_3912_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3899_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3912_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
uint8_t v___x_3904_; 
v___x_3904_ = lean_unbox(v_a_3900_);
lean_dec(v_a_3900_);
if (v___x_3904_ == 0)
{
lean_del_object(v___x_3902_);
lean_dec(v_a_3898_);
v___y_3605_ = v_a_3594_;
v___y_3606_ = v_a_3595_;
v___y_3607_ = v_a_3596_;
v___y_3608_ = v_a_3597_;
v___y_3609_ = v_a_3598_;
v___y_3610_ = v_a_3599_;
v___y_3611_ = v_a_3600_;
v___y_3612_ = v_a_3601_;
v___y_3613_ = v_a_3602_;
goto v___jp_3604_;
}
else
{
lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3910_; 
lean_inc_ref(v_body_3700_);
lean_inc_ref(v_binderType_3699_);
lean_inc(v_binderName_3698_);
lean_dec_ref_known(v_e_3593_, 3);
v___x_3905_ = l_Lean_mkLambda(v_binderName_3698_, v_binderInfo_3701_, v_binderType_3699_, v_body_3700_);
v___x_3906_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__18, &l_Lean_Meta_Grind_NormSym_simpForall___closed__18_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__18);
v___x_3907_ = l_Lean_Expr_app___override(v___x_3906_, v___x_3905_);
v___x_3908_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3908_, 0, v_a_3898_);
lean_ctor_set(v___x_3908_, 1, v___x_3907_);
lean_ctor_set_uint8(v___x_3908_, sizeof(void*)*2, v___x_3702_);
lean_ctor_set_uint8(v___x_3908_, sizeof(void*)*2 + 1, v___x_3882_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 0, v___x_3908_);
v___x_3910_ = v___x_3902_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3908_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
lean_dec(v_a_3898_);
lean_dec_ref_known(v_e_3593_, 3);
v_a_3913_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3899_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3899_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
lean_dec_ref_known(v_e_3593_, 3);
v_a_3921_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___x_3897_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3897_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
else
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3936_; 
lean_dec_ref_known(v_e_3593_, 3);
v_a_3929_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3931_ = v___x_3892_;
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3892_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3932_ == 0)
{
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
}
else
{
lean_object* v___x_3937_; lean_object* v___x_3938_; 
lean_dec_ref(v___x_3885_);
lean_inc_ref(v_body_3700_);
lean_inc_ref(v_binderType_3699_);
lean_inc(v_binderName_3698_);
v___x_3937_ = l_Lean_mkLambda(v_binderName_3698_, v_binderInfo_3701_, v_binderType_3699_, v_body_3700_);
lean_inc(v_a_3602_);
lean_inc_ref(v_a_3601_);
lean_inc(v_a_3600_);
lean_inc_ref(v_a_3599_);
lean_inc_ref(v___x_3937_);
v___x_3938_ = lean_infer_type(v___x_3937_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_object* v_a_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v_a_3939_ = lean_ctor_get(v___x_3938_, 0);
lean_inc(v_a_3939_);
lean_dec_ref_known(v___x_3938_, 1);
v___x_3940_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__20, &l_Lean_Meta_Grind_NormSym_simpForall___closed__20_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__20);
lean_inc_ref(v_binderType_3699_);
lean_inc(v_binderName_3698_);
v___x_3941_ = l_Lean_mkForall(v_binderName_3698_, v_binderInfo_3701_, v_binderType_3699_, v___x_3940_);
v___x_3942_ = l_Lean_Meta_isExprDefEq(v_a_3939_, v___x_3941_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; uint8_t v___x_3944_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_a_3943_);
lean_dec_ref_known(v___x_3942_, 1);
v___x_3944_ = lean_unbox(v_a_3943_);
lean_dec(v_a_3943_);
if (v___x_3944_ == 0)
{
lean_dec_ref(v___x_3937_);
v___y_3605_ = v_a_3594_;
v___y_3606_ = v_a_3595_;
v___y_3607_ = v_a_3596_;
v___y_3608_ = v_a_3597_;
v___y_3609_ = v_a_3598_;
v___y_3610_ = v_a_3599_;
v___y_3611_ = v_a_3600_;
v___y_3612_ = v_a_3601_;
v___y_3613_ = v_a_3602_;
goto v___jp_3604_;
}
else
{
lean_object* v___x_3945_; 
lean_dec_ref_known(v_e_3593_, 3);
v___x_3945_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3597_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3956_; 
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3948_ = v___x_3945_;
v_isShared_3949_ = v_isSharedCheck_3956_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3945_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3956_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3954_; 
v___x_3950_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__23, &l_Lean_Meta_Grind_NormSym_simpForall___closed__23_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__23);
v___x_3951_ = l_Lean_Expr_app___override(v___x_3950_, v___x_3937_);
v___x_3952_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3952_, 0, v_a_3946_);
lean_ctor_set(v___x_3952_, 1, v___x_3951_);
lean_ctor_set_uint8(v___x_3952_, sizeof(void*)*2, v___x_3702_);
lean_ctor_set_uint8(v___x_3952_, sizeof(void*)*2 + 1, v___x_3882_);
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 0, v___x_3952_);
v___x_3954_ = v___x_3948_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v___x_3952_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
lean_dec_ref(v___x_3937_);
v_a_3957_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3945_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3945_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
lean_dec_ref(v___x_3937_);
lean_dec_ref_known(v_e_3593_, 3);
v_a_3965_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3942_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3942_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
}
}
else
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
lean_dec_ref(v___x_3937_);
lean_dec_ref_known(v_e_3593_, 3);
v_a_3973_ = lean_ctor_get(v___x_3938_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3938_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3938_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3938_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
lean_dec_ref_known(v_e_3593_, 3);
v_a_3981_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3883_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3883_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
}
else
{
lean_object* v___x_3989_; lean_object* v___x_3990_; 
lean_dec_ref(v_e_3593_);
v___x_3989_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3989_);
return v___x_3990_;
}
v___jp_3604_:
{
lean_object* v___x_3614_; 
lean_inc_ref(v_e_3593_);
v___x_3614_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f(v_e_3593_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3689_; 
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3617_ = v___x_3614_;
v_isShared_3618_ = v_isSharedCheck_3689_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3614_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3689_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
if (lean_obj_tag(v_a_3615_) == 1)
{
lean_object* v_val_3619_; lean_object* v_fst_3620_; lean_object* v_snd_3621_; uint8_t v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3625_; 
lean_dec_ref(v_e_3593_);
v_val_3619_ = lean_ctor_get(v_a_3615_, 0);
lean_inc(v_val_3619_);
lean_dec_ref_known(v_a_3615_, 1);
v_fst_3620_ = lean_ctor_get(v_val_3619_, 0);
lean_inc(v_fst_3620_);
v_snd_3621_ = lean_ctor_get(v_val_3619_, 1);
lean_inc(v_snd_3621_);
lean_dec(v_val_3619_);
v___x_3622_ = 0;
v___x_3623_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3623_, 0, v_fst_3620_);
lean_ctor_set(v___x_3623_, 1, v_snd_3621_);
lean_ctor_set_uint8(v___x_3623_, sizeof(void*)*2, v___x_3622_);
lean_ctor_set_uint8(v___x_3623_, sizeof(void*)*2 + 1, v___x_3622_);
if (v_isShared_3618_ == 0)
{
lean_ctor_set(v___x_3617_, 0, v___x_3623_);
v___x_3625_ = v___x_3617_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3623_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
else
{
lean_object* v___x_3627_; 
lean_del_object(v___x_3617_);
lean_dec(v_a_3615_);
v___x_3627_ = l_Lean_Meta_Grind_forallImpAnd_x3f(v_e_3593_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3680_; 
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3630_ = v___x_3627_;
v_isShared_3631_ = v_isSharedCheck_3680_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3627_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3680_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
if (lean_obj_tag(v_a_3628_) == 1)
{
lean_object* v_val_3632_; lean_object* v_snd_3633_; lean_object* v_fst_3634_; lean_object* v_fst_3635_; lean_object* v_snd_3636_; lean_object* v___x_3637_; 
lean_del_object(v___x_3630_);
v_val_3632_ = lean_ctor_get(v_a_3628_, 0);
lean_inc(v_val_3632_);
lean_dec_ref_known(v_a_3628_, 1);
v_snd_3633_ = lean_ctor_get(v_val_3632_, 1);
lean_inc(v_snd_3633_);
v_fst_3634_ = lean_ctor_get(v_val_3632_, 0);
lean_inc(v_fst_3634_);
lean_dec(v_val_3632_);
v_fst_3635_ = lean_ctor_get(v_snd_3633_, 0);
lean_inc(v_fst_3635_);
v_snd_3636_ = lean_ctor_get(v_snd_3633_, 1);
lean_inc(v_snd_3636_);
lean_dec(v_snd_3633_);
v___x_3637_ = l_Lean_Meta_Sym_shareCommonInc(v_fst_3634_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; lean_object* v___x_3639_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
lean_dec_ref_known(v___x_3637_, 1);
v___x_3639_ = l_Lean_Meta_Sym_shareCommonInc(v_fst_3635_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3640_; lean_object* v___x_3641_; 
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_a_3640_);
lean_dec_ref_known(v___x_3639_, 1);
v___x_3641_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v_a_3638_, v_a_3640_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3651_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3644_ = v___x_3641_;
v_isShared_3645_ = v_isSharedCheck_3651_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3641_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3651_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
uint8_t v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3649_; 
v___x_3646_ = 0;
v___x_3647_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3647_, 0, v_a_3642_);
lean_ctor_set(v___x_3647_, 1, v_snd_3636_);
lean_ctor_set_uint8(v___x_3647_, sizeof(void*)*2, v___x_3646_);
lean_ctor_set_uint8(v___x_3647_, sizeof(void*)*2 + 1, v___x_3646_);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v___x_3647_);
v___x_3649_ = v___x_3644_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3647_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
else
{
lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3659_; 
lean_dec(v_snd_3636_);
v_a_3652_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3654_ = v___x_3641_;
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v___x_3641_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3657_; 
if (v_isShared_3655_ == 0)
{
v___x_3657_ = v___x_3654_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3652_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
lean_dec(v_a_3638_);
lean_dec(v_snd_3636_);
v_a_3660_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3639_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3639_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
lean_dec(v_snd_3636_);
lean_dec(v_fst_3635_);
v_a_3668_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3637_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3637_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3668_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
else
{
lean_object* v___x_3676_; lean_object* v___x_3678_; 
lean_dec(v_a_3628_);
v___x_3676_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 0, v___x_3676_);
v___x_3678_ = v___x_3630_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3676_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
v_a_3681_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3627_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3627_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
}
}
else
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
lean_dec_ref(v_e_3593_);
v_a_3690_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3614_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3614_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpForall___boxed(lean_object* v_e_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l_Lean_Meta_Grind_NormSym_simpForall(v_e_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_);
lean_dec(v_a_4000_);
lean_dec_ref(v_a_3999_);
lean_dec(v_a_3998_);
lean_dec_ref(v_a_3997_);
lean_dec(v_a_3996_);
lean_dec_ref(v_a_3995_);
lean_dec(v_a_3994_);
lean_dec_ref(v_a_3993_);
lean_dec(v_a_3992_);
return v_res_4002_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpExists___closed__6(void){
_start:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4016_ = lean_box(0);
v___x_4017_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___closed__5));
v___x_4018_ = l_Lean_mkConst(v___x_4017_, v___x_4016_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists(lean_object* v_e_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_){
_start:
{
lean_object* v___x_4051_; uint8_t v___x_4052_; 
v___x_4051_ = l_Lean_Expr_cleanupAnnotations(v_e_4034_);
v___x_4052_ = l_Lean_Expr_isApp(v___x_4051_);
if (v___x_4052_ == 0)
{
lean_dec_ref(v___x_4051_);
goto v___jp_4048_;
}
else
{
lean_object* v_arg_4053_; lean_object* v___x_4054_; uint8_t v___x_4055_; 
v_arg_4053_ = lean_ctor_get(v___x_4051_, 1);
lean_inc_ref(v_arg_4053_);
v___x_4054_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4051_);
v___x_4055_ = l_Lean_Expr_isApp(v___x_4054_);
if (v___x_4055_ == 0)
{
lean_dec_ref(v___x_4054_);
lean_dec_ref(v_arg_4053_);
goto v___jp_4048_;
}
else
{
lean_object* v_arg_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; uint8_t v___x_4059_; 
v_arg_4056_ = lean_ctor_get(v___x_4054_, 1);
lean_inc_ref(v_arg_4056_);
v___x_4057_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4054_);
v___x_4058_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg___closed__1));
v___x_4059_ = l_Lean_Expr_isConstOf(v___x_4057_, v___x_4058_);
if (v___x_4059_ == 0)
{
lean_dec_ref(v___x_4057_);
lean_dec_ref(v_arg_4056_);
lean_dec_ref(v_arg_4053_);
goto v___jp_4048_;
}
else
{
if (lean_obj_tag(v_arg_4053_) == 6)
{
lean_object* v_binderName_4060_; lean_object* v_body_4061_; lean_object* v_u_4062_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; uint8_t v___x_4150_; 
v_binderName_4060_ = lean_ctor_get(v_arg_4053_, 0);
lean_inc(v_binderName_4060_);
v_body_4061_ = lean_ctor_get(v_arg_4053_, 2);
lean_inc_ref(v_body_4061_);
lean_dec_ref_known(v_arg_4053_, 3);
v_u_4062_ = l_Lean_Expr_constLevels_x21(v___x_4057_);
v___x_4150_ = l_Lean_Expr_isApp(v_body_4061_);
if (v___x_4150_ == 0)
{
lean_dec(v_binderName_4060_);
lean_dec_ref(v___x_4057_);
v___y_4064_ = v_a_4035_;
v___y_4065_ = v_a_4036_;
v___y_4066_ = v_a_4037_;
v___y_4067_ = v_a_4038_;
v___y_4068_ = v_a_4039_;
v___y_4069_ = v_a_4040_;
v___y_4070_ = v_a_4041_;
v___y_4071_ = v_a_4042_;
v___y_4072_ = v_a_4043_;
goto v___jp_4063_;
}
else
{
lean_object* v___x_4151_; lean_object* v___x_4152_; uint8_t v___x_4153_; 
v___x_4151_ = l_Lean_Expr_getAppNumArgs(v_body_4061_);
v___x_4152_ = lean_unsigned_to_nat(2u);
v___x_4153_ = lean_nat_dec_eq(v___x_4151_, v___x_4152_);
lean_dec(v___x_4151_);
if (v___x_4153_ == 0)
{
lean_dec(v_binderName_4060_);
lean_dec_ref(v___x_4057_);
v___y_4064_ = v_a_4035_;
v___y_4065_ = v_a_4036_;
v___y_4066_ = v_a_4037_;
v___y_4067_ = v_a_4038_;
v___y_4068_ = v_a_4039_;
v___y_4069_ = v_a_4040_;
v___y_4070_ = v_a_4041_;
v___y_4071_ = v_a_4042_;
v___y_4072_ = v_a_4043_;
goto v___jp_4063_;
}
else
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4154_ = l_Lean_Expr_appFn_x21(v_body_4061_);
v___x_4155_ = l_Lean_Expr_appFn_x21(v___x_4154_);
if (lean_obj_tag(v___x_4155_) == 4)
{
lean_object* v_declName_4156_; lean_object* v___x_4157_; uint8_t v___x_4158_; 
v_declName_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_declName_4156_);
lean_dec_ref_known(v___x_4155_, 2);
v___x_4157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1));
v___x_4158_ = lean_name_eq(v_declName_4156_, v___x_4157_);
if (v___x_4158_ == 0)
{
lean_object* v___x_4159_; uint8_t v___x_4160_; 
v___x_4159_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS___closed__1));
v___x_4160_ = lean_name_eq(v_declName_4156_, v___x_4159_);
lean_dec(v_declName_4156_);
if (v___x_4160_ == 0)
{
lean_dec_ref(v___x_4154_);
lean_dec(v_binderName_4060_);
lean_dec_ref(v___x_4057_);
v___y_4064_ = v_a_4035_;
v___y_4065_ = v_a_4036_;
v___y_4066_ = v_a_4037_;
v___y_4067_ = v_a_4038_;
v___y_4068_ = v_a_4039_;
v___y_4069_ = v_a_4040_;
v___y_4070_ = v_a_4041_;
v___y_4071_ = v_a_4042_;
v___y_4072_ = v_a_4043_;
goto v___jp_4063_;
}
else
{
lean_object* v_b_4161_; lean_object* v_b_4162_; uint8_t v___x_4163_; 
v_b_4161_ = l_Lean_Expr_appArg_x21(v___x_4154_);
lean_dec_ref(v___x_4154_);
v_b_4162_ = l_Lean_Expr_appArg_x21(v_body_4061_);
v___x_4163_ = l_Lean_Expr_hasLooseBVars(v_b_4161_);
if (v___x_4163_ == 0)
{
uint8_t v___x_4164_; lean_object* v___x_4165_; 
lean_dec_ref(v_body_4061_);
v___x_4164_ = 0;
lean_inc_ref(v_arg_4056_);
v___x_4165_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_binderName_4060_, v___x_4164_, v_arg_4056_, v_b_4162_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; lean_object* v___x_4167_; 
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
lean_inc_n(v_a_4166_, 2);
lean_dec_ref_known(v___x_4165_, 1);
lean_inc_ref(v_arg_4056_);
v___x_4167_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v___x_4057_, v_arg_4056_, v_a_4166_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_object* v_a_4168_; lean_object* v___x_4169_; 
v_a_4168_ = lean_ctor_get(v___x_4167_, 0);
lean_inc(v_a_4168_);
lean_dec_ref_known(v___x_4167_, 1);
lean_inc_ref(v_b_4161_);
v___x_4169_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v_b_4161_, v_a_4168_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4181_; 
v_a_4170_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4181_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_4172_ = v___x_4169_;
v_isShared_4173_ = v_isSharedCheck_4181_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___x_4169_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4181_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4179_; 
v___x_4174_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___closed__8));
v___x_4175_ = l_Lean_mkConst(v___x_4174_, v_u_4062_);
v___x_4176_ = l_Lean_mkApp3(v___x_4175_, v_arg_4056_, v_a_4166_, v_b_4161_);
v___x_4177_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_4177_, 0, v_a_4170_);
lean_ctor_set(v___x_4177_, 1, v___x_4176_);
lean_ctor_set_uint8(v___x_4177_, sizeof(void*)*2, v___x_4158_);
lean_ctor_set_uint8(v___x_4177_, sizeof(void*)*2 + 1, v___x_4158_);
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
else
{
lean_object* v_a_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4189_; 
lean_dec(v_a_4166_);
lean_dec_ref(v_b_4161_);
lean_dec(v_u_4062_);
lean_dec_ref(v_arg_4056_);
v_a_4182_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4184_ = v___x_4169_;
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_a_4182_);
lean_dec(v___x_4169_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v___x_4187_; 
if (v_isShared_4185_ == 0)
{
v___x_4187_ = v___x_4184_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_a_4182_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
return v___x_4187_;
}
}
}
}
else
{
lean_object* v_a_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4197_; 
lean_dec(v_a_4166_);
lean_dec_ref(v_b_4161_);
lean_dec(v_u_4062_);
lean_dec_ref(v_arg_4056_);
v_a_4190_ = lean_ctor_get(v___x_4167_, 0);
v_isSharedCheck_4197_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4192_ = v___x_4167_;
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_a_4190_);
lean_dec(v___x_4167_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4195_; 
if (v_isShared_4193_ == 0)
{
v___x_4195_ = v___x_4192_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4190_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
return v___x_4195_;
}
}
}
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
lean_dec_ref(v_b_4161_);
lean_dec(v_u_4062_);
lean_dec_ref(v___x_4057_);
lean_dec_ref(v_arg_4056_);
v_a_4198_ = lean_ctor_get(v___x_4165_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___x_4165_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4165_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
}
else
{
uint8_t v___x_4206_; 
v___x_4206_ = l_Lean_Expr_hasLooseBVars(v_b_4162_);
if (v___x_4206_ == 0)
{
uint8_t v___x_4207_; lean_object* v___x_4208_; 
lean_dec_ref(v_body_4061_);
v___x_4207_ = 0;
lean_inc_ref(v_arg_4056_);
v___x_4208_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_binderName_4060_, v___x_4207_, v_arg_4056_, v_b_4161_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4209_; lean_object* v___x_4210_; 
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
lean_inc_n(v_a_4209_, 2);
lean_dec_ref_known(v___x_4208_, 1);
lean_inc_ref(v_arg_4056_);
v___x_4210_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v___x_4057_, v_arg_4056_, v_a_4209_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_object* v_a_4211_; lean_object* v___x_4212_; 
v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
lean_inc(v_a_4211_);
lean_dec_ref_known(v___x_4210_, 1);
lean_inc_ref(v_b_4162_);
v___x_4212_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v_a_4211_, v_b_4162_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4224_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4215_ = v___x_4212_;
v_isShared_4216_ = v_isSharedCheck_4224_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4212_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4224_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4222_; 
v___x_4217_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___closed__10));
v___x_4218_ = l_Lean_mkConst(v___x_4217_, v_u_4062_);
v___x_4219_ = l_Lean_mkApp3(v___x_4218_, v_arg_4056_, v_a_4209_, v_b_4162_);
v___x_4220_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_4220_, 0, v_a_4213_);
lean_ctor_set(v___x_4220_, 1, v___x_4219_);
lean_ctor_set_uint8(v___x_4220_, sizeof(void*)*2, v___x_4158_);
lean_ctor_set_uint8(v___x_4220_, sizeof(void*)*2 + 1, v___x_4158_);
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 0, v___x_4220_);
v___x_4222_ = v___x_4215_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v___x_4220_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
else
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4232_; 
lean_dec(v_a_4209_);
lean_dec_ref(v_b_4162_);
lean_dec(v_u_4062_);
lean_dec_ref(v_arg_4056_);
v_a_4225_ = lean_ctor_get(v___x_4212_, 0);
v_isSharedCheck_4232_ = !lean_is_exclusive(v___x_4212_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4227_ = v___x_4212_;
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4212_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4230_; 
if (v_isShared_4228_ == 0)
{
v___x_4230_ = v___x_4227_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_a_4225_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
}
else
{
lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4240_; 
lean_dec(v_a_4209_);
lean_dec_ref(v_b_4162_);
lean_dec(v_u_4062_);
lean_dec_ref(v_arg_4056_);
v_a_4233_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4235_ = v___x_4210_;
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_dec(v___x_4210_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4238_; 
if (v_isShared_4236_ == 0)
{
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_a_4233_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
}
else
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4248_; 
lean_dec_ref(v_b_4162_);
lean_dec(v_u_4062_);
lean_dec_ref(v___x_4057_);
lean_dec_ref(v_arg_4056_);
v_a_4241_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4243_ = v___x_4208_;
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4208_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4241_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
}
else
{
lean_dec_ref(v_b_4162_);
lean_dec_ref(v_b_4161_);
lean_dec(v_binderName_4060_);
lean_dec_ref(v___x_4057_);
v___y_4064_ = v_a_4035_;
v___y_4065_ = v_a_4036_;
v___y_4066_ = v_a_4037_;
v___y_4067_ = v_a_4038_;
v___y_4068_ = v_a_4039_;
v___y_4069_ = v_a_4040_;
v___y_4070_ = v_a_4041_;
v___y_4071_ = v_a_4042_;
v___y_4072_ = v_a_4043_;
goto v___jp_4063_;
}
}
}
}
else
{
lean_object* v_pRaw_4249_; lean_object* v_qRaw_4250_; uint8_t v___x_4251_; lean_object* v___x_4252_; 
lean_dec(v_declName_4156_);
v_pRaw_4249_ = l_Lean_Expr_appArg_x21(v___x_4154_);
lean_dec_ref(v___x_4154_);
v_qRaw_4250_ = l_Lean_Expr_appArg_x21(v_body_4061_);
lean_dec_ref(v_body_4061_);
v___x_4251_ = 0;
lean_inc_ref(v_arg_4056_);
lean_inc(v_binderName_4060_);
v___x_4252_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_binderName_4060_, v___x_4251_, v_arg_4056_, v_pRaw_4249_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_object* v_a_4253_; lean_object* v___x_4254_; 
v_a_4253_ = lean_ctor_get(v___x_4252_, 0);
lean_inc(v_a_4253_);
lean_dec_ref_known(v___x_4252_, 1);
lean_inc_ref(v_arg_4056_);
v___x_4254_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_binderName_4060_, v___x_4251_, v_arg_4056_, v_qRaw_4250_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
if (lean_obj_tag(v___x_4254_) == 0)
{
lean_object* v_a_4255_; lean_object* v___x_4256_; 
v_a_4255_ = lean_ctor_get(v___x_4254_, 0);
lean_inc(v_a_4255_);
lean_dec_ref_known(v___x_4254_, 1);
lean_inc(v_a_4253_);
lean_inc_ref(v_arg_4056_);
lean_inc_ref(v___x_4057_);
v___x_4256_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v___x_4057_, v_arg_4056_, v_a_4253_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
if (lean_obj_tag(v___x_4256_) == 0)
{
lean_object* v_a_4257_; lean_object* v___x_4258_; 
v_a_4257_ = lean_ctor_get(v___x_4256_, 0);
lean_inc(v_a_4257_);
lean_dec_ref_known(v___x_4256_, 1);
lean_inc(v_a_4255_);
lean_inc_ref(v_arg_4056_);
v___x_4258_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v___x_4057_, v_arg_4056_, v_a_4255_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
if (lean_obj_tag(v___x_4258_) == 0)
{
lean_object* v_a_4259_; lean_object* v___x_4260_; 
v_a_4259_ = lean_ctor_get(v___x_4258_, 0);
lean_inc(v_a_4259_);
lean_dec_ref_known(v___x_4258_, 1);
v___x_4260_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_a_4257_, v_a_4259_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_);
if (lean_obj_tag(v___x_4260_) == 0)
{
lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4273_; 
v_a_4261_ = lean_ctor_get(v___x_4260_, 0);
v_isSharedCheck_4273_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4263_ = v___x_4260_;
v_isShared_4264_ = v_isSharedCheck_4273_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v___x_4260_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4273_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; uint8_t v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4271_; 
v___x_4265_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___closed__12));
v___x_4266_ = l_Lean_mkConst(v___x_4265_, v_u_4062_);
v___x_4267_ = l_Lean_mkApp3(v___x_4266_, v_arg_4056_, v_a_4253_, v_a_4255_);
v___x_4268_ = 0;
v___x_4269_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_4269_, 0, v_a_4261_);
lean_ctor_set(v___x_4269_, 1, v___x_4267_);
lean_ctor_set_uint8(v___x_4269_, sizeof(void*)*2, v___x_4268_);
lean_ctor_set_uint8(v___x_4269_, sizeof(void*)*2 + 1, v___x_4268_);
if (v_isShared_4264_ == 0)
{
lean_ctor_set(v___x_4263_, 0, v___x_4269_);
v___x_4271_ = v___x_4263_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v___x_4269_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
return v___x_4271_;
}
}
}
else
{
lean_object* v_a_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4281_; 
lean_dec(v_a_4255_);
lean_dec(v_a_4253_);
lean_dec(v_u_4062_);
lean_dec_ref(v_arg_4056_);
v_a_4274_ = lean_ctor_get(v___x_4260_, 0);
v_isSharedCheck_4281_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4281_ == 0)
{
v___x_4276_ = v___x_4260_;
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_a_4274_);
lean_dec(v___x_4260_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v___x_4279_; 
if (v_isShared_4277_ == 0)
{
v___x_4279_ = v___x_4276_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_a_4274_);
v___x_4279_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
return v___x_4279_;
}
}
}
}
else
{
lean_object* v_a_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4289_; 
lean_dec(v_a_4257_);
lean_dec(v_a_4255_);
lean_dec(v_a_4253_);
lean_dec(v_u_4062_);
lean_dec_ref(v_arg_4056_);
v_a_4282_ = lean_ctor_get(v___x_4258_, 0);
v_isSharedCheck_4289_ = !lean_is_exclusive(v___x_4258_);
if (v_isSharedCheck_4289_ == 0)
{
v___x_4284_ = v___x_4258_;
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_a_4282_);
lean_dec(v___x_4258_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___x_4287_; 
if (v_isShared_4285_ == 0)
{
v___x_4287_ = v___x_4284_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v_a_4282_);
v___x_4287_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
return v___x_4287_;
}
}
}
}
else
{
lean_object* v_a_4290_; lean_object* v___x_4292_; uint8_t v_isShared_4293_; uint8_t v_isSharedCheck_4297_; 
lean_dec(v_a_4255_);
lean_dec(v_a_4253_);
lean_dec(v_u_4062_);
lean_dec_ref(v___x_4057_);
lean_dec_ref(v_arg_4056_);
v_a_4290_ = lean_ctor_get(v___x_4256_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_4256_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4292_ = v___x_4256_;
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
else
{
lean_inc(v_a_4290_);
lean_dec(v___x_4256_);
v___x_4292_ = lean_box(0);
v_isShared_4293_ = v_isSharedCheck_4297_;
goto v_resetjp_4291_;
}
v_resetjp_4291_:
{
lean_object* v___x_4295_; 
if (v_isShared_4293_ == 0)
{
v___x_4295_ = v___x_4292_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_a_4290_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
return v___x_4295_;
}
}
}
}
else
{
lean_object* v_a_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4305_; 
lean_dec(v_a_4253_);
lean_dec(v_u_4062_);
lean_dec_ref(v___x_4057_);
lean_dec_ref(v_arg_4056_);
v_a_4298_ = lean_ctor_get(v___x_4254_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4254_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4300_ = v___x_4254_;
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_a_4298_);
lean_dec(v___x_4254_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4303_; 
if (v_isShared_4301_ == 0)
{
v___x_4303_ = v___x_4300_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_a_4298_);
v___x_4303_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
return v___x_4303_;
}
}
}
}
else
{
lean_object* v_a_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
lean_dec_ref(v_qRaw_4250_);
lean_dec(v_u_4062_);
lean_dec(v_binderName_4060_);
lean_dec_ref(v___x_4057_);
lean_dec_ref(v_arg_4056_);
v_a_4306_ = lean_ctor_get(v___x_4252_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4308_ = v___x_4252_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_a_4306_);
lean_dec(v___x_4252_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4306_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
}
}
else
{
lean_object* v___x_4314_; lean_object* v___x_4315_; 
lean_dec_ref(v___x_4155_);
lean_dec_ref(v___x_4154_);
lean_dec(v_u_4062_);
lean_dec_ref(v_body_4061_);
lean_dec(v_binderName_4060_);
lean_dec_ref(v___x_4057_);
lean_dec_ref(v_arg_4056_);
v___x_4314_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_4315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4315_, 0, v___x_4314_);
return v___x_4315_;
}
}
}
v___jp_4063_:
{
uint8_t v___x_4073_; 
v___x_4073_ = l_Lean_Expr_hasLooseBVars(v_body_4061_);
if (v___x_4073_ == 0)
{
lean_object* v___x_4074_; 
lean_inc_ref(v_arg_4056_);
v___x_4074_ = l_Lean_Meta_isProp(v_arg_4056_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v_a_4075_; uint8_t v___x_4076_; 
v_a_4075_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_a_4075_);
lean_dec_ref_known(v___x_4074_, 1);
v___x_4076_ = lean_unbox(v_a_4075_);
if (v___x_4076_ == 0)
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___closed__1));
lean_inc(v_u_4062_);
v___x_4078_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v___x_4077_, v_u_4062_, v___y_4068_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_object* v_a_4079_; lean_object* v___x_4080_; 
v_a_4079_ = lean_ctor_get(v___x_4078_, 0);
lean_inc(v_a_4079_);
lean_dec_ref_known(v___x_4078_, 1);
lean_inc_ref(v_arg_4056_);
v___x_4080_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_a_4079_, v_arg_4056_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v_a_4081_; lean_object* v___x_4082_; 
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc(v_a_4081_);
lean_dec_ref_known(v___x_4080_, 1);
v___x_4082_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_4081_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4097_; 
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4085_ = v___x_4082_;
v_isShared_4086_ = v_isSharedCheck_4097_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4082_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4097_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
if (lean_obj_tag(v_a_4083_) == 1)
{
lean_object* v_val_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; uint8_t v___x_4092_; uint8_t v___x_4093_; lean_object* v___x_4095_; 
v_val_4087_ = lean_ctor_get(v_a_4083_, 0);
lean_inc(v_val_4087_);
lean_dec_ref_known(v_a_4083_, 1);
v___x_4088_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___closed__3));
v___x_4089_ = l_Lean_mkConst(v___x_4088_, v_u_4062_);
lean_inc_ref(v_body_4061_);
v___x_4090_ = l_Lean_mkApp3(v___x_4089_, v_arg_4056_, v_val_4087_, v_body_4061_);
v___x_4091_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_4091_, 0, v_body_4061_);
lean_ctor_set(v___x_4091_, 1, v___x_4090_);
v___x_4092_ = lean_unbox(v_a_4075_);
lean_ctor_set_uint8(v___x_4091_, sizeof(void*)*2, v___x_4092_);
v___x_4093_ = lean_unbox(v_a_4075_);
lean_dec(v_a_4075_);
lean_ctor_set_uint8(v___x_4091_, sizeof(void*)*2 + 1, v___x_4093_);
if (v_isShared_4086_ == 0)
{
lean_ctor_set(v___x_4085_, 0, v___x_4091_);
v___x_4095_ = v___x_4085_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4091_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
else
{
lean_del_object(v___x_4085_);
lean_dec(v_a_4083_);
lean_dec(v_a_4075_);
lean_dec(v_u_4062_);
lean_dec_ref(v_body_4061_);
lean_dec_ref(v_arg_4056_);
goto v___jp_4045_;
}
}
}
else
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4105_; 
lean_dec(v_a_4075_);
lean_dec(v_u_4062_);
lean_dec_ref(v_body_4061_);
lean_dec_ref(v_arg_4056_);
v_a_4098_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4100_ = v___x_4082_;
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4082_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4103_; 
if (v_isShared_4101_ == 0)
{
v___x_4103_ = v___x_4100_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
else
{
lean_object* v_a_4106_; lean_object* v___x_4108_; uint8_t v_isShared_4109_; uint8_t v_isSharedCheck_4113_; 
lean_dec(v_a_4075_);
lean_dec(v_u_4062_);
lean_dec_ref(v_body_4061_);
lean_dec_ref(v_arg_4056_);
v_a_4106_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4113_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4108_ = v___x_4080_;
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
else
{
lean_inc(v_a_4106_);
lean_dec(v___x_4080_);
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
else
{
lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4121_; 
lean_dec(v_a_4075_);
lean_dec(v_u_4062_);
lean_dec_ref(v_body_4061_);
lean_dec_ref(v_arg_4056_);
v_a_4114_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4116_ = v___x_4078_;
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v___x_4078_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4119_; 
if (v_isShared_4117_ == 0)
{
v___x_4119_ = v___x_4116_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_a_4114_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
}
else
{
lean_object* v___x_4122_; 
lean_dec(v_a_4075_);
lean_dec(v_u_4062_);
lean_inc_ref(v_body_4061_);
lean_inc_ref(v_arg_4056_);
v___x_4122_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v_arg_4056_, v_body_4061_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4133_; 
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4125_ = v___x_4122_;
v_isShared_4126_ = v_isSharedCheck_4133_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4122_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4133_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4131_; 
v___x_4127_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpExists___closed__6, &l_Lean_Meta_Grind_NormSym_simpExists___closed__6_once, _init_l_Lean_Meta_Grind_NormSym_simpExists___closed__6);
v___x_4128_ = l_Lean_mkAppB(v___x_4127_, v_arg_4056_, v_body_4061_);
v___x_4129_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_4129_, 0, v_a_4123_);
lean_ctor_set(v___x_4129_, 1, v___x_4128_);
lean_ctor_set_uint8(v___x_4129_, sizeof(void*)*2, v___x_4073_);
lean_ctor_set_uint8(v___x_4129_, sizeof(void*)*2 + 1, v___x_4073_);
if (v_isShared_4126_ == 0)
{
lean_ctor_set(v___x_4125_, 0, v___x_4129_);
v___x_4131_ = v___x_4125_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4129_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
else
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
lean_dec_ref(v_body_4061_);
lean_dec_ref(v_arg_4056_);
v_a_4134_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4136_ = v___x_4122_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___x_4122_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4139_; 
if (v_isShared_4137_ == 0)
{
v___x_4139_ = v___x_4136_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
}
else
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4149_; 
lean_dec(v_u_4062_);
lean_dec_ref(v_body_4061_);
lean_dec_ref(v_arg_4056_);
v_a_4142_ = lean_ctor_get(v___x_4074_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4074_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4144_ = v___x_4074_;
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___x_4074_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4147_; 
if (v_isShared_4145_ == 0)
{
v___x_4147_ = v___x_4144_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
}
else
{
lean_dec(v_u_4062_);
lean_dec_ref(v_body_4061_);
lean_dec_ref(v_arg_4056_);
goto v___jp_4045_;
}
}
}
else
{
lean_object* v___x_4316_; lean_object* v___x_4317_; 
lean_dec_ref(v___x_4057_);
lean_dec_ref(v_arg_4056_);
lean_dec_ref(v_arg_4053_);
v___x_4316_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_4317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4317_, 0, v___x_4316_);
return v___x_4317_;
}
}
}
}
v___jp_4045_:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4046_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
return v___x_4047_;
}
v___jp_4048_:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4049_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_4050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4049_);
return v___x_4050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists___boxed(lean_object* v_e_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l_Lean_Meta_Grind_NormSym_simpExists(v_e_4318_, v_a_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_);
lean_dec(v_a_4327_);
lean_dec_ref(v_a_4326_);
lean_dec(v_a_4325_);
lean_dec_ref(v_a_4324_);
lean_dec(v_a_4323_);
lean_dec_ref(v_a_4322_);
lean_dec(v_a_4321_);
lean_dec_ref(v_a_4320_);
lean_dec(v_a_4319_);
return v_res_4329_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Eta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ForallAnd(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Norm(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_NormSymProcs(uint8_t builtin) {
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
res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Eta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ForallAnd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CtorRecognizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_NormSymProcs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AbstractS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Eta(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_ForallAnd(uint8_t builtin);
lean_object* initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
lean_object* initialize_Init_Grind_Norm(uint8_t builtin);
lean_object* initialize_Init_Grind_Util(uint8_t builtin);
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_NormSymProcs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_AbstractS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Eta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ForallAnd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CtorRecognizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_NormSymProcs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_NormSymProcs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_NormSymProcs(builtin);
}
#ifdef __cplusplus
}
#endif

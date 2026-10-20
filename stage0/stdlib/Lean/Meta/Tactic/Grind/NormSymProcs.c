// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.NormSymProcs
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.Simp.Result import Lean.Meta.Sym.Simp.App import Lean.Meta.Sym.Simp.Forall import Lean.Meta.Match.MatcherInfo import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.AbstractS import Lean.Meta.Sym.Util import Lean.Meta.Sym.InferType import Lean.Meta.Sym.SynthInstance import Lean.Meta.AppBuilder import Lean.Meta.Tactic.Grind.ForallAnd import Lean.Meta.CtorRecognizer import Init.Grind.Norm import Init.Grind.Util import Init.Grind.Lemmas import Init.ByCases
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(lean_object* v_e_406_){
_start:
{
lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_411_ = l_Lean_Expr_cleanupAnnotations(v_e_406_);
v___x_412_ = l_Lean_Expr_isApp(v___x_411_);
if (v___x_412_ == 0)
{
lean_dec_ref(v___x_411_);
goto v___jp_408_;
}
else
{
lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_413_ = l_Lean_Expr_appFnCleanup___redArg(v___x_411_);
v___x_414_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__3));
v___x_415_ = l_Lean_Expr_isConstOf(v___x_413_, v___x_414_);
lean_dec_ref(v___x_413_);
if (v___x_415_ == 0)
{
goto v___jp_408_;
}
else
{
uint8_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = 0;
v___x_417_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_415_, v___x_416_);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
}
v___jp_408_:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___boxed(lean_object* v_e_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(v_e_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond(lean_object* v_e_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(v_e_422_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___boxed(lean_object* v_e_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Meta_Grind_NormSym_preMatchCond(v_e_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(lean_object* v_declName_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; lean_object* v_env_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_449_ = lean_st_ref_get(v___y_447_);
v_env_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc_ref(v_env_450_);
lean_dec(v___x_449_);
v___x_451_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_450_, v_declName_446_);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg___boxed(lean_object* v_declName_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(v_declName_453_, v___y_454_);
lean_dec(v___y_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0(lean_object* v_declName_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(v_declName_457_, v___y_466_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___boxed(lean_object* v_declName_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0(v_declName_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
lean_dec(v___y_470_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(lean_object* v_e_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
if (lean_obj_tag(v_e_486_) == 5)
{
lean_object* v_fn_500_; lean_object* v_arg_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v_fn_500_ = lean_ctor_get(v_e_486_, 0);
lean_inc_ref(v_fn_500_);
v_arg_501_ = lean_ctor_get(v_e_486_, 1);
lean_inc_ref(v_arg_501_);
lean_inc_ref(v_e_486_);
v___x_502_ = l_Lean_Expr_cleanupAnnotations(v_e_486_);
v___x_503_ = l_Lean_Expr_isApp(v___x_502_);
if (v___x_503_ == 0)
{
lean_dec_ref(v___x_502_);
lean_dec_ref(v_arg_501_);
lean_dec_ref(v_fn_500_);
lean_dec_ref_known(v_e_486_, 2);
goto v___jp_497_;
}
else
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = l_Lean_Expr_appFnCleanup___redArg(v___x_502_);
v___x_505_ = l_Lean_Expr_isApp(v___x_504_);
if (v___x_505_ == 0)
{
lean_dec_ref(v___x_504_);
lean_dec_ref(v_arg_501_);
lean_dec_ref(v_fn_500_);
lean_dec_ref_known(v_e_486_, 2);
goto v___jp_497_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_506_ = l_Lean_Expr_appFnCleanup___redArg(v___x_504_);
v___x_507_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___closed__1));
v___x_508_ = l_Lean_Expr_isConstOf(v___x_506_, v___x_507_);
lean_dec_ref(v___x_506_);
if (v___x_508_ == 0)
{
lean_dec_ref(v_arg_501_);
lean_dec_ref(v_fn_500_);
lean_dec_ref_known(v_e_486_, 2);
goto v___jp_497_;
}
else
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_Expr_getAppFn(v_arg_501_);
if (lean_obj_tag(v___x_509_) == 4)
{
lean_object* v_declName_510_; lean_object* v___x_511_; lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_553_; 
v_declName_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_declName_510_);
lean_dec_ref_known(v___x_509_, 2);
v___x_511_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(v_declName_510_, v_a_495_);
v_a_512_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_553_ == 0)
{
v___x_514_ = v___x_511_;
v_isShared_515_ = v_isSharedCheck_553_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_553_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
if (lean_obj_tag(v_a_512_) == 1)
{
lean_object* v_val_516_; lean_object* v_numParams_517_; lean_object* v_numDiscrs_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
lean_del_object(v___x_514_);
v_val_516_ = lean_ctor_get(v_a_512_, 0);
lean_inc(v_val_516_);
lean_dec_ref_known(v_a_512_, 1);
v_numParams_517_ = lean_ctor_get(v_val_516_, 0);
lean_inc(v_numParams_517_);
v_numDiscrs_518_ = lean_ctor_get(v_val_516_, 1);
lean_inc(v_numDiscrs_518_);
lean_dec(v_val_516_);
v___x_519_ = lean_unsigned_to_nat(1u);
v___x_520_ = lean_nat_add(v_numParams_517_, v___x_519_);
lean_dec(v_numParams_517_);
v___x_521_ = lean_nat_add(v___x_520_, v_numDiscrs_518_);
lean_dec(v_numDiscrs_518_);
lean_inc_ref(v_arg_501_);
v___x_522_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_arg_501_, v___x_520_, v___x_521_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
lean_dec(v___x_521_);
lean_dec(v___x_520_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_524_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v___x_524_ = l_Lean_Meta_Sym_Simp_mkCongrArg___redArg(v_e_486_, v_fn_500_, v_arg_501_, v_a_523_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_547_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_547_ == 0)
{
v___x_527_ = v___x_524_;
v_isShared_528_ = v_isSharedCheck_547_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_524_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_547_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
if (lean_obj_tag(v_a_525_) == 0)
{
uint8_t v_contextDependent_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v_contextDependent_529_ = lean_ctor_get_uint8(v_a_525_, 1);
lean_dec_ref_known(v_a_525_, 0);
v___x_530_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_508_, v_contextDependent_529_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_530_);
v___x_532_ = v___x_527_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
else
{
lean_object* v_e_x27_534_; lean_object* v_proof_535_; uint8_t v_contextDependent_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_546_; 
v_e_x27_534_ = lean_ctor_get(v_a_525_, 0);
v_proof_535_ = lean_ctor_get(v_a_525_, 1);
v_contextDependent_536_ = lean_ctor_get_uint8(v_a_525_, sizeof(void*)*2 + 1);
v_isSharedCheck_546_ = !lean_is_exclusive(v_a_525_);
if (v_isSharedCheck_546_ == 0)
{
v___x_538_ = v_a_525_;
v_isShared_539_ = v_isSharedCheck_546_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_proof_535_);
lean_inc(v_e_x27_534_);
lean_dec(v_a_525_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_546_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_e_x27_534_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_proof_535_);
lean_ctor_set_uint8(v_reuseFailAlloc_545_, sizeof(void*)*2 + 1, v_contextDependent_536_);
v___x_541_ = v_reuseFailAlloc_545_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_543_; 
lean_ctor_set_uint8(v___x_541_, sizeof(void*)*2, v___x_508_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_541_);
v___x_543_ = v___x_527_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
}
else
{
return v___x_524_;
}
}
else
{
lean_dec_ref(v_arg_501_);
lean_dec_ref(v_fn_500_);
lean_dec_ref_known(v_e_486_, 2);
return v___x_522_;
}
}
else
{
uint8_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
lean_dec(v_a_512_);
lean_dec_ref(v_arg_501_);
lean_dec_ref(v_fn_500_);
lean_dec_ref_known(v_e_486_, 2);
v___x_548_ = 0;
v___x_549_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_508_, v___x_548_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_549_);
v___x_551_ = v___x_514_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
else
{
uint8_t v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec_ref(v___x_509_);
lean_dec_ref(v_arg_501_);
lean_dec_ref(v_fn_500_);
lean_dec_ref_known(v_e_486_, 2);
v___x_554_ = 0;
v___x_555_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_508_, v___x_554_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
return v___x_556_;
}
}
}
}
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec_ref(v_e_486_);
v___x_557_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
v___jp_497_:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___boxed(lean_object* v_e_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(v_e_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_);
lean_dec(v_a_568_);
lean_dec_ref(v_a_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_a_565_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
return v_res_570_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(lean_object* v_declName_594_){
_start:
{
lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_595_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__2));
v___x_596_ = lean_name_eq(v_declName_594_, v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_597_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__4));
v___x_598_ = lean_name_eq(v_declName_594_, v___x_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_599_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__6));
v___x_600_ = lean_name_eq(v_declName_594_, v___x_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_601_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__9));
v___x_602_ = lean_name_eq(v_declName_594_, v___x_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__12));
v___x_604_ = lean_name_eq(v_declName_594_, v___x_603_);
return v___x_604_;
}
else
{
return v___x_602_;
}
}
else
{
return v___x_600_;
}
}
else
{
return v___x_598_;
}
}
else
{
return v___x_596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___boxed(lean_object* v_declName_605_){
_start:
{
uint8_t v_res_606_; lean_object* v_r_607_; 
v_res_606_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(v_declName_605_);
lean_dec(v_declName_605_);
v_r_607_ = lean_box(v_res_606_);
return v_r_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(lean_object* v_u_608_, lean_object* v___y_609_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = l_Lean_Expr_sort___override(v_u_608_);
v___x_612_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_611_, v___y_609_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg___boxed(lean_object* v_u_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v_u_613_, v___y_614_);
lean_dec(v___y_614_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1(lean_object* v_u_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v_u_617_, v___y_622_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___boxed(lean_object* v_u_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1(v_u_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(lean_object* v_f_641_, lean_object* v_a_u2081_642_, lean_object* v_a_u2082_643_, lean_object* v_a_u2083_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v_f_641_, v_a_u2081_642_, v_a_u2082_643_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_654_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
v___x_654_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_a_653_, v_a_u2083_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
return v___x_654_;
}
else
{
lean_dec_ref(v_a_u2083_644_);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg___boxed(lean_object* v_f_655_, lean_object* v_a_u2081_656_, lean_object* v_a_u2082_657_, lean_object* v_a_u2083_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v_f_655_, v_a_u2081_656_, v_a_u2082_657_, v_a_u2083_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
return v_res_666_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__5(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = lean_box(0);
v___x_678_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__4));
v___x_679_ = l_Lean_mkConst(v___x_678_, v___x_677_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__8(void){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_685_ = lean_box(0);
v___x_686_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__7));
v___x_687_ = l_Lean_mkConst(v___x_686_, v___x_685_);
return v___x_687_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__17(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = lean_box(0);
v___x_705_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__16));
v___x_706_ = l_Lean_mkConst(v___x_705_, v___x_704_);
return v___x_706_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__20(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_712_ = lean_box(0);
v___x_713_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__19));
v___x_714_ = l_Lean_mkConst(v___x_713_, v___x_712_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpEq(lean_object* v_e_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = l_Lean_Expr_cleanupAnnotations(v_e_715_);
v___x_730_ = l_Lean_Expr_isApp(v___x_729_);
if (v___x_730_ == 0)
{
lean_dec_ref(v___x_729_);
goto v___jp_726_;
}
else
{
lean_object* v_arg_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v_arg_731_ = lean_ctor_get(v___x_729_, 1);
lean_inc_ref(v_arg_731_);
v___x_732_ = l_Lean_Expr_appFnCleanup___redArg(v___x_729_);
v___x_733_ = l_Lean_Expr_isApp(v___x_732_);
if (v___x_733_ == 0)
{
lean_dec_ref(v___x_732_);
lean_dec_ref(v_arg_731_);
goto v___jp_726_;
}
else
{
lean_object* v_arg_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v_arg_734_ = lean_ctor_get(v___x_732_, 1);
lean_inc_ref(v_arg_734_);
v___x_735_ = l_Lean_Expr_appFnCleanup___redArg(v___x_732_);
v___x_736_ = l_Lean_Expr_isApp(v___x_735_);
if (v___x_736_ == 0)
{
lean_dec_ref(v___x_735_);
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_731_);
goto v___jp_726_;
}
else
{
lean_object* v_arg_737_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v_arg_737_ = lean_ctor_get(v___x_735_, 1);
lean_inc_ref(v_arg_737_);
v___x_738_ = l_Lean_Expr_appFnCleanup___redArg(v___x_735_);
v___x_739_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__1));
v___x_740_ = l_Lean_Expr_isConstOf(v___x_738_, v___x_739_);
if (v___x_740_ == 0)
{
lean_dec_ref(v___x_738_);
lean_dec_ref(v_arg_737_);
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_731_);
goto v___jp_726_;
}
else
{
lean_object* v___x_741_; 
lean_inc_ref(v_arg_737_);
v___x_741_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_737_, v_a_722_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_908_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_908_ == 0)
{
v___x_744_ = v___x_741_;
v_isShared_745_ = v_isSharedCheck_908_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_741_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_908_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_751_ = l_Lean_Expr_cleanupAnnotations(v_a_742_);
v___x_752_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__2));
v___x_753_ = l_Lean_Expr_isConstOf(v___x_751_, v___x_752_);
lean_dec_ref(v___x_751_);
if (v___x_753_ == 0)
{
size_t v___x_754_; size_t v___x_755_; uint8_t v___x_756_; 
lean_del_object(v___x_744_);
v___x_754_ = lean_ptr_addr(v_arg_734_);
v___x_755_ = lean_ptr_addr(v_arg_731_);
v___x_756_ = lean_usize_dec_eq(v___x_754_, v___x_755_);
if (v___x_756_ == 0)
{
uint8_t v___x_757_; 
lean_dec_ref(v___x_738_);
lean_dec_ref(v_arg_737_);
lean_inc_ref(v_arg_731_);
v___x_757_ = l_Lean_Expr_isTrue(v_arg_731_);
if (v___x_757_ == 0)
{
uint8_t v___x_758_; 
v___x_758_ = l_Lean_Expr_isFalse(v_arg_731_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v___x_760_; 
lean_dec_ref(v_arg_734_);
v___x_759_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_759_, 0, v___x_758_);
lean_ctor_set_uint8(v___x_759_, 1, v___x_758_);
v___x_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
return v___x_760_;
}
else
{
lean_object* v___x_761_; 
lean_inc_ref(v_arg_734_);
v___x_761_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_734_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_772_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_772_ == 0)
{
v___x_764_ = v___x_761_;
v_isShared_765_ = v_isSharedCheck_772_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_761_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_772_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_766_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpEq___closed__5, &l_Lean_Meta_Grind_NormSym_simpEq___closed__5_once, _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__5);
v___x_767_ = l_Lean_Expr_app___override(v___x_766_, v_arg_734_);
v___x_768_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_768_, 0, v_a_762_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*2, v___x_757_);
lean_ctor_set_uint8(v___x_768_, sizeof(void*)*2 + 1, v___x_757_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_768_);
v___x_770_ = v___x_764_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec_ref(v_arg_734_);
v_a_773_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_761_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_761_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
else
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
lean_dec_ref(v_arg_731_);
v___x_781_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpEq___closed__8, &l_Lean_Meta_Grind_NormSym_simpEq___closed__8_once, _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__8);
lean_inc_ref(v_arg_734_);
v___x_782_ = l_Lean_Expr_app___override(v___x_781_, v_arg_734_);
v___x_783_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_783_, 0, v_arg_734_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*2, v___x_740_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*2 + 1, v___x_756_);
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
return v___x_784_;
}
}
else
{
lean_object* v___x_785_; 
lean_dec_ref(v_arg_731_);
v___x_785_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_719_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_798_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_798_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_798_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_798_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_790_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__10));
v___x_791_ = l_Lean_Expr_constLevels_x21(v___x_738_);
lean_dec_ref(v___x_738_);
v___x_792_ = l_Lean_mkConst(v___x_790_, v___x_791_);
v___x_793_ = l_Lean_mkAppB(v___x_792_, v_arg_737_, v_arg_734_);
v___x_794_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_794_, 0, v_a_786_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
lean_ctor_set_uint8(v___x_794_, sizeof(void*)*2, v___x_740_);
lean_ctor_set_uint8(v___x_794_, sizeof(void*)*2 + 1, v___x_753_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_794_);
v___x_796_ = v___x_788_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref(v___x_738_);
lean_dec_ref(v_arg_737_);
lean_dec_ref(v_arg_734_);
v_a_799_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_785_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_785_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
else
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_Expr_getAppFn(v_arg_731_);
if (lean_obj_tag(v___x_807_) == 4)
{
lean_object* v_declName_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v_declName_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_declName_808_);
lean_dec_ref_known(v___x_807_, 2);
v___x_809_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__12));
v___x_810_ = lean_name_eq(v_declName_808_, v___x_809_);
if (v___x_810_ == 0)
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__14));
v___x_812_ = lean_name_eq(v_declName_808_, v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_834_; 
lean_del_object(v___x_744_);
v___x_834_ = l_Lean_Expr_getAppFn(v_arg_734_);
if (lean_obj_tag(v___x_834_) == 4)
{
lean_object* v_declName_835_; uint8_t v___x_836_; 
v_declName_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_declName_835_);
lean_dec_ref_known(v___x_834_, 2);
v___x_836_ = lean_name_eq(v_declName_835_, v___x_809_);
if (v___x_836_ == 0)
{
uint8_t v___x_837_; 
v___x_837_ = lean_name_eq(v_declName_835_, v___x_811_);
if (v___x_837_ == 0)
{
uint8_t v___x_900_; 
v___x_900_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(v_declName_835_);
lean_dec(v_declName_835_);
if (v___x_900_ == 0)
{
uint8_t v___x_901_; 
v___x_901_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(v_declName_808_);
lean_dec(v_declName_808_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; 
lean_dec_ref(v___x_738_);
lean_dec_ref(v_arg_737_);
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_731_);
v___x_902_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_902_, 0, v___x_901_);
lean_ctor_set_uint8(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
return v___x_903_;
}
else
{
goto v___jp_838_;
}
}
else
{
lean_dec(v_declName_808_);
goto v___jp_838_;
}
}
else
{
lean_dec(v_declName_835_);
lean_dec(v_declName_808_);
goto v___jp_813_;
}
v___jp_838_:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_719_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
v___x_841_ = lean_box(0);
v___x_842_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v___x_841_, v_a_720_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_844_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_843_);
lean_dec_ref_known(v___x_842_, 1);
lean_inc(v_a_840_);
lean_inc_ref(v_arg_734_);
lean_inc_ref(v_arg_737_);
lean_inc_ref(v___x_738_);
v___x_844_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v___x_738_, v_arg_737_, v_arg_734_, v_a_840_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; lean_object* v___x_846_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v___x_844_, 1);
lean_inc_ref(v_arg_731_);
lean_inc_ref(v___x_738_);
v___x_846_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v___x_738_, v_arg_737_, v_arg_731_, v_a_840_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_848_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_846_, 1);
v___x_848_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v___x_738_, v_a_843_, v_a_845_, v_a_847_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_859_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_859_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_859_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_859_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_853_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpEq___closed__20, &l_Lean_Meta_Grind_NormSym_simpEq___closed__20_once, _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__20);
v___x_854_ = l_Lean_mkAppB(v___x_853_, v_arg_734_, v_arg_731_);
v___x_855_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_855_, 0, v_a_849_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
lean_ctor_set_uint8(v___x_855_, sizeof(void*)*2, v___x_837_);
lean_ctor_set_uint8(v___x_855_, sizeof(void*)*2 + 1, v___x_837_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_855_);
v___x_857_ = v___x_851_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_731_);
v_a_860_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_848_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_848_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec(v_a_845_);
lean_dec(v_a_843_);
lean_dec_ref(v___x_738_);
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_731_);
v_a_868_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_846_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_846_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec(v_a_843_);
lean_dec(v_a_840_);
lean_dec_ref(v___x_738_);
lean_dec_ref(v_arg_737_);
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_731_);
v_a_876_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_844_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_844_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec(v_a_840_);
lean_dec_ref(v___x_738_);
lean_dec_ref(v_arg_737_);
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_731_);
v_a_884_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_842_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_842_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec_ref(v___x_738_);
lean_dec_ref(v_arg_737_);
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_731_);
v_a_892_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_839_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_839_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
else
{
lean_dec(v_declName_835_);
lean_dec(v_declName_808_);
goto v___jp_813_;
}
}
else
{
lean_object* v___x_904_; lean_object* v___x_905_; 
lean_dec_ref(v___x_834_);
lean_dec(v_declName_808_);
lean_dec_ref(v___x_738_);
lean_dec_ref(v_arg_737_);
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_731_);
v___x_904_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_904_, 0, v___x_812_);
lean_ctor_set_uint8(v___x_904_, 1, v___x_812_);
v___x_905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
return v___x_905_;
}
}
else
{
lean_dec(v_declName_808_);
lean_dec_ref(v___x_738_);
lean_dec_ref(v_arg_737_);
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_731_);
goto v___jp_746_;
}
v___jp_813_:
{
lean_object* v___x_814_; 
lean_inc_ref(v_arg_734_);
lean_inc_ref(v_arg_731_);
v___x_814_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v___x_738_, v_arg_737_, v_arg_731_, v_arg_734_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_825_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_825_ == 0)
{
v___x_817_ = v___x_814_;
v_isShared_818_ = v_isSharedCheck_825_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_814_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_825_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_819_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpEq___closed__17, &l_Lean_Meta_Grind_NormSym_simpEq___closed__17_once, _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__17);
v___x_820_ = l_Lean_mkAppB(v___x_819_, v_arg_734_, v_arg_731_);
v___x_821_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_821_, 0, v_a_815_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*2, v___x_812_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*2 + 1, v___x_812_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v___x_821_);
v___x_823_ = v___x_817_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
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
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_731_);
v_a_826_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_814_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_814_);
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
else
{
lean_dec(v_declName_808_);
lean_dec_ref(v___x_738_);
lean_dec_ref(v_arg_737_);
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_731_);
goto v___jp_746_;
}
}
else
{
lean_object* v___x_906_; lean_object* v___x_907_; 
lean_dec_ref(v___x_807_);
lean_del_object(v___x_744_);
lean_dec_ref(v___x_738_);
lean_dec_ref(v_arg_737_);
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_731_);
v___x_906_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
return v___x_907_;
}
}
v___jp_746_:
{
lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_747_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_747_);
v___x_749_ = v___x_744_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec_ref(v___x_738_);
lean_dec_ref(v_arg_737_);
lean_dec_ref(v_arg_734_);
lean_dec_ref(v_arg_731_);
v_a_909_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_741_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_741_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
}
}
}
v___jp_726_:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpEq___boxed(lean_object* v_e_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_Meta_Grind_NormSym_simpEq(v_e_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(lean_object* v_f_929_, lean_object* v_a_u2081_930_, lean_object* v_a_u2082_931_, lean_object* v_a_u2083_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v_f_929_, v_a_u2081_930_, v_a_u2082_931_, v_a_u2083_932_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___boxed(lean_object* v_f_944_, lean_object* v_a_u2081_945_, lean_object* v_a_u2082_946_, lean_object* v_a_u2083_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v_f_944_, v_a_u2081_945_, v_a_u2082_946_, v_a_u2083_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___redArg(lean_object* v_f_959_, lean_object* v_a_u2081_960_, lean_object* v_a_u2082_961_, lean_object* v_a_u2083_962_, lean_object* v_a_u2084_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v_f_959_, v_a_u2081_960_, v_a_u2082_961_, v_a_u2083_962_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_973_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_971_, 1);
v___x_973_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_a_972_, v_a_u2084_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
return v___x_973_;
}
else
{
lean_dec_ref(v_a_u2084_963_);
return v___x_971_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___redArg___boxed(lean_object* v_f_974_, lean_object* v_a_u2081_975_, lean_object* v_a_u2082_976_, lean_object* v_a_u2083_977_, lean_object* v_a_u2084_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___redArg(v_f_974_, v_a_u2081_975_, v_a_u2082_976_, v_a_u2083_977_, v_a_u2084_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0(lean_object* v_f_987_, lean_object* v_a_u2081_988_, lean_object* v_a_u2082_989_, lean_object* v_a_u2083_990_, lean_object* v_a_u2084_991_, lean_object* v_a_u2085_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___redArg(v_f_987_, v_a_u2081_988_, v_a_u2082_989_, v_a_u2083_990_, v_a_u2084_991_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_a_1004_, v_a_u2085_992_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
return v___x_1005_;
}
else
{
lean_dec_ref(v_a_u2085_992_);
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___boxed(lean_object* v_f_1006_, lean_object* v_a_u2081_1007_, lean_object* v_a_u2082_1008_, lean_object* v_a_u2083_1009_, lean_object* v_a_u2084_1010_, lean_object* v_a_u2085_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0(v_f_1006_, v_a_u2081_1007_, v_a_u2082_1008_, v_a_u2083_1009_, v_a_u2084_1010_, v_a_u2085_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpDIte(lean_object* v_e_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___x_1046_; uint8_t v___x_1047_; 
v___x_1046_ = l_Lean_Expr_cleanupAnnotations(v_e_1032_);
v___x_1047_ = l_Lean_Expr_isApp(v___x_1046_);
if (v___x_1047_ == 0)
{
lean_dec_ref(v___x_1046_);
goto v___jp_1043_;
}
else
{
lean_object* v_arg_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v_arg_1048_ = lean_ctor_get(v___x_1046_, 1);
lean_inc_ref(v_arg_1048_);
v___x_1049_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1046_);
v___x_1050_ = l_Lean_Expr_isApp(v___x_1049_);
if (v___x_1050_ == 0)
{
lean_dec_ref(v___x_1049_);
lean_dec_ref(v_arg_1048_);
goto v___jp_1043_;
}
else
{
lean_object* v_arg_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v_arg_1051_ = lean_ctor_get(v___x_1049_, 1);
lean_inc_ref(v_arg_1051_);
v___x_1052_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1049_);
v___x_1053_ = l_Lean_Expr_isApp(v___x_1052_);
if (v___x_1053_ == 0)
{
lean_dec_ref(v___x_1052_);
lean_dec_ref(v_arg_1051_);
lean_dec_ref(v_arg_1048_);
goto v___jp_1043_;
}
else
{
lean_object* v_arg_1054_; lean_object* v___x_1055_; uint8_t v___x_1056_; 
v_arg_1054_ = lean_ctor_get(v___x_1052_, 1);
lean_inc_ref(v_arg_1054_);
v___x_1055_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1052_);
v___x_1056_ = l_Lean_Expr_isApp(v___x_1055_);
if (v___x_1056_ == 0)
{
lean_dec_ref(v___x_1055_);
lean_dec_ref(v_arg_1054_);
lean_dec_ref(v_arg_1051_);
lean_dec_ref(v_arg_1048_);
goto v___jp_1043_;
}
else
{
lean_object* v_arg_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v_arg_1057_ = lean_ctor_get(v___x_1055_, 1);
lean_inc_ref(v_arg_1057_);
v___x_1058_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1055_);
v___x_1059_ = l_Lean_Expr_isApp(v___x_1058_);
if (v___x_1059_ == 0)
{
lean_dec_ref(v___x_1058_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_arg_1054_);
lean_dec_ref(v_arg_1051_);
lean_dec_ref(v_arg_1048_);
goto v___jp_1043_;
}
else
{
lean_object* v_arg_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v_arg_1060_ = lean_ctor_get(v___x_1058_, 1);
lean_inc_ref(v_arg_1060_);
v___x_1061_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1058_);
v___x_1062_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpDIte___closed__1));
v___x_1063_ = l_Lean_Expr_isConstOf(v___x_1061_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_dec_ref(v___x_1061_);
lean_dec_ref(v_arg_1060_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_arg_1054_);
lean_dec_ref(v_arg_1051_);
lean_dec_ref(v_arg_1048_);
goto v___jp_1043_;
}
else
{
if (lean_obj_tag(v_arg_1051_) == 6)
{
lean_object* v_body_1064_; uint8_t v___x_1065_; 
v_body_1064_ = lean_ctor_get(v_arg_1051_, 2);
lean_inc_ref(v_body_1064_);
lean_dec_ref_known(v_arg_1051_, 3);
v___x_1065_ = l_Lean_Expr_hasLooseBVars(v_body_1064_);
if (v___x_1065_ == 0)
{
if (lean_obj_tag(v_arg_1048_) == 6)
{
lean_object* v_body_1066_; uint8_t v___x_1067_; 
v_body_1066_ = lean_ctor_get(v_arg_1048_, 2);
lean_inc_ref(v_body_1066_);
lean_dec_ref_known(v_arg_1048_, 3);
v___x_1067_ = l_Lean_Expr_hasLooseBVars(v_body_1066_);
if (v___x_1067_ == 0)
{
lean_object* v_us_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_us_1068_ = l_Lean_Expr_constLevels_x21(v___x_1061_);
lean_dec_ref(v___x_1061_);
v___x_1069_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpDIte___closed__3));
lean_inc(v_us_1068_);
v___x_1070_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v___x_1069_, v_us_1068_, v_a_1037_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1072_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1071_);
lean_dec_ref_known(v___x_1070_, 1);
lean_inc_ref(v_body_1066_);
lean_inc_ref(v_body_1064_);
lean_inc_ref(v_arg_1054_);
lean_inc_ref(v_arg_1057_);
lean_inc_ref(v_arg_1060_);
v___x_1072_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0(v_a_1071_, v_arg_1060_, v_arg_1057_, v_arg_1054_, v_body_1064_, v_body_1066_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1084_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1084_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1084_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1077_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpDIte___closed__5));
v___x_1078_ = l_Lean_mkConst(v___x_1077_, v_us_1068_);
v___x_1079_ = l_Lean_mkApp5(v___x_1078_, v_arg_1057_, v_arg_1060_, v_body_1064_, v_body_1066_, v_arg_1054_);
v___x_1080_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1080_, 0, v_a_1073_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
lean_ctor_set_uint8(v___x_1080_, sizeof(void*)*2, v___x_1067_);
lean_ctor_set_uint8(v___x_1080_, sizeof(void*)*2 + 1, v___x_1067_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1080_);
v___x_1082_ = v___x_1075_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
lean_dec(v_us_1068_);
lean_dec_ref(v_body_1066_);
lean_dec_ref(v_body_1064_);
lean_dec_ref(v_arg_1060_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_arg_1054_);
v_a_1085_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1072_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1072_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
else
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
lean_dec(v_us_1068_);
lean_dec_ref(v_body_1066_);
lean_dec_ref(v_body_1064_);
lean_dec_ref(v_arg_1060_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_arg_1054_);
v_a_1093_ = lean_ctor_get(v___x_1070_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1070_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1095_ = v___x_1070_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1070_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_a_1093_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
else
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
lean_dec_ref(v_body_1066_);
lean_dec_ref(v_body_1064_);
lean_dec_ref(v___x_1061_);
lean_dec_ref(v_arg_1060_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_arg_1054_);
v___x_1101_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1101_, 0, v___x_1065_);
lean_ctor_set_uint8(v___x_1101_, 1, v___x_1065_);
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
}
else
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_dec_ref(v_body_1064_);
lean_dec_ref(v___x_1061_);
lean_dec_ref(v_arg_1060_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_arg_1054_);
lean_dec_ref(v_arg_1048_);
v___x_1103_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1103_, 0, v___x_1065_);
lean_ctor_set_uint8(v___x_1103_, 1, v___x_1065_);
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
return v___x_1104_;
}
}
else
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_dec_ref(v_body_1064_);
lean_dec_ref(v___x_1061_);
lean_dec_ref(v_arg_1060_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_arg_1054_);
lean_dec_ref(v_arg_1048_);
v___x_1105_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
return v___x_1106_;
}
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec_ref(v___x_1061_);
lean_dec_ref(v_arg_1060_);
lean_dec_ref(v_arg_1057_);
lean_dec_ref(v_arg_1054_);
lean_dec_ref(v_arg_1051_);
lean_dec_ref(v_arg_1048_);
v___x_1107_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
return v___x_1108_;
}
}
}
}
}
}
}
v___jp_1043_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
return v___x_1045_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpDIte___boxed(lean_object* v_e_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_Meta_Grind_NormSym_simpDIte(v_e_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
lean_dec(v_a_1110_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0(lean_object* v_f_1121_, lean_object* v_a_u2081_1122_, lean_object* v_a_u2082_1123_, lean_object* v_a_u2083_1124_, lean_object* v_a_u2084_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___redArg(v_f_1121_, v_a_u2081_1122_, v_a_u2082_1123_, v_a_u2083_1124_, v_a_u2084_1125_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___boxed(lean_object* v_f_1137_, lean_object* v_a_u2081_1138_, lean_object* v_a_u2082_1139_, lean_object* v_a_u2083_1140_, lean_object* v_a_u2084_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0(v_f_1137_, v_a_u2081_1138_, v_a_u2082_1139_, v_a_u2083_1140_, v_a_u2084_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(lean_object* v_x_1153_, uint8_t v_bi_1154_, lean_object* v_t_1155_, lean_object* v_b_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___y_1165_; lean_object* v___x_1168_; uint8_t v_debug_1169_; 
v___x_1168_ = lean_st_ref_get(v___y_1158_);
v_debug_1169_ = lean_ctor_get_uint8(v___x_1168_, sizeof(void*)*12);
lean_dec(v___x_1168_);
if (v_debug_1169_ == 0)
{
v___y_1165_ = v___y_1158_;
goto v___jp_1164_;
}
else
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1155_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v___x_1171_; 
lean_dec_ref_known(v___x_1170_, 1);
v___x_1171_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_dec_ref_known(v___x_1171_, 1);
v___y_1165_ = v___y_1158_;
goto v___jp_1164_;
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec_ref(v_b_1156_);
lean_dec_ref(v_t_1155_);
lean_dec(v_x_1153_);
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1171_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec_ref(v_b_1156_);
lean_dec_ref(v_t_1155_);
lean_dec(v_x_1153_);
v_a_1180_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1170_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1170_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
v___jp_1164_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = l_Lean_Expr_lam___override(v_x_1153_, v_t_1155_, v_b_1156_, v_bi_1154_);
v___x_1167_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1166_, v___y_1165_);
return v___x_1167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg___boxed(lean_object* v_x_1188_, lean_object* v_bi_1189_, lean_object* v_t_1190_, lean_object* v_b_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
uint8_t v_bi_boxed_1199_; lean_object* v_res_1200_; 
v_bi_boxed_1199_ = lean_unbox(v_bi_1189_);
v_res_1200_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_x_1188_, v_bi_boxed_1199_, v_t_1190_, v_b_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0(lean_object* v_x_1201_, uint8_t v_bi_1202_, lean_object* v_t_1203_, lean_object* v_b_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_x_1201_, v_bi_1202_, v_t_1203_, v_b_1204_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___boxed(lean_object* v_x_1216_, lean_object* v_bi_1217_, lean_object* v_t_1218_, lean_object* v_b_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
uint8_t v_bi_boxed_1230_; lean_object* v_res_1231_; 
v_bi_boxed_1230_ = lean_unbox(v_bi_1217_);
v_res_1231_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0(v_x_1216_, v_bi_boxed_1230_, v_t_1218_, v_b_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(lean_object* v_idx_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = l_Lean_Expr_bvar___override(v_idx_1232_);
v___x_1236_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1235_, v___y_1233_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg___boxed(lean_object* v_idx_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(v_idx_1237_, v___y_1238_);
lean_dec(v___y_1238_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1(lean_object* v_idx_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(v_idx_1241_, v___y_1246_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___boxed(lean_object* v_idx_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1(v_idx_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(lean_object* v_x_1265_, uint8_t v_bi_1266_, lean_object* v_t_1267_, lean_object* v_b_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
lean_object* v___y_1277_; lean_object* v___x_1280_; uint8_t v_debug_1281_; 
v___x_1280_ = lean_st_ref_get(v___y_1270_);
v_debug_1281_ = lean_ctor_get_uint8(v___x_1280_, sizeof(void*)*12);
lean_dec(v___x_1280_);
if (v_debug_1281_ == 0)
{
v___y_1277_ = v___y_1270_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1267_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v___x_1283_; 
lean_dec_ref_known(v___x_1282_, 1);
v___x_1283_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_dec_ref_known(v___x_1283_, 1);
v___y_1277_ = v___y_1270_;
goto v___jp_1276_;
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec_ref(v_b_1268_);
lean_dec_ref(v_t_1267_);
lean_dec(v_x_1265_);
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec_ref(v_b_1268_);
lean_dec_ref(v_t_1267_);
lean_dec(v_x_1265_);
v_a_1292_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1282_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1282_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
}
v___jp_1276_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = l_Lean_Expr_forallE___override(v_x_1265_, v_t_1267_, v_b_1268_, v_bi_1266_);
v___x_1279_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1278_, v___y_1277_);
return v___x_1279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg___boxed(lean_object* v_x_1300_, lean_object* v_bi_1301_, lean_object* v_t_1302_, lean_object* v_b_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
uint8_t v_bi_boxed_1311_; lean_object* v_res_1312_; 
v_bi_boxed_1311_ = lean_unbox(v_bi_1301_);
v_res_1312_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_x_1300_, v_bi_boxed_1311_, v_t_1302_, v_b_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2(lean_object* v_x_1313_, uint8_t v_bi_1314_, lean_object* v_t_1315_, lean_object* v_b_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_x_1313_, v_bi_1314_, v_t_1315_, v_b_1316_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___boxed(lean_object* v_x_1328_, lean_object* v_bi_1329_, lean_object* v_t_1330_, lean_object* v_b_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
uint8_t v_bi_boxed_1342_; lean_object* v_res_1343_; 
v_bi_boxed_1342_ = lean_unbox(v_bi_1329_);
v_res_1343_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2(v_x_1328_, v_bi_boxed_1342_, v_t_1330_, v_b_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
return v_res_1343_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__4(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1354_ = lean_box(0);
v___x_1355_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__3));
v___x_1356_ = l_Lean_mkConst(v___x_1355_, v___x_1354_);
return v___x_1356_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__11(void){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1368_ = lean_box(0);
v___x_1369_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__10));
v___x_1370_ = l_Lean_mkConst(v___x_1369_, v___x_1368_);
return v___x_1370_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__14(void){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = lean_box(0);
v___x_1376_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__13));
v___x_1377_ = l_Lean_mkConst(v___x_1376_, v___x_1375_);
return v___x_1377_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__17(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = lean_box(0);
v___x_1383_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__16));
v___x_1384_ = l_Lean_mkConst(v___x_1383_, v___x_1382_);
return v___x_1384_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__20(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = lean_box(0);
v___x_1391_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__19));
v___x_1392_ = l_Lean_mkConst(v___x_1391_, v___x_1390_);
return v___x_1392_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__23(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1398_ = lean_box(0);
v___x_1399_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__22));
v___x_1400_ = l_Lean_mkConst(v___x_1399_, v___x_1398_);
return v___x_1400_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__26(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1406_ = lean_box(0);
v___x_1407_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__25));
v___x_1408_ = l_Lean_mkConst(v___x_1407_, v___x_1406_);
return v___x_1408_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__33(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = lean_box(0);
v___x_1423_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__32));
v___x_1424_ = l_Lean_mkConst(v___x_1423_, v___x_1422_);
return v___x_1424_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__36(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = lean_box(0);
v___x_1431_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__35));
v___x_1432_ = l_Lean_mkConst(v___x_1431_, v___x_1430_);
return v___x_1432_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__39(void){
_start:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1438_ = lean_box(0);
v___x_1439_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__38));
v___x_1440_ = l_Lean_mkConst(v___x_1439_, v___x_1438_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_pushNot(lean_object* v_e_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; uint8_t v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; uint8_t v___y_1466_; lean_object* v___x_1524_; uint8_t v___x_1525_; 
v___x_1524_ = l_Lean_Expr_cleanupAnnotations(v_e_1441_);
v___x_1525_ = l_Lean_Expr_isApp(v___x_1524_);
if (v___x_1525_ == 0)
{
lean_dec_ref(v___x_1524_);
goto v___jp_1521_;
}
else
{
lean_object* v_arg_1526_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___x_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; 
v_arg_1526_ = lean_ctor_get(v___x_1524_, 1);
lean_inc_ref(v_arg_1526_);
v___x_1587_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1524_);
v___x_1588_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS___closed__1));
v___x_1589_ = l_Lean_Expr_isConstOf(v___x_1587_, v___x_1588_);
lean_dec_ref(v___x_1587_);
if (v___x_1589_ == 0)
{
lean_dec_ref(v_arg_1526_);
goto v___jp_1521_;
}
else
{
lean_object* v___x_1590_; 
lean_inc_ref(v_arg_1526_);
v___x_1590_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1526_, v_a_1448_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1974_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1974_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1974_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v___x_1595_ = l_Lean_Expr_cleanupAnnotations(v_a_1591_);
v___x_1596_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__6));
v___x_1597_ = l_Lean_Expr_isConstOf(v___x_1595_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1598_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_1599_ = l_Lean_Expr_isConstOf(v___x_1595_, v___x_1598_);
if (v___x_1599_ == 0)
{
uint8_t v___x_1600_; 
v___x_1600_ = l_Lean_Expr_isApp(v___x_1595_);
if (v___x_1600_ == 0)
{
lean_dec_ref(v___x_1595_);
lean_del_object(v___x_1593_);
v___y_1528_ = v_a_1442_;
v___y_1529_ = v_a_1443_;
v___y_1530_ = v_a_1444_;
v___y_1531_ = v_a_1445_;
v___y_1532_ = v_a_1446_;
v___y_1533_ = v_a_1447_;
v___y_1534_ = v_a_1448_;
v___y_1535_ = v_a_1449_;
v___y_1536_ = v_a_1450_;
goto v___jp_1527_;
}
else
{
lean_object* v_arg_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
v_arg_1601_ = lean_ctor_get(v___x_1595_, 1);
lean_inc_ref(v_arg_1601_);
v___x_1602_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1595_);
v___x_1603_ = l_Lean_Expr_isConstOf(v___x_1602_, v___x_1588_);
if (v___x_1603_ == 0)
{
uint8_t v___x_1604_; 
lean_del_object(v___x_1593_);
v___x_1604_ = l_Lean_Expr_isApp(v___x_1602_);
if (v___x_1604_ == 0)
{
lean_dec_ref(v___x_1602_);
lean_dec_ref(v_arg_1601_);
v___y_1528_ = v_a_1442_;
v___y_1529_ = v_a_1443_;
v___y_1530_ = v_a_1444_;
v___y_1531_ = v_a_1445_;
v___y_1532_ = v_a_1446_;
v___y_1533_ = v_a_1447_;
v___y_1534_ = v_a_1448_;
v___y_1535_ = v_a_1449_;
v___y_1536_ = v_a_1450_;
goto v___jp_1527_;
}
else
{
lean_object* v_arg_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; 
v_arg_1605_ = lean_ctor_get(v___x_1602_, 1);
lean_inc_ref(v_arg_1605_);
v___x_1606_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1602_);
v___x_1607_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg___closed__1));
v___x_1608_ = l_Lean_Expr_isConstOf(v___x_1606_, v___x_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1));
v___x_1610_ = l_Lean_Expr_isConstOf(v___x_1606_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1611_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS___closed__1));
v___x_1612_ = l_Lean_Expr_isConstOf(v___x_1606_, v___x_1611_);
if (v___x_1612_ == 0)
{
uint8_t v___x_1613_; 
v___x_1613_ = l_Lean_Expr_isApp(v___x_1606_);
if (v___x_1613_ == 0)
{
lean_dec_ref(v___x_1606_);
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1601_);
v___y_1528_ = v_a_1442_;
v___y_1529_ = v_a_1443_;
v___y_1530_ = v_a_1444_;
v___y_1531_ = v_a_1445_;
v___y_1532_ = v_a_1446_;
v___y_1533_ = v_a_1447_;
v___y_1534_ = v_a_1448_;
v___y_1535_ = v_a_1449_;
v___y_1536_ = v_a_1450_;
goto v___jp_1527_;
}
else
{
lean_object* v_arg_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
v_arg_1614_ = lean_ctor_get(v___x_1606_, 1);
lean_inc_ref(v_arg_1614_);
v___x_1615_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1606_);
v___x_1616_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__1));
v___x_1617_ = l_Lean_Expr_isConstOf(v___x_1615_, v___x_1616_);
if (v___x_1617_ == 0)
{
uint8_t v___x_1618_; 
v___x_1618_ = l_Lean_Expr_isApp(v___x_1615_);
if (v___x_1618_ == 0)
{
lean_dec_ref(v___x_1615_);
lean_dec_ref(v_arg_1614_);
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1601_);
v___y_1528_ = v_a_1442_;
v___y_1529_ = v_a_1443_;
v___y_1530_ = v_a_1444_;
v___y_1531_ = v_a_1445_;
v___y_1532_ = v_a_1446_;
v___y_1533_ = v_a_1447_;
v___y_1534_ = v_a_1448_;
v___y_1535_ = v_a_1449_;
v___y_1536_ = v_a_1450_;
goto v___jp_1527_;
}
else
{
lean_object* v_arg_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v_arg_1619_ = lean_ctor_get(v___x_1615_, 1);
lean_inc_ref(v_arg_1619_);
v___x_1620_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1615_);
v___x_1621_ = l_Lean_Expr_isApp(v___x_1620_);
if (v___x_1621_ == 0)
{
lean_dec_ref(v___x_1620_);
lean_dec_ref(v_arg_1619_);
lean_dec_ref(v_arg_1614_);
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1601_);
v___y_1528_ = v_a_1442_;
v___y_1529_ = v_a_1443_;
v___y_1530_ = v_a_1444_;
v___y_1531_ = v_a_1445_;
v___y_1532_ = v_a_1446_;
v___y_1533_ = v_a_1447_;
v___y_1534_ = v_a_1448_;
v___y_1535_ = v_a_1449_;
v___y_1536_ = v_a_1450_;
goto v___jp_1527_;
}
else
{
lean_object* v_arg_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v_arg_1622_ = lean_ctor_get(v___x_1620_, 1);
lean_inc_ref(v_arg_1622_);
v___x_1623_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1620_);
v___x_1624_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpDIte___closed__3));
v___x_1625_ = l_Lean_Expr_isConstOf(v___x_1623_, v___x_1624_);
if (v___x_1625_ == 0)
{
lean_dec_ref(v___x_1623_);
lean_dec_ref(v_arg_1622_);
lean_dec_ref(v_arg_1619_);
lean_dec_ref(v_arg_1614_);
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1601_);
v___y_1528_ = v_a_1442_;
v___y_1529_ = v_a_1443_;
v___y_1530_ = v_a_1444_;
v___y_1531_ = v_a_1445_;
v___y_1532_ = v_a_1446_;
v___y_1533_ = v_a_1447_;
v___y_1534_ = v_a_1448_;
v___y_1535_ = v_a_1449_;
v___y_1536_ = v_a_1450_;
goto v___jp_1527_;
}
else
{
lean_object* v___x_1626_; 
lean_dec_ref(v_arg_1526_);
lean_inc_ref(v_arg_1605_);
v___x_1626_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1605_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1628_; 
v_a_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v___x_1626_, 1);
lean_inc_ref(v_arg_1601_);
v___x_1628_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1601_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1630_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___x_1628_, 1);
lean_inc_ref(v_arg_1614_);
lean_inc_ref(v_arg_1619_);
v___x_1630_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0(v___x_1623_, v_arg_1622_, v_arg_1619_, v_arg_1614_, v_a_1627_, v_a_1629_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1641_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1633_ = v___x_1630_;
v_isShared_1634_ = v_isSharedCheck_1641_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1641_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1639_; 
v___x_1635_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__11, &l_Lean_Meta_Grind_NormSym_pushNot___closed__11_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__11);
v___x_1636_ = l_Lean_mkApp4(v___x_1635_, v_arg_1619_, v_arg_1614_, v_arg_1605_, v_arg_1601_);
v___x_1637_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1637_, 0, v_a_1631_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
lean_ctor_set_uint8(v___x_1637_, sizeof(void*)*2, v___x_1617_);
lean_ctor_set_uint8(v___x_1637_, sizeof(void*)*2 + 1, v___x_1617_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v___x_1637_);
v___x_1639_ = v___x_1633_;
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
else
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1649_; 
lean_dec_ref(v_arg_1619_);
lean_dec_ref(v_arg_1614_);
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1601_);
v_a_1642_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1644_ = v___x_1630_;
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1630_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1649_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1647_; 
if (v_isShared_1645_ == 0)
{
v___x_1647_ = v___x_1644_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_a_1642_);
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
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec(v_a_1627_);
lean_dec_ref(v___x_1623_);
lean_dec_ref(v_arg_1622_);
lean_dec_ref(v_arg_1619_);
lean_dec_ref(v_arg_1614_);
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1601_);
v_a_1650_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1628_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1628_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec_ref(v___x_1623_);
lean_dec_ref(v_arg_1622_);
lean_dec_ref(v_arg_1619_);
lean_dec_ref(v_arg_1614_);
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1601_);
v_a_1658_ = lean_ctor_get(v___x_1626_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1626_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1626_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1626_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1663_; 
if (v_isShared_1661_ == 0)
{
v___x_1663_ = v___x_1660_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
}
}
}
}
}
else
{
uint8_t v___x_1666_; 
lean_dec_ref(v_arg_1526_);
v___x_1666_ = l_Lean_Expr_isProp(v_arg_1614_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1601_, v_a_1448_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1741_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1670_ = v___x_1667_;
v_isShared_1671_ = v_isSharedCheck_1741_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1667_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1741_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; uint8_t v___x_1674_; 
v___x_1672_ = l_Lean_Expr_cleanupAnnotations(v_a_1668_);
v___x_1673_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__14));
v___x_1674_ = l_Lean_Expr_isConstOf(v___x_1672_, v___x_1673_);
if (v___x_1674_ == 0)
{
lean_object* v___x_1675_; uint8_t v___x_1676_; 
v___x_1675_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__12));
v___x_1676_ = l_Lean_Expr_isConstOf(v___x_1672_, v___x_1675_);
lean_dec_ref(v___x_1672_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
lean_dec_ref(v___x_1615_);
lean_dec_ref(v_arg_1614_);
lean_dec_ref(v_arg_1605_);
v___x_1677_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1677_, 0, v___x_1666_);
lean_ctor_set_uint8(v___x_1677_, 1, v___x_1666_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set(v___x_1670_, 0, v___x_1677_);
v___x_1679_ = v___x_1670_;
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
else
{
lean_object* v___x_1681_; 
lean_del_object(v___x_1670_);
v___x_1681_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_1445_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v___x_1683_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_a_1682_);
lean_dec_ref_known(v___x_1681_, 1);
lean_inc_ref(v_arg_1605_);
v___x_1683_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v___x_1615_, v_arg_1614_, v_arg_1605_, v_a_1682_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1694_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1686_ = v___x_1683_;
v_isShared_1687_ = v_isSharedCheck_1694_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1683_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1694_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1688_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__14, &l_Lean_Meta_Grind_NormSym_pushNot___closed__14_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__14);
v___x_1689_ = l_Lean_Expr_app___override(v___x_1688_, v_arg_1605_);
v___x_1690_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1690_, 0, v_a_1684_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
lean_ctor_set_uint8(v___x_1690_, sizeof(void*)*2, v___x_1666_);
lean_ctor_set_uint8(v___x_1690_, sizeof(void*)*2 + 1, v___x_1666_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 0, v___x_1690_);
v___x_1692_ = v___x_1686_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
else
{
lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1702_; 
lean_dec_ref(v_arg_1605_);
v_a_1695_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1697_ = v___x_1683_;
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1683_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1702_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
lean_dec_ref(v___x_1615_);
lean_dec_ref(v_arg_1614_);
lean_dec_ref(v_arg_1605_);
v_a_1703_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1681_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1681_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
else
{
lean_object* v___x_1711_; 
lean_dec_ref(v___x_1672_);
lean_del_object(v___x_1670_);
v___x_1711_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_1445_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1713_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_a_1712_);
lean_dec_ref_known(v___x_1711_, 1);
lean_inc_ref(v_arg_1605_);
v___x_1713_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v___x_1615_, v_arg_1614_, v_arg_1605_, v_a_1712_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1724_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1716_ = v___x_1713_;
v_isShared_1717_ = v_isSharedCheck_1724_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1713_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1724_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1718_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__17, &l_Lean_Meta_Grind_NormSym_pushNot___closed__17_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__17);
v___x_1719_ = l_Lean_Expr_app___override(v___x_1718_, v_arg_1605_);
v___x_1720_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1720_, 0, v_a_1714_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
lean_ctor_set_uint8(v___x_1720_, sizeof(void*)*2, v___x_1666_);
lean_ctor_set_uint8(v___x_1720_, sizeof(void*)*2 + 1, v___x_1666_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v___x_1720_);
v___x_1722_ = v___x_1716_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
lean_dec_ref(v_arg_1605_);
v_a_1725_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1713_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1713_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec_ref(v___x_1615_);
lean_dec_ref(v_arg_1614_);
lean_dec_ref(v_arg_1605_);
v_a_1733_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1711_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1711_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec_ref(v___x_1615_);
lean_dec_ref(v_arg_1614_);
lean_dec_ref(v_arg_1605_);
v_a_1742_ = lean_ctor_get(v___x_1667_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1667_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1667_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
else
{
lean_object* v___x_1750_; 
lean_inc_ref(v_arg_1601_);
v___x_1750_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1601_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1752_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref_known(v___x_1750_, 1);
lean_inc_ref(v_arg_1605_);
v___x_1752_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v___x_1615_, v_arg_1614_, v_arg_1605_, v_a_1751_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1763_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1763_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1763_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1757_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__20, &l_Lean_Meta_Grind_NormSym_pushNot___closed__20_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__20);
v___x_1758_ = l_Lean_mkAppB(v___x_1757_, v_arg_1605_, v_arg_1601_);
v___x_1759_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1759_, 0, v_a_1753_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
lean_ctor_set_uint8(v___x_1759_, sizeof(void*)*2, v___x_1612_);
lean_ctor_set_uint8(v___x_1759_, sizeof(void*)*2 + 1, v___x_1612_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1759_);
v___x_1761_ = v___x_1755_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1601_);
v_a_1764_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1752_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1752_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_dec_ref(v___x_1615_);
lean_dec_ref(v_arg_1614_);
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1601_);
v_a_1772_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1750_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1750_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1780_; 
lean_dec_ref(v___x_1606_);
lean_dec_ref(v_arg_1526_);
lean_inc_ref(v_arg_1605_);
v___x_1780_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1605_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1782_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1781_);
lean_dec_ref_known(v___x_1780_, 1);
lean_inc_ref(v_arg_1601_);
v___x_1782_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1601_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1784_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1782_, 1);
v___x_1784_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_a_1781_, v_a_1783_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1795_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1787_ = v___x_1784_;
v_isShared_1788_ = v_isSharedCheck_1795_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1784_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1795_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
v___x_1789_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__23, &l_Lean_Meta_Grind_NormSym_pushNot___closed__23_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__23);
v___x_1790_ = l_Lean_mkAppB(v___x_1789_, v_arg_1605_, v_arg_1601_);
v___x_1791_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1791_, 0, v_a_1785_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*2, v___x_1610_);
lean_ctor_set_uint8(v___x_1791_, sizeof(void*)*2 + 1, v___x_1610_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 0, v___x_1791_);
v___x_1793_ = v___x_1787_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1601_);
v_a_1796_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1784_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1784_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
lean_dec(v_a_1781_);
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1601_);
v_a_1804_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1782_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1782_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1601_);
v_a_1812_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1780_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1780_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
}
else
{
lean_object* v___x_1820_; 
lean_dec_ref(v___x_1606_);
lean_dec_ref(v_arg_1526_);
lean_inc_ref(v_arg_1605_);
v___x_1820_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1605_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1822_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_a_1821_);
lean_dec_ref_known(v___x_1820_, 1);
lean_inc_ref(v_arg_1601_);
v___x_1822_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1601_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1824_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
lean_dec_ref_known(v___x_1822_, 1);
v___x_1824_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v_a_1821_, v_a_1823_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1835_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1827_ = v___x_1824_;
v_isShared_1828_ = v_isSharedCheck_1835_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1835_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1829_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__26, &l_Lean_Meta_Grind_NormSym_pushNot___closed__26_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__26);
v___x_1830_ = l_Lean_mkAppB(v___x_1829_, v_arg_1605_, v_arg_1601_);
v___x_1831_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1831_, 0, v_a_1825_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*2, v___x_1608_);
lean_ctor_set_uint8(v___x_1831_, sizeof(void*)*2 + 1, v___x_1608_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1831_);
v___x_1833_ = v___x_1827_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1601_);
v_a_1836_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1824_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1824_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
else
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1851_; 
lean_dec(v_a_1821_);
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1601_);
v_a_1844_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1846_ = v___x_1822_;
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1822_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1851_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1849_; 
if (v_isShared_1847_ == 0)
{
v___x_1849_ = v___x_1846_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_a_1844_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1601_);
v_a_1852_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1820_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1820_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
else
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
lean_dec_ref(v___x_1606_);
lean_dec_ref(v_arg_1526_);
v___x_1860_ = lean_unsigned_to_nat(0u);
v___x_1861_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(v___x_1860_, v_a_1446_);
if (lean_obj_tag(v___x_1861_) == 0)
{
lean_object* v_a_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v_a_1862_ = lean_ctor_get(v___x_1861_, 0);
lean_inc(v_a_1862_);
lean_dec_ref_known(v___x_1861_, 1);
v___x_1863_ = lean_unsigned_to_nat(1u);
v___x_1864_ = lean_mk_empty_array_with_capacity(v___x_1863_);
v___x_1865_ = lean_array_push(v___x_1864_, v_a_1862_);
lean_inc_ref(v_arg_1601_);
v___x_1866_ = l_Lean_Meta_Sym_betaS(v_arg_1601_, v___x_1865_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1868_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_a_1867_);
lean_dec_ref_known(v___x_1866_, 1);
v___x_1868_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_a_1867_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; lean_object* v___x_1872_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref_known(v___x_1868_, 1);
v___x_1870_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__28));
v___x_1871_ = 0;
lean_inc_ref(v_arg_1605_);
v___x_1872_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v___x_1870_, v___x_1871_, v_arg_1605_, v_a_1869_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1874_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1872_, 1);
lean_inc_ref(v_arg_1605_);
v___x_1874_ = l_Lean_Meta_Sym_getLevel___redArg(v_arg_1605_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1888_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1877_ = v___x_1874_;
v_isShared_1878_ = v_isSharedCheck_1888_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1888_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1886_; 
v___x_1879_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__30));
v___x_1880_ = lean_box(0);
v___x_1881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1881_, 0, v_a_1875_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
v___x_1882_ = l_Lean_mkConst(v___x_1879_, v___x_1881_);
v___x_1883_ = l_Lean_mkAppB(v___x_1882_, v_arg_1605_, v_arg_1601_);
v___x_1884_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1884_, 0, v_a_1873_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
lean_ctor_set_uint8(v___x_1884_, sizeof(void*)*2, v___x_1603_);
lean_ctor_set_uint8(v___x_1884_, sizeof(void*)*2 + 1, v___x_1603_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1884_);
v___x_1886_ = v___x_1877_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
lean_dec(v_a_1873_);
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1601_);
v_a_1889_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1874_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1874_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1601_);
v_a_1897_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1872_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1872_);
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
else
{
lean_object* v_a_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1912_; 
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1601_);
v_a_1905_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1907_ = v___x_1868_;
v_isShared_1908_ = v_isSharedCheck_1912_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_a_1905_);
lean_dec(v___x_1868_);
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
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1601_);
v_a_1913_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1866_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1866_);
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
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec_ref(v_arg_1605_);
lean_dec_ref(v_arg_1601_);
v_a_1921_ = lean_ctor_get(v___x_1861_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1861_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1861_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1861_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
}
else
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1933_; 
lean_dec_ref(v___x_1602_);
lean_dec_ref(v_arg_1526_);
v___x_1929_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__33, &l_Lean_Meta_Grind_NormSym_pushNot___closed__33_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__33);
lean_inc_ref(v_arg_1601_);
v___x_1930_ = l_Lean_Expr_app___override(v___x_1929_, v_arg_1601_);
v___x_1931_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1931_, 0, v_arg_1601_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
lean_ctor_set_uint8(v___x_1931_, sizeof(void*)*2, v___x_1599_);
lean_ctor_set_uint8(v___x_1931_, sizeof(void*)*2 + 1, v___x_1599_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v___x_1931_);
v___x_1933_ = v___x_1593_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
else
{
lean_object* v___x_1935_; 
lean_dec_ref(v___x_1595_);
lean_del_object(v___x_1593_);
lean_dec_ref(v_arg_1526_);
v___x_1935_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_1445_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1945_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1945_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1945_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1943_; 
v___x_1940_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__36, &l_Lean_Meta_Grind_NormSym_pushNot___closed__36_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__36);
v___x_1941_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1941_, 0, v_a_1936_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
lean_ctor_set_uint8(v___x_1941_, sizeof(void*)*2, v___x_1597_);
lean_ctor_set_uint8(v___x_1941_, sizeof(void*)*2 + 1, v___x_1597_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1941_);
v___x_1943_ = v___x_1938_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1941_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
v_a_1946_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1935_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1935_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
else
{
lean_object* v___x_1954_; 
lean_dec_ref(v___x_1595_);
lean_del_object(v___x_1593_);
lean_dec_ref(v_arg_1526_);
v___x_1954_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_1445_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1965_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1957_ = v___x_1954_;
v_isShared_1958_ = v_isSharedCheck_1965_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1954_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1965_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; uint8_t v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1963_; 
v___x_1959_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__39, &l_Lean_Meta_Grind_NormSym_pushNot___closed__39_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__39);
v___x_1960_ = 0;
v___x_1961_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1961_, 0, v_a_1955_);
lean_ctor_set(v___x_1961_, 1, v___x_1959_);
lean_ctor_set_uint8(v___x_1961_, sizeof(void*)*2, v___x_1960_);
lean_ctor_set_uint8(v___x_1961_, sizeof(void*)*2 + 1, v___x_1960_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v___x_1961_);
v___x_1963_ = v___x_1957_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
v_a_1966_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1954_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1954_);
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
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_dec_ref(v_arg_1526_);
v_a_1975_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1590_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1590_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
v___jp_1527_:
{
if (lean_obj_tag(v_arg_1526_) == 7)
{
lean_object* v_binderName_1537_; lean_object* v_binderType_1538_; lean_object* v_body_1539_; uint8_t v_binderInfo_1540_; lean_object* v___x_1541_; 
v_binderName_1537_ = lean_ctor_get(v_arg_1526_, 0);
lean_inc(v_binderName_1537_);
v_binderType_1538_ = lean_ctor_get(v_arg_1526_, 1);
lean_inc_ref_n(v_binderType_1538_, 2);
v_body_1539_ = lean_ctor_get(v_arg_1526_, 2);
lean_inc_ref(v_body_1539_);
v_binderInfo_1540_ = lean_ctor_get_uint8(v_arg_1526_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_arg_1526_, 3);
v___x_1541_ = l_Lean_Meta_isProp(v_binderType_1538_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; uint8_t v___x_1543_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v___x_1541_, 1);
v___x_1543_ = l_Lean_Expr_hasLooseBVars(v_body_1539_);
if (v___x_1543_ == 0)
{
uint8_t v___x_1544_; 
v___x_1544_ = lean_unbox(v_a_1542_);
if (v___x_1544_ == 0)
{
uint8_t v___x_1545_; 
v___x_1545_ = lean_unbox(v_a_1542_);
lean_dec(v_a_1542_);
v___y_1453_ = v___y_1532_;
v___y_1454_ = v___y_1531_;
v___y_1455_ = v___y_1530_;
v___y_1456_ = v_binderName_1537_;
v___y_1457_ = v_binderInfo_1540_;
v___y_1458_ = v___y_1529_;
v___y_1459_ = v_body_1539_;
v___y_1460_ = v___y_1528_;
v___y_1461_ = v___y_1533_;
v___y_1462_ = v___y_1535_;
v___y_1463_ = v___y_1534_;
v___y_1464_ = v___y_1536_;
v___y_1465_ = v_binderType_1538_;
v___y_1466_ = v___x_1545_;
goto v___jp_1452_;
}
else
{
lean_object* v___x_1546_; 
lean_dec(v_a_1542_);
lean_dec(v_binderName_1537_);
lean_inc_ref(v_body_1539_);
v___x_1546_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_body_1539_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1548_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1546_, 1);
lean_inc_ref(v_binderType_1538_);
v___x_1548_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v_binderType_1538_, v_a_1547_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1559_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1551_ = v___x_1548_;
v_isShared_1552_ = v_isSharedCheck_1559_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1548_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1559_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1557_; 
v___x_1553_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__4, &l_Lean_Meta_Grind_NormSym_pushNot___closed__4_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__4);
v___x_1554_ = l_Lean_mkAppB(v___x_1553_, v_binderType_1538_, v_body_1539_);
v___x_1555_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1555_, 0, v_a_1549_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
lean_ctor_set_uint8(v___x_1555_, sizeof(void*)*2, v___x_1543_);
lean_ctor_set_uint8(v___x_1555_, sizeof(void*)*2 + 1, v___x_1543_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1555_);
v___x_1557_ = v___x_1551_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec_ref(v_body_1539_);
lean_dec_ref(v_binderType_1538_);
v_a_1560_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1548_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1548_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_dec_ref(v_body_1539_);
lean_dec_ref(v_binderType_1538_);
v_a_1568_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1546_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1546_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
else
{
uint8_t v___x_1576_; 
lean_dec(v_a_1542_);
v___x_1576_ = 0;
v___y_1453_ = v___y_1532_;
v___y_1454_ = v___y_1531_;
v___y_1455_ = v___y_1530_;
v___y_1456_ = v_binderName_1537_;
v___y_1457_ = v_binderInfo_1540_;
v___y_1458_ = v___y_1529_;
v___y_1459_ = v_body_1539_;
v___y_1460_ = v___y_1528_;
v___y_1461_ = v___y_1533_;
v___y_1462_ = v___y_1535_;
v___y_1463_ = v___y_1534_;
v___y_1464_ = v___y_1536_;
v___y_1465_ = v_binderType_1538_;
v___y_1466_ = v___x_1576_;
goto v___jp_1452_;
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref(v_body_1539_);
lean_dec_ref(v_binderType_1538_);
lean_dec(v_binderName_1537_);
v_a_1577_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1541_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1541_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
lean_dec_ref(v_arg_1526_);
v___x_1585_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
return v___x_1586_;
}
}
}
v___jp_1452_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_inc_ref(v___y_1459_);
lean_inc_ref(v___y_1465_);
lean_inc(v___y_1456_);
v___x_1467_ = l_Lean_mkLambda(v___y_1456_, v___y_1457_, v___y_1465_, v___y_1459_);
v___x_1468_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v___y_1459_, v___y_1460_, v___y_1458_, v___y_1455_, v___y_1454_, v___y_1453_, v___y_1461_, v___y_1463_, v___y_1462_, v___y_1464_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1470_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref_known(v___x_1468_, 1);
lean_inc_ref(v___y_1465_);
v___x_1470_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v___y_1456_, v___y_1457_, v___y_1465_, v_a_1469_, v___y_1454_, v___y_1453_, v___y_1461_, v___y_1463_, v___y_1462_, v___y_1464_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1472_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
lean_inc_ref(v___y_1465_);
v___x_1472_ = l_Lean_Meta_Sym_getLevel___redArg(v___y_1465_, v___y_1453_, v___y_1461_, v___y_1463_, v___y_1462_, v___y_1464_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1474_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc_n(v_a_1473_, 2);
lean_dec_ref_known(v___x_1472_, 1);
lean_inc_ref(v___y_1465_);
v___x_1474_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg(v_a_1473_, v___y_1465_, v_a_1471_, v___y_1454_, v___y_1453_, v___y_1461_, v___y_1463_, v___y_1462_, v___y_1464_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1488_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1477_ = v___x_1474_;
v_isShared_1478_ = v_isSharedCheck_1488_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1488_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
v___x_1479_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__1));
v___x_1480_ = lean_box(0);
v___x_1481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1481_, 0, v_a_1473_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
v___x_1482_ = l_Lean_mkConst(v___x_1479_, v___x_1481_);
v___x_1483_ = l_Lean_mkAppB(v___x_1482_, v___y_1465_, v___x_1467_);
v___x_1484_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1484_, 0, v_a_1475_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
lean_ctor_set_uint8(v___x_1484_, sizeof(void*)*2, v___y_1466_);
lean_ctor_set_uint8(v___x_1484_, sizeof(void*)*2 + 1, v___y_1466_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1484_);
v___x_1486_ = v___x_1477_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec(v_a_1473_);
lean_dec_ref(v___x_1467_);
lean_dec_ref(v___y_1465_);
v_a_1489_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1474_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1474_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_dec(v_a_1471_);
lean_dec_ref(v___x_1467_);
lean_dec_ref(v___y_1465_);
v_a_1497_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1472_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1472_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec_ref(v___x_1467_);
lean_dec_ref(v___y_1465_);
v_a_1505_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1470_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1470_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec_ref(v___x_1467_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1456_);
v_a_1513_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1468_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1468_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
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
v___jp_1521_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
return v___x_1523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_pushNot___boxed(lean_object* v_e_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lean_Meta_Grind_NormSym_pushNot(v_e_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
lean_dec(v_a_1992_);
lean_dec_ref(v_a_1991_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
lean_dec(v_a_1988_);
lean_dec_ref(v_a_1987_);
lean_dec(v_a_1986_);
lean_dec_ref(v_a_1985_);
lean_dec(v_a_1984_);
return v_res_1994_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2(void){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2000_ = lean_box(0);
v___x_2001_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__1));
v___x_2002_ = l_Lean_mkConst(v___x_2001_, v___x_2000_);
return v___x_2002_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5(void){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2008_ = lean_box(0);
v___x_2009_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__4));
v___x_2010_ = l_Lean_mkConst(v___x_2009_, v___x_2008_);
return v___x_2010_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8(void){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2014_ = lean_box(0);
v___x_2015_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__7));
v___x_2016_ = l_Lean_mkConst(v___x_2015_, v___x_2014_);
return v___x_2016_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11(void){
_start:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2020_ = lean_box(0);
v___x_2021_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__10));
v___x_2022_ = l_Lean_mkConst(v___x_2021_, v___x_2020_);
return v___x_2022_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2028_ = lean_box(0);
v___x_2029_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__13));
v___x_2030_ = l_Lean_mkConst(v___x_2029_, v___x_2028_);
return v___x_2030_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2034_ = lean_box(0);
v___x_2035_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__16));
v___x_2036_ = l_Lean_mkConst(v___x_2035_, v___x_2034_);
return v___x_2036_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20(void){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2040_ = lean_box(0);
v___x_2041_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__19));
v___x_2042_ = l_Lean_mkConst(v___x_2041_, v___x_2040_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg(lean_object* v_e_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v___x_2057_; uint8_t v___x_2058_; 
v___x_2057_ = l_Lean_Expr_cleanupAnnotations(v_e_2043_);
v___x_2058_ = l_Lean_Expr_isApp(v___x_2057_);
if (v___x_2058_ == 0)
{
lean_dec_ref(v___x_2057_);
goto v___jp_2054_;
}
else
{
lean_object* v_arg_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v_arg_2059_ = lean_ctor_get(v___x_2057_, 1);
lean_inc_ref(v_arg_2059_);
v___x_2060_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2057_);
v___x_2061_ = l_Lean_Expr_isApp(v___x_2060_);
if (v___x_2061_ == 0)
{
lean_dec_ref(v___x_2060_);
lean_dec_ref(v_arg_2059_);
goto v___jp_2054_;
}
else
{
lean_object* v_arg_2062_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___x_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; 
v_arg_2062_ = lean_ctor_get(v___x_2060_, 1);
lean_inc_ref(v_arg_2062_);
v___x_2181_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2060_);
v___x_2182_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1));
v___x_2183_ = l_Lean_Expr_isConstOf(v___x_2181_, v___x_2182_);
lean_dec_ref(v___x_2181_);
if (v___x_2183_ == 0)
{
lean_dec_ref(v_arg_2062_);
lean_dec_ref(v_arg_2059_);
goto v___jp_2054_;
}
else
{
lean_object* v___x_2184_; 
lean_inc_ref(v_arg_2062_);
v___x_2184_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_2062_, v_a_2047_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2244_; 
v_a_2185_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2187_ = v___x_2184_;
v_isShared_2188_ = v_isSharedCheck_2244_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2184_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2244_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; 
v___x_2189_ = l_Lean_Expr_cleanupAnnotations(v_a_2185_);
v___x_2190_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__6));
v___x_2191_ = l_Lean_Expr_isConstOf(v___x_2189_, v___x_2190_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2192_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_2193_ = l_Lean_Expr_isConstOf(v___x_2189_, v___x_2192_);
if (v___x_2193_ == 0)
{
uint8_t v___x_2194_; 
lean_del_object(v___x_2187_);
v___x_2194_ = l_Lean_Expr_isApp(v___x_2189_);
if (v___x_2194_ == 0)
{
lean_dec_ref(v___x_2189_);
v___y_2064_ = v_a_2044_;
v___y_2065_ = v_a_2045_;
v___y_2066_ = v_a_2046_;
v___y_2067_ = v_a_2047_;
v___y_2068_ = v_a_2048_;
v___y_2069_ = v_a_2049_;
goto v___jp_2063_;
}
else
{
lean_object* v_arg_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v_arg_2195_ = lean_ctor_get(v___x_2189_, 1);
lean_inc_ref(v_arg_2195_);
v___x_2196_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2189_);
v___x_2197_ = l_Lean_Expr_isApp(v___x_2196_);
if (v___x_2197_ == 0)
{
lean_dec_ref(v___x_2196_);
lean_dec_ref(v_arg_2195_);
v___y_2064_ = v_a_2044_;
v___y_2065_ = v_a_2045_;
v___y_2066_ = v_a_2046_;
v___y_2067_ = v_a_2047_;
v___y_2068_ = v_a_2048_;
v___y_2069_ = v_a_2049_;
goto v___jp_2063_;
}
else
{
lean_object* v_arg_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
v_arg_2198_ = lean_ctor_get(v___x_2196_, 1);
lean_inc_ref(v_arg_2198_);
v___x_2199_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2196_);
v___x_2200_ = l_Lean_Expr_isConstOf(v___x_2199_, v___x_2182_);
lean_dec_ref(v___x_2199_);
if (v___x_2200_ == 0)
{
lean_dec_ref(v_arg_2198_);
lean_dec_ref(v_arg_2195_);
v___y_2064_ = v_a_2044_;
v___y_2065_ = v_a_2045_;
v___y_2066_ = v_a_2046_;
v___y_2067_ = v_a_2047_;
v___y_2068_ = v_a_2048_;
v___y_2069_ = v_a_2049_;
goto v___jp_2063_;
}
else
{
lean_object* v___x_2201_; 
lean_dec_ref(v_arg_2062_);
lean_inc_ref(v_arg_2059_);
lean_inc_ref(v_arg_2195_);
v___x_2201_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_arg_2195_, v_arg_2059_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2203_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2201_, 1);
lean_inc_ref(v_arg_2198_);
v___x_2203_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_arg_2198_, v_a_2202_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2214_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2214_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2214_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2208_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14);
v___x_2209_ = l_Lean_mkApp3(v___x_2208_, v_arg_2198_, v_arg_2195_, v_arg_2059_);
v___x_2210_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2210_, 0, v_a_2204_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
lean_ctor_set_uint8(v___x_2210_, sizeof(void*)*2, v___x_2193_);
lean_ctor_set_uint8(v___x_2210_, sizeof(void*)*2 + 1, v___x_2193_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2210_);
v___x_2212_ = v___x_2206_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec_ref(v_arg_2198_);
lean_dec_ref(v_arg_2195_);
lean_dec_ref(v_arg_2059_);
v_a_2215_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2203_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2203_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec_ref(v_arg_2198_);
lean_dec_ref(v_arg_2195_);
lean_dec_ref(v_arg_2059_);
v_a_2223_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2201_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2201_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2235_; 
lean_dec_ref(v___x_2189_);
v___x_2231_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17);
v___x_2232_ = l_Lean_Expr_app___override(v___x_2231_, v_arg_2059_);
v___x_2233_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2233_, 0, v_arg_2062_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
lean_ctor_set_uint8(v___x_2233_, sizeof(void*)*2, v___x_2191_);
lean_ctor_set_uint8(v___x_2233_, sizeof(void*)*2 + 1, v___x_2191_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v___x_2233_);
v___x_2235_ = v___x_2187_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
else
{
lean_object* v___x_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2242_; 
lean_dec_ref(v___x_2189_);
lean_dec_ref(v_arg_2062_);
v___x_2237_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20);
lean_inc_ref(v_arg_2059_);
v___x_2238_ = l_Lean_Expr_app___override(v___x_2237_, v_arg_2059_);
v___x_2239_ = 0;
v___x_2240_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2240_, 0, v_arg_2059_);
lean_ctor_set(v___x_2240_, 1, v___x_2238_);
lean_ctor_set_uint8(v___x_2240_, sizeof(void*)*2, v___x_2239_);
lean_ctor_set_uint8(v___x_2240_, sizeof(void*)*2 + 1, v___x_2239_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v___x_2240_);
v___x_2242_ = v___x_2187_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_dec_ref(v_arg_2062_);
lean_dec_ref(v_arg_2059_);
v_a_2245_ = lean_ctor_get(v___x_2184_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2184_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2184_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
v___jp_2063_:
{
lean_object* v___x_2070_; 
lean_inc_ref(v_arg_2059_);
v___x_2070_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_2059_, v___y_2067_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2172_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2073_ = v___x_2070_;
v_isShared_2074_ = v_isSharedCheck_2172_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2070_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2172_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2075_ = l_Lean_Expr_cleanupAnnotations(v_a_2071_);
v___x_2076_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__6));
v___x_2077_ = l_Lean_Expr_isConstOf(v___x_2075_, v___x_2076_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2078_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_2079_ = l_Lean_Expr_isConstOf(v___x_2075_, v___x_2078_);
if (v___x_2079_ == 0)
{
uint8_t v___x_2080_; 
lean_dec_ref(v_arg_2059_);
v___x_2080_ = l_Lean_Expr_isApp(v___x_2075_);
if (v___x_2080_ == 0)
{
lean_dec_ref(v___x_2075_);
lean_del_object(v___x_2073_);
lean_dec_ref(v_arg_2062_);
goto v___jp_2051_;
}
else
{
lean_object* v_arg_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
v_arg_2081_ = lean_ctor_get(v___x_2075_, 1);
lean_inc_ref(v_arg_2081_);
v___x_2082_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2075_);
v___x_2083_ = l_Lean_Expr_isApp(v___x_2082_);
if (v___x_2083_ == 0)
{
lean_dec_ref(v___x_2082_);
lean_dec_ref(v_arg_2081_);
lean_del_object(v___x_2073_);
lean_dec_ref(v_arg_2062_);
goto v___jp_2051_;
}
else
{
lean_object* v_arg_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
v_arg_2084_ = lean_ctor_get(v___x_2082_, 1);
lean_inc_ref(v_arg_2084_);
v___x_2085_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2082_);
v___x_2086_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1));
v___x_2087_ = l_Lean_Expr_isConstOf(v___x_2085_, v___x_2086_);
lean_dec_ref(v___x_2085_);
if (v___x_2087_ == 0)
{
lean_dec_ref(v_arg_2084_);
lean_dec_ref(v_arg_2081_);
lean_del_object(v___x_2073_);
lean_dec_ref(v_arg_2062_);
goto v___jp_2051_;
}
else
{
uint8_t v___x_2088_; 
v___x_2088_ = l_Lean_Expr_isForall(v_arg_2062_);
if (v___x_2088_ == 0)
{
uint8_t v___x_2089_; 
v___x_2089_ = l_Lean_Expr_isForall(v_arg_2084_);
if (v___x_2089_ == 0)
{
uint8_t v___x_2090_; 
v___x_2090_ = l_Lean_Expr_isForall(v_arg_2081_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; lean_object* v___x_2093_; 
lean_dec_ref(v_arg_2084_);
lean_dec_ref(v_arg_2081_);
lean_dec_ref(v_arg_2062_);
v___x_2091_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2091_, 0, v___x_2090_);
lean_ctor_set_uint8(v___x_2091_, 1, v___x_2090_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2091_);
v___x_2093_ = v___x_2073_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v___x_2091_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
else
{
lean_object* v___x_2095_; 
lean_del_object(v___x_2073_);
lean_inc_ref(v_arg_2062_);
lean_inc_ref(v_arg_2084_);
v___x_2095_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_arg_2084_, v_arg_2062_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2097_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
lean_inc_ref(v_arg_2081_);
v___x_2097_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_arg_2081_, v_a_2096_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2108_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2100_ = v___x_2097_;
v_isShared_2101_ = v_isSharedCheck_2108_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2097_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2108_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2102_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2);
v___x_2103_ = l_Lean_mkApp3(v___x_2102_, v_arg_2062_, v_arg_2084_, v_arg_2081_);
v___x_2104_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2104_, 0, v_a_2098_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
lean_ctor_set_uint8(v___x_2104_, sizeof(void*)*2, v___x_2089_);
lean_ctor_set_uint8(v___x_2104_, sizeof(void*)*2 + 1, v___x_2089_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 0, v___x_2104_);
v___x_2106_ = v___x_2100_;
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
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec_ref(v_arg_2084_);
lean_dec_ref(v_arg_2081_);
lean_dec_ref(v_arg_2062_);
v_a_2109_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2097_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2097_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec_ref(v_arg_2084_);
lean_dec_ref(v_arg_2081_);
lean_dec_ref(v_arg_2062_);
v_a_2117_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2095_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2095_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
else
{
lean_object* v___x_2125_; 
lean_del_object(v___x_2073_);
lean_inc_ref(v_arg_2081_);
lean_inc_ref(v_arg_2062_);
v___x_2125_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_arg_2062_, v_arg_2081_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___x_2127_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
lean_inc_ref(v_arg_2084_);
v___x_2127_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_arg_2084_, v_a_2126_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2138_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2130_ = v___x_2127_;
v_isShared_2131_ = v_isSharedCheck_2138_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2127_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2138_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2136_; 
v___x_2132_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5);
v___x_2133_ = l_Lean_mkApp3(v___x_2132_, v_arg_2062_, v_arg_2084_, v_arg_2081_);
v___x_2134_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2134_, 0, v_a_2128_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
lean_ctor_set_uint8(v___x_2134_, sizeof(void*)*2, v___x_2088_);
lean_ctor_set_uint8(v___x_2134_, sizeof(void*)*2 + 1, v___x_2088_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 0, v___x_2134_);
v___x_2136_ = v___x_2130_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_dec_ref(v_arg_2084_);
lean_dec_ref(v_arg_2081_);
lean_dec_ref(v_arg_2062_);
v_a_2139_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2127_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2127_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
lean_dec_ref(v_arg_2084_);
lean_dec_ref(v_arg_2081_);
lean_dec_ref(v_arg_2062_);
v_a_2147_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2125_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2125_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2157_; 
lean_dec_ref(v_arg_2084_);
lean_dec_ref(v_arg_2081_);
lean_dec_ref(v_arg_2062_);
v___x_2155_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2155_, 0, v___x_2079_);
lean_ctor_set_uint8(v___x_2155_, 1, v___x_2079_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2155_);
v___x_2157_ = v___x_2073_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
}
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2163_; 
lean_dec_ref(v___x_2075_);
v___x_2159_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8);
v___x_2160_ = l_Lean_Expr_app___override(v___x_2159_, v_arg_2062_);
v___x_2161_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2161_, 0, v_arg_2059_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
lean_ctor_set_uint8(v___x_2161_, sizeof(void*)*2, v___x_2077_);
lean_ctor_set_uint8(v___x_2161_, sizeof(void*)*2 + 1, v___x_2077_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2161_);
v___x_2163_ = v___x_2073_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2170_; 
lean_dec_ref(v___x_2075_);
lean_dec_ref(v_arg_2059_);
v___x_2165_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11);
lean_inc_ref(v_arg_2062_);
v___x_2166_ = l_Lean_Expr_app___override(v___x_2165_, v_arg_2062_);
v___x_2167_ = 0;
v___x_2168_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2168_, 0, v_arg_2062_);
lean_ctor_set(v___x_2168_, 1, v___x_2166_);
lean_ctor_set_uint8(v___x_2168_, sizeof(void*)*2, v___x_2167_);
lean_ctor_set_uint8(v___x_2168_, sizeof(void*)*2 + 1, v___x_2167_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2168_);
v___x_2170_ = v___x_2073_;
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
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec_ref(v_arg_2062_);
lean_dec_ref(v_arg_2059_);
v_a_2173_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2070_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2070_);
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
}
}
v___jp_2051_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
return v___x_2053_;
}
v___jp_2054_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
return v___x_2056_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___boxed(lean_object* v_e_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_Meta_Grind_NormSym_simpOr___redArg(v_e_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_);
lean_dec(v_a_2259_);
lean_dec_ref(v_a_2258_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2254_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr(lean_object* v_e_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_Meta_Grind_NormSym_simpOr___redArg(v_e_2262_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr___boxed(lean_object* v_e_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v_res_2285_; 
v_res_2285_ = l_Lean_Meta_Grind_NormSym_simpOr(v_e_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec(v_a_2283_);
lean_dec_ref(v_a_2282_);
lean_dec(v_a_2281_);
lean_dec_ref(v_a_2280_);
lean_dec(v_a_2279_);
lean_dec_ref(v_a_2278_);
lean_dec(v_a_2277_);
lean_dec_ref(v_a_2276_);
lean_dec(v_a_2275_);
return v_res_2285_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2286_ = lean_box(0);
v___x_2287_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__6));
v___x_2288_ = l_Lean_mkConst(v___x_2287_, v___x_2286_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0(uint8_t v___x_2289_, uint8_t v___x_2290_, lean_object* v_h_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v___y_2303_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2312_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0, &l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0);
lean_inc_ref(v_h_2291_);
v___x_2313_ = l_Lean_Meta_mkNoConfusion(v___x_2312_, v_h_2291_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; lean_object* v___x_2319_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref_known(v___x_2313_, 1);
v___x_2315_ = lean_unsigned_to_nat(1u);
v___x_2316_ = lean_mk_empty_array_with_capacity(v___x_2315_);
v___x_2317_ = lean_array_push(v___x_2316_, v_h_2291_);
v___x_2318_ = 1;
v___x_2319_ = l_Lean_Meta_mkLambdaFVars(v___x_2317_, v_a_2314_, v___x_2289_, v___x_2290_, v___x_2289_, v___x_2290_, v___x_2318_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
lean_dec_ref(v___x_2317_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2321_; uint8_t v_transparency_2322_; uint8_t v___x_2323_; uint8_t v___x_2324_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2319_, 1);
v___x_2321_ = l_Lean_Meta_Context_config(v___y_2297_);
v_transparency_2322_ = lean_ctor_get_uint8(v___x_2321_, 9);
lean_dec_ref(v___x_2321_);
v___x_2323_ = 1;
v___x_2324_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2322_, v___x_2323_);
if (v___x_2324_ == 0)
{
lean_object* v_keyedConfig_2325_; uint8_t v_trackZetaDelta_2326_; lean_object* v_zetaDeltaSet_2327_; lean_object* v_lctx_2328_; lean_object* v_localInstances_2329_; lean_object* v_defEqCtx_x3f_2330_; lean_object* v_synthPendingDepth_2331_; lean_object* v_customCanUnfoldPredicate_x3f_2332_; uint8_t v_univApprox_2333_; uint8_t v_inTypeClassResolution_2334_; uint8_t v_cacheInferType_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v_keyedConfig_2325_ = lean_ctor_get(v___y_2297_, 0);
v_trackZetaDelta_2326_ = lean_ctor_get_uint8(v___y_2297_, sizeof(void*)*7);
v_zetaDeltaSet_2327_ = lean_ctor_get(v___y_2297_, 1);
v_lctx_2328_ = lean_ctor_get(v___y_2297_, 2);
v_localInstances_2329_ = lean_ctor_get(v___y_2297_, 3);
v_defEqCtx_x3f_2330_ = lean_ctor_get(v___y_2297_, 4);
v_synthPendingDepth_2331_ = lean_ctor_get(v___y_2297_, 5);
v_customCanUnfoldPredicate_x3f_2332_ = lean_ctor_get(v___y_2297_, 6);
v_univApprox_2333_ = lean_ctor_get_uint8(v___y_2297_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2334_ = lean_ctor_get_uint8(v___y_2297_, sizeof(void*)*7 + 2);
v_cacheInferType_2335_ = lean_ctor_get_uint8(v___y_2297_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2325_);
v___x_2336_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2323_, v_keyedConfig_2325_);
lean_inc(v_customCanUnfoldPredicate_x3f_2332_);
lean_inc(v_synthPendingDepth_2331_);
lean_inc(v_defEqCtx_x3f_2330_);
lean_inc_ref(v_localInstances_2329_);
lean_inc_ref(v_lctx_2328_);
lean_inc(v_zetaDeltaSet_2327_);
v___x_2337_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
lean_ctor_set(v___x_2337_, 1, v_zetaDeltaSet_2327_);
lean_ctor_set(v___x_2337_, 2, v_lctx_2328_);
lean_ctor_set(v___x_2337_, 3, v_localInstances_2329_);
lean_ctor_set(v___x_2337_, 4, v_defEqCtx_x3f_2330_);
lean_ctor_set(v___x_2337_, 5, v_synthPendingDepth_2331_);
lean_ctor_set(v___x_2337_, 6, v_customCanUnfoldPredicate_x3f_2332_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*7, v_trackZetaDelta_2326_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*7 + 1, v_univApprox_2333_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2334_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*7 + 3, v_cacheInferType_2335_);
v___x_2338_ = l_Lean_Meta_mkEqFalse_x27(v_a_2320_, v___x_2337_, v___y_2298_, v___y_2299_, v___y_2300_);
lean_dec_ref_known(v___x_2337_, 7);
v___y_2303_ = v___x_2338_;
goto v___jp_2302_;
}
else
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_Meta_mkEqFalse_x27(v_a_2320_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
v___y_2303_ = v___x_2339_;
goto v___jp_2302_;
}
}
else
{
return v___x_2319_;
}
}
else
{
lean_dec_ref(v_h_2291_);
return v___x_2313_;
}
v___jp_2302_:
{
if (lean_obj_tag(v___y_2303_) == 0)
{
return v___y_2303_;
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
v_a_2304_ = lean_ctor_get(v___y_2303_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___y_2303_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___y_2303_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___y_2303_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___boxed(lean_object* v___x_2340_, lean_object* v___x_2341_, lean_object* v_h_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
uint8_t v___x_16179__boxed_2353_; uint8_t v___x_16180__boxed_2354_; lean_object* v_res_2355_; 
v___x_16179__boxed_2353_ = lean_unbox(v___x_2340_);
v___x_16180__boxed_2354_ = lean_unbox(v___x_2341_);
v_res_2355_ = l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0(v___x_16179__boxed_2353_, v___x_16180__boxed_2354_, v_h_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0(lean_object* v_k_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v_b_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v___x_2368_; 
lean_inc(v___y_2366_);
lean_inc_ref(v___y_2365_);
lean_inc(v___y_2364_);
lean_inc_ref(v___y_2363_);
lean_inc(v___y_2361_);
lean_inc_ref(v___y_2360_);
lean_inc(v___y_2359_);
lean_inc_ref(v___y_2358_);
lean_inc(v___y_2357_);
v___x_2368_ = lean_apply_11(v_k_2356_, v_b_2362_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, lean_box(0));
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v_b_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0(v_k_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v_b_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(lean_object* v_name_2382_, uint8_t v_bi_2383_, lean_object* v_type_2384_, lean_object* v_k_2385_, uint8_t v_kind_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v___f_2397_; lean_object* v___x_2398_; 
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
lean_inc(v___y_2389_);
lean_inc_ref(v___y_2388_);
lean_inc(v___y_2387_);
v___f_2397_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_2397_, 0, v_k_2385_);
lean_closure_set(v___f_2397_, 1, v___y_2387_);
lean_closure_set(v___f_2397_, 2, v___y_2388_);
lean_closure_set(v___f_2397_, 3, v___y_2389_);
lean_closure_set(v___f_2397_, 4, v___y_2390_);
lean_closure_set(v___f_2397_, 5, v___y_2391_);
v___x_2398_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2382_, v_bi_2383_, v_type_2384_, v___f_2397_, v_kind_2386_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2398_) == 0)
{
return v___x_2398_;
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2398_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2398_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___boxed(lean_object* v_name_2407_, lean_object* v_bi_2408_, lean_object* v_type_2409_, lean_object* v_k_2410_, lean_object* v_kind_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
uint8_t v_bi_boxed_2422_; uint8_t v_kind_boxed_2423_; lean_object* v_res_2424_; 
v_bi_boxed_2422_ = lean_unbox(v_bi_2408_);
v_kind_boxed_2423_ = lean_unbox(v_kind_2411_);
v_res_2424_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(v_name_2407_, v_bi_boxed_2422_, v_type_2409_, v_k_2410_, v_kind_boxed_2423_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(lean_object* v_name_2425_, lean_object* v_type_2426_, lean_object* v_k_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
uint8_t v___x_2438_; uint8_t v___x_2439_; lean_object* v___x_2440_; 
v___x_2438_ = 0;
v___x_2439_ = 0;
v___x_2440_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(v_name_2425_, v___x_2438_, v_type_2426_, v_k_2427_, v___x_2439_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg___boxed(lean_object* v_name_2441_, lean_object* v_type_2442_, lean_object* v_k_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_name_2441_, v_type_2442_, v_k_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq(lean_object* v_e_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_){
_start:
{
lean_object* v___x_2472_; uint8_t v___x_2473_; 
lean_inc_ref(v_e_2458_);
v___x_2472_ = l_Lean_Expr_cleanupAnnotations(v_e_2458_);
v___x_2473_ = l_Lean_Expr_isApp(v___x_2472_);
if (v___x_2473_ == 0)
{
lean_dec_ref(v___x_2472_);
lean_dec_ref(v_e_2458_);
goto v___jp_2469_;
}
else
{
lean_object* v_arg_2474_; lean_object* v___x_2475_; uint8_t v___x_2476_; 
v_arg_2474_ = lean_ctor_get(v___x_2472_, 1);
lean_inc_ref(v_arg_2474_);
v___x_2475_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2472_);
v___x_2476_ = l_Lean_Expr_isApp(v___x_2475_);
if (v___x_2476_ == 0)
{
lean_dec_ref(v___x_2475_);
lean_dec_ref(v_arg_2474_);
lean_dec_ref(v_e_2458_);
goto v___jp_2469_;
}
else
{
lean_object* v_arg_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; 
v_arg_2477_ = lean_ctor_get(v___x_2475_, 1);
lean_inc_ref(v_arg_2477_);
v___x_2478_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2475_);
v___x_2479_ = l_Lean_Expr_isApp(v___x_2478_);
if (v___x_2479_ == 0)
{
lean_dec_ref(v___x_2478_);
lean_dec_ref(v_arg_2477_);
lean_dec_ref(v_arg_2474_);
lean_dec_ref(v_e_2458_);
goto v___jp_2469_;
}
else
{
lean_object* v___x_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; 
v___x_2480_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2478_);
v___x_2481_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__1));
v___x_2482_ = l_Lean_Expr_isConstOf(v___x_2480_, v___x_2481_);
lean_dec_ref(v___x_2480_);
if (v___x_2482_ == 0)
{
lean_dec_ref(v_arg_2477_);
lean_dec_ref(v_arg_2474_);
lean_dec_ref(v_e_2458_);
goto v___jp_2469_;
}
else
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Lean_Meta_isConstructorApp_x3f(v_arg_2477_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2553_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2486_ = v___x_2483_;
v_isShared_2487_ = v_isSharedCheck_2553_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2483_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2553_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
if (lean_obj_tag(v_a_2484_) == 1)
{
lean_object* v_val_2488_; lean_object* v___x_2489_; 
lean_del_object(v___x_2486_);
v_val_2488_ = lean_ctor_get(v_a_2484_, 0);
lean_inc(v_val_2488_);
lean_dec_ref_known(v_a_2484_, 1);
v___x_2489_ = l_Lean_Meta_isConstructorApp_x3f(v_arg_2474_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2540_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2492_ = v___x_2489_;
v_isShared_2493_ = v_isSharedCheck_2540_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2489_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2540_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
if (lean_obj_tag(v_a_2490_) == 1)
{
lean_object* v_toConstantVal_2494_; lean_object* v_val_2495_; lean_object* v_toConstantVal_2496_; lean_object* v_name_2497_; lean_object* v_name_2498_; uint8_t v___x_2499_; 
v_toConstantVal_2494_ = lean_ctor_get(v_val_2488_, 0);
lean_inc_ref(v_toConstantVal_2494_);
lean_dec(v_val_2488_);
v_val_2495_ = lean_ctor_get(v_a_2490_, 0);
lean_inc(v_val_2495_);
lean_dec_ref_known(v_a_2490_, 1);
v_toConstantVal_2496_ = lean_ctor_get(v_val_2495_, 0);
lean_inc_ref(v_toConstantVal_2496_);
lean_dec(v_val_2495_);
v_name_2497_ = lean_ctor_get(v_toConstantVal_2494_, 0);
lean_inc(v_name_2497_);
lean_dec_ref(v_toConstantVal_2494_);
v_name_2498_ = lean_ctor_get(v_toConstantVal_2496_, 0);
lean_inc(v_name_2498_);
lean_dec_ref(v_toConstantVal_2496_);
v___x_2499_ = lean_name_eq(v_name_2497_, v_name_2498_);
lean_dec(v_name_2498_);
lean_dec(v_name_2497_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___f_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
lean_del_object(v___x_2492_);
v___x_2500_ = lean_box(v___x_2499_);
v___x_2501_ = lean_box(v___x_2482_);
v___f_2502_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2502_, 0, v___x_2500_);
lean_closure_set(v___f_2502_, 1, v___x_2501_);
v___x_2503_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_reduceCtorEq___closed__1));
v___x_2504_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v___x_2503_, v_e_2458_, v___f_2502_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; lean_object* v___x_2506_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2504_, 1);
v___x_2506_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2462_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2515_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2509_ = v___x_2506_;
v_isShared_2510_ = v_isSharedCheck_2515_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2506_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2515_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2511_; lean_object* v___x_2513_; 
v___x_2511_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2511_, 0, v_a_2507_);
lean_ctor_set(v___x_2511_, 1, v_a_2505_);
lean_ctor_set_uint8(v___x_2511_, sizeof(void*)*2, v___x_2482_);
lean_ctor_set_uint8(v___x_2511_, sizeof(void*)*2 + 1, v___x_2499_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 0, v___x_2511_);
v___x_2513_ = v___x_2509_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2511_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec(v_a_2505_);
v_a_2516_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2506_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2506_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
v_a_2524_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2504_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2504_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
else
{
lean_object* v___x_2532_; lean_object* v___x_2534_; 
lean_dec_ref(v_e_2458_);
v___x_2532_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 0, v___x_2532_);
v___x_2534_ = v___x_2492_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v___x_2532_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
else
{
lean_object* v___x_2536_; lean_object* v___x_2538_; 
lean_dec(v_a_2490_);
lean_dec(v_val_2488_);
lean_dec_ref(v_e_2458_);
v___x_2536_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_2493_ == 0)
{
lean_ctor_set(v___x_2492_, 0, v___x_2536_);
v___x_2538_ = v___x_2492_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec(v_val_2488_);
lean_dec_ref(v_e_2458_);
v_a_2541_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2489_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2489_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
else
{
lean_object* v___x_2549_; lean_object* v___x_2551_; 
lean_dec(v_a_2484_);
lean_dec_ref(v_arg_2474_);
lean_dec_ref(v_e_2458_);
v___x_2549_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 0, v___x_2549_);
v___x_2551_ = v___x_2486_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2549_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
else
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2561_; 
lean_dec_ref(v_arg_2474_);
lean_dec_ref(v_e_2458_);
v_a_2554_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2556_ = v___x_2483_;
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___x_2483_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2561_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2559_; 
if (v_isShared_2557_ == 0)
{
v___x_2559_ = v___x_2556_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2554_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
}
}
}
}
v___jp_2469_:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
return v___x_2471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___boxed(lean_object* v_e_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_Meta_Grind_NormSym_reduceCtorEq(v_e_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
lean_dec(v_a_2565_);
lean_dec_ref(v_a_2564_);
lean_dec(v_a_2563_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0(lean_object* v_00_u03b1_2574_, lean_object* v_name_2575_, uint8_t v_bi_2576_, lean_object* v_type_2577_, lean_object* v_k_2578_, uint8_t v_kind_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(v_name_2575_, v_bi_2576_, v_type_2577_, v_k_2578_, v_kind_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2591_, lean_object* v_name_2592_, lean_object* v_bi_2593_, lean_object* v_type_2594_, lean_object* v_k_2595_, lean_object* v_kind_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
uint8_t v_bi_boxed_2607_; uint8_t v_kind_boxed_2608_; lean_object* v_res_2609_; 
v_bi_boxed_2607_ = lean_unbox(v_bi_2593_);
v_kind_boxed_2608_ = lean_unbox(v_kind_2596_);
v_res_2609_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0(v_00_u03b1_2591_, v_name_2592_, v_bi_boxed_2607_, v_type_2594_, v_k_2595_, v_kind_boxed_2608_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0(lean_object* v_00_u03b1_2610_, lean_object* v_name_2611_, lean_object* v_type_2612_, lean_object* v_k_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_name_2611_, v_type_2612_, v_k_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___boxed(lean_object* v_00_u03b1_2625_, lean_object* v_name_2626_, lean_object* v_type_2627_, lean_object* v_k_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0(v_00_u03b1_2625_, v_name_2626_, v_type_2627_, v_k_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(lean_object* v_e_2640_){
_start:
{
if (lean_obj_tag(v_e_2640_) == 7)
{
lean_object* v_binderName_2641_; lean_object* v_binderType_2642_; lean_object* v_body_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
v_binderName_2641_ = lean_ctor_get(v_e_2640_, 0);
v_binderType_2642_ = lean_ctor_get(v_e_2640_, 1);
v_body_2643_ = lean_ctor_get(v_e_2640_, 2);
lean_inc_ref(v_body_2643_);
lean_inc_ref(v_binderType_2642_);
v___x_2644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2644_, 0, v_binderType_2642_);
lean_ctor_set(v___x_2644_, 1, v_body_2643_);
lean_inc(v_binderName_2641_);
v___x_2645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2645_, 0, v_binderName_2641_);
lean_ctor_set(v___x_2645_, 1, v___x_2644_);
v___x_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
return v___x_2646_;
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v___x_2647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS___closed__1));
v___x_2648_ = lean_unsigned_to_nat(1u);
v___x_2649_ = l_Lean_Expr_isAppOfArity(v_e_2640_, v___x_2647_, v___x_2648_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; 
v___x_2650_ = lean_box(0);
return v___x_2650_;
}
else
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2651_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__28));
v___x_2652_ = l_Lean_Expr_appArg_x21(v_e_2640_);
v___x_2653_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0, &l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0);
v___x_2654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2652_);
lean_ctor_set(v___x_2654_, 1, v___x_2653_);
v___x_2655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2651_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
v___x_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
return v___x_2656_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f___boxed(lean_object* v_e_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(v_e_2657_);
lean_dec_ref(v_e_2657_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0(lean_object* v_fst_2659_, lean_object* v_a_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = lean_expr_instantiate1(v_fst_2659_, v_a_2660_);
v___x_2672_ = l_Lean_Meta_getLevel(v___x_2671_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0___boxed(lean_object* v_fst_2673_, lean_object* v_a_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0(v_fst_2673_, v_a_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v_a_2674_);
lean_dec_ref(v_fst_2673_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f(lean_object* v_e_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_){
_start:
{
if (lean_obj_tag(v_e_2696_) == 7)
{
lean_object* v_binderName_2710_; lean_object* v_binderType_2711_; lean_object* v_body_2712_; uint8_t v_binderInfo_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; 
v_binderName_2710_ = lean_ctor_get(v_e_2696_, 0);
lean_inc(v_binderName_2710_);
v_binderType_2711_ = lean_ctor_get(v_e_2696_, 1);
lean_inc_ref(v_binderType_2711_);
v_body_2712_ = lean_ctor_get(v_e_2696_, 2);
lean_inc_ref(v_body_2712_);
v_binderInfo_2713_ = lean_ctor_get_uint8(v_e_2696_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2696_, 3);
v___x_2714_ = l_Lean_Expr_cleanupAnnotations(v_body_2712_);
v___x_2715_ = l_Lean_Expr_isApp(v___x_2714_);
if (v___x_2715_ == 0)
{
lean_dec_ref(v___x_2714_);
lean_dec_ref(v_binderType_2711_);
lean_dec(v_binderName_2710_);
goto v___jp_2707_;
}
else
{
lean_object* v_arg_2716_; lean_object* v___x_2717_; uint8_t v___x_2718_; 
v_arg_2716_ = lean_ctor_get(v___x_2714_, 1);
lean_inc_ref(v_arg_2716_);
v___x_2717_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2714_);
v___x_2718_ = l_Lean_Expr_isApp(v___x_2717_);
if (v___x_2718_ == 0)
{
lean_dec_ref(v___x_2717_);
lean_dec_ref(v_arg_2716_);
lean_dec_ref(v_binderType_2711_);
lean_dec(v_binderName_2710_);
goto v___jp_2707_;
}
else
{
lean_object* v_arg_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; uint8_t v___x_2722_; 
v_arg_2719_ = lean_ctor_get(v___x_2717_, 1);
lean_inc_ref(v_arg_2719_);
v___x_2720_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2717_);
v___x_2721_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1));
v___x_2722_ = l_Lean_Expr_isConstOf(v___x_2720_, v___x_2721_);
lean_dec_ref(v___x_2720_);
if (v___x_2722_ == 0)
{
lean_dec_ref(v_arg_2719_);
lean_dec_ref(v_arg_2716_);
lean_dec_ref(v_binderType_2711_);
lean_dec(v_binderName_2710_);
goto v___jp_2707_;
}
else
{
lean_object* v___x_2723_; 
v___x_2723_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(v_arg_2719_);
if (lean_obj_tag(v___x_2723_) == 1)
{
lean_object* v_val_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2830_; 
lean_dec_ref(v_arg_2719_);
v_val_2724_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2726_ = v___x_2723_;
v_isShared_2727_ = v_isSharedCheck_2830_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_val_2724_);
lean_dec(v___x_2723_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2830_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v_snd_2728_; lean_object* v_fst_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2829_; 
v_snd_2728_ = lean_ctor_get(v_val_2724_, 1);
v_fst_2729_ = lean_ctor_get(v_val_2724_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v_val_2724_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2731_ = v_val_2724_;
v_isShared_2732_ = v_isSharedCheck_2829_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_snd_2728_);
lean_inc(v_fst_2729_);
lean_dec(v_val_2724_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2829_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v_fst_2733_; lean_object* v_snd_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2828_; 
v_fst_2733_ = lean_ctor_get(v_snd_2728_, 0);
v_snd_2734_ = lean_ctor_get(v_snd_2728_, 1);
v_isSharedCheck_2828_ = !lean_is_exclusive(v_snd_2728_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2736_ = v_snd_2728_;
v_isShared_2737_ = v_isSharedCheck_2828_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_snd_2734_);
lean_inc(v_fst_2733_);
lean_dec(v_snd_2728_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2828_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___f_2738_; lean_object* v_p_2739_; uint8_t v___x_2740_; lean_object* v___x_2741_; lean_object* v_q_2742_; lean_object* v_00_u03b2_2743_; lean_object* v___x_2744_; 
lean_inc_n(v_fst_2733_, 3);
v___f_2738_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2738_, 0, v_fst_2733_);
lean_inc_ref(v_arg_2716_);
lean_inc_ref_n(v_binderType_2711_, 4);
lean_inc_n(v_binderName_2710_, 3);
v_p_2739_ = l_Lean_mkLambda(v_binderName_2710_, v_binderInfo_2713_, v_binderType_2711_, v_arg_2716_);
v___x_2740_ = 0;
lean_inc(v_snd_2734_);
lean_inc(v_fst_2729_);
v___x_2741_ = l_Lean_mkLambda(v_fst_2729_, v___x_2740_, v_fst_2733_, v_snd_2734_);
v_q_2742_ = l_Lean_mkLambda(v_binderName_2710_, v_binderInfo_2713_, v_binderType_2711_, v___x_2741_);
v_00_u03b2_2743_ = l_Lean_mkLambda(v_binderName_2710_, v_binderInfo_2713_, v_binderType_2711_, v_fst_2733_);
v___x_2744_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2711_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2746_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref_known(v___x_2744_, 1);
lean_inc_ref(v_binderType_2711_);
lean_inc(v_binderName_2710_);
v___x_2746_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_binderName_2710_, v_binderType_2711_, v___f_2738_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref_known(v___x_2746_, 1);
v___x_2748_ = lean_unsigned_to_nat(0u);
v___x_2749_ = lean_unsigned_to_nat(1u);
v___x_2750_ = lean_expr_lift_loose_bvars(v_arg_2716_, v___x_2748_, v___x_2749_);
lean_dec_ref(v_arg_2716_);
v___x_2751_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2750_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; lean_object* v___x_2753_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc(v_a_2752_);
lean_dec_ref_known(v___x_2751_, 1);
v___x_2753_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_snd_2734_, v_a_2752_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; lean_object* v___x_2755_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc(v_a_2754_);
lean_dec_ref_known(v___x_2753_, 1);
v___x_2755_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_fst_2729_, v___x_2740_, v_fst_2733_, v_a_2754_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2757_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_a_2756_);
lean_dec_ref_known(v___x_2755_, 1);
lean_inc_ref(v_binderType_2711_);
v___x_2757_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_binderName_2710_, v_binderInfo_2713_, v_binderType_2711_, v_a_2756_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2779_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2760_ = v___x_2757_;
v_isShared_2761_ = v_isSharedCheck_2779_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2757_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2779_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2765_; 
v___x_2762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__1));
v___x_2763_ = lean_box(0);
if (v_isShared_2732_ == 0)
{
lean_ctor_set_tag(v___x_2731_, 1);
lean_ctor_set(v___x_2731_, 1, v___x_2763_);
lean_ctor_set(v___x_2731_, 0, v_a_2747_);
v___x_2765_ = v___x_2731_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2747_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v___x_2763_);
v___x_2765_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2770_; 
v___x_2766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2766_, 0, v_a_2745_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
v___x_2767_ = l_Lean_mkConst(v___x_2762_, v___x_2766_);
v___x_2768_ = l_Lean_mkApp4(v___x_2767_, v_binderType_2711_, v_00_u03b2_2743_, v_p_2739_, v_q_2742_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 1, v___x_2768_);
lean_ctor_set(v___x_2736_, 0, v_a_2758_);
v___x_2770_ = v___x_2736_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2758_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v___x_2768_);
v___x_2770_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v___x_2772_; 
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 0, v___x_2770_);
v___x_2772_ = v___x_2726_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_object* v___x_2774_; 
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2772_);
v___x_2774_ = v___x_2760_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
}
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_dec(v_a_2747_);
lean_dec(v_a_2745_);
lean_dec_ref(v_00_u03b2_2743_);
lean_dec_ref(v_q_2742_);
lean_dec_ref(v_p_2739_);
lean_del_object(v___x_2736_);
lean_del_object(v___x_2731_);
lean_del_object(v___x_2726_);
lean_dec_ref(v_binderType_2711_);
v_a_2780_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2757_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2757_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec(v_a_2747_);
lean_dec(v_a_2745_);
lean_dec_ref(v_00_u03b2_2743_);
lean_dec_ref(v_q_2742_);
lean_dec_ref(v_p_2739_);
lean_del_object(v___x_2736_);
lean_del_object(v___x_2731_);
lean_del_object(v___x_2726_);
lean_dec_ref(v_binderType_2711_);
lean_dec(v_binderName_2710_);
v_a_2788_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2755_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2755_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec(v_a_2747_);
lean_dec(v_a_2745_);
lean_dec_ref(v_00_u03b2_2743_);
lean_dec_ref(v_q_2742_);
lean_dec_ref(v_p_2739_);
lean_del_object(v___x_2736_);
lean_dec(v_fst_2733_);
lean_del_object(v___x_2731_);
lean_dec(v_fst_2729_);
lean_del_object(v___x_2726_);
lean_dec_ref(v_binderType_2711_);
lean_dec(v_binderName_2710_);
v_a_2796_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2753_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2753_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2801_; 
if (v_isShared_2799_ == 0)
{
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_dec(v_a_2747_);
lean_dec(v_a_2745_);
lean_dec_ref(v_00_u03b2_2743_);
lean_dec_ref(v_q_2742_);
lean_dec_ref(v_p_2739_);
lean_del_object(v___x_2736_);
lean_dec(v_snd_2734_);
lean_dec(v_fst_2733_);
lean_del_object(v___x_2731_);
lean_dec(v_fst_2729_);
lean_del_object(v___x_2726_);
lean_dec_ref(v_binderType_2711_);
lean_dec(v_binderName_2710_);
v_a_2804_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2751_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2751_);
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
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_dec(v_a_2745_);
lean_dec_ref(v_00_u03b2_2743_);
lean_dec_ref(v_q_2742_);
lean_dec_ref(v_p_2739_);
lean_del_object(v___x_2736_);
lean_dec(v_snd_2734_);
lean_dec(v_fst_2733_);
lean_del_object(v___x_2731_);
lean_dec(v_fst_2729_);
lean_del_object(v___x_2726_);
lean_dec_ref(v_arg_2716_);
lean_dec_ref(v_binderType_2711_);
lean_dec(v_binderName_2710_);
v_a_2812_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2746_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2746_);
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
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec_ref(v_00_u03b2_2743_);
lean_dec_ref(v_q_2742_);
lean_dec_ref(v_p_2739_);
lean_dec_ref(v___f_2738_);
lean_del_object(v___x_2736_);
lean_dec(v_snd_2734_);
lean_dec(v_fst_2733_);
lean_del_object(v___x_2731_);
lean_dec(v_fst_2729_);
lean_del_object(v___x_2726_);
lean_dec_ref(v_arg_2716_);
lean_dec_ref(v_binderType_2711_);
lean_dec(v_binderName_2710_);
v_a_2820_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2744_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2744_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2831_; 
lean_dec(v___x_2723_);
v___x_2831_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(v_arg_2716_);
lean_dec_ref(v_arg_2716_);
if (lean_obj_tag(v___x_2831_) == 1)
{
lean_object* v_val_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2938_; 
v_val_2832_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2834_ = v___x_2831_;
v_isShared_2835_ = v_isSharedCheck_2938_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_val_2832_);
lean_dec(v___x_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2938_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v_snd_2836_; lean_object* v_fst_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2937_; 
v_snd_2836_ = lean_ctor_get(v_val_2832_, 1);
v_fst_2837_ = lean_ctor_get(v_val_2832_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v_val_2832_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2839_ = v_val_2832_;
v_isShared_2840_ = v_isSharedCheck_2937_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_snd_2836_);
lean_inc(v_fst_2837_);
lean_dec(v_val_2832_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2937_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v_fst_2841_; lean_object* v_snd_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2936_; 
v_fst_2841_ = lean_ctor_get(v_snd_2836_, 0);
v_snd_2842_ = lean_ctor_get(v_snd_2836_, 1);
v_isSharedCheck_2936_ = !lean_is_exclusive(v_snd_2836_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2844_ = v_snd_2836_;
v_isShared_2845_ = v_isSharedCheck_2936_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_snd_2842_);
lean_inc(v_fst_2841_);
lean_dec(v_snd_2836_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2936_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___f_2846_; lean_object* v_p_2847_; uint8_t v___x_2848_; lean_object* v___x_2849_; lean_object* v_q_2850_; lean_object* v_00_u03b2_2851_; lean_object* v___x_2852_; 
lean_inc_n(v_fst_2841_, 3);
v___f_2846_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2846_, 0, v_fst_2841_);
lean_inc_ref(v_arg_2719_);
lean_inc_ref_n(v_binderType_2711_, 4);
lean_inc_n(v_binderName_2710_, 3);
v_p_2847_ = l_Lean_mkLambda(v_binderName_2710_, v_binderInfo_2713_, v_binderType_2711_, v_arg_2719_);
v___x_2848_ = 0;
lean_inc(v_snd_2842_);
lean_inc(v_fst_2837_);
v___x_2849_ = l_Lean_mkLambda(v_fst_2837_, v___x_2848_, v_fst_2841_, v_snd_2842_);
v_q_2850_ = l_Lean_mkLambda(v_binderName_2710_, v_binderInfo_2713_, v_binderType_2711_, v___x_2849_);
v_00_u03b2_2851_ = l_Lean_mkLambda(v_binderName_2710_, v_binderInfo_2713_, v_binderType_2711_, v_fst_2841_);
v___x_2852_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2711_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2854_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_a_2853_);
lean_dec_ref_known(v___x_2852_, 1);
lean_inc_ref(v_binderType_2711_);
lean_inc(v_binderName_2710_);
v___x_2854_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_binderName_2710_, v_binderType_2711_, v___f_2846_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2854_, 1);
v___x_2856_ = lean_unsigned_to_nat(0u);
v___x_2857_ = lean_unsigned_to_nat(1u);
v___x_2858_ = lean_expr_lift_loose_bvars(v_arg_2719_, v___x_2856_, v___x_2857_);
lean_dec_ref(v_arg_2719_);
v___x_2859_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2858_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2861_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref_known(v___x_2859_, 1);
v___x_2861_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_a_2860_, v_snd_2842_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2863_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
v___x_2863_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_fst_2837_, v___x_2848_, v_fst_2841_, v_a_2862_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2865_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref_known(v___x_2863_, 1);
lean_inc_ref(v_binderType_2711_);
v___x_2865_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_binderName_2710_, v_binderInfo_2713_, v_binderType_2711_, v_a_2864_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2887_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2868_ = v___x_2865_;
v_isShared_2869_ = v_isSharedCheck_2887_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2865_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2887_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2873_; 
v___x_2870_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__3));
v___x_2871_ = lean_box(0);
if (v_isShared_2840_ == 0)
{
lean_ctor_set_tag(v___x_2839_, 1);
lean_ctor_set(v___x_2839_, 1, v___x_2871_);
lean_ctor_set(v___x_2839_, 0, v_a_2855_);
v___x_2873_ = v___x_2839_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2855_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v___x_2871_);
v___x_2873_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2878_; 
v___x_2874_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2874_, 0, v_a_2853_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___x_2875_ = l_Lean_mkConst(v___x_2870_, v___x_2874_);
v___x_2876_ = l_Lean_mkApp4(v___x_2875_, v_binderType_2711_, v_00_u03b2_2851_, v_p_2847_, v_q_2850_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 1, v___x_2876_);
lean_ctor_set(v___x_2844_, 0, v_a_2866_);
v___x_2878_ = v___x_2844_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2866_);
lean_ctor_set(v_reuseFailAlloc_2885_, 1, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
lean_object* v___x_2880_; 
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v___x_2878_);
v___x_2880_ = v___x_2834_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2878_);
v___x_2880_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
lean_object* v___x_2882_; 
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v___x_2880_);
v___x_2882_ = v___x_2868_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec(v_a_2855_);
lean_dec(v_a_2853_);
lean_dec_ref(v_00_u03b2_2851_);
lean_dec_ref(v_q_2850_);
lean_dec_ref(v_p_2847_);
lean_del_object(v___x_2844_);
lean_del_object(v___x_2839_);
lean_del_object(v___x_2834_);
lean_dec_ref(v_binderType_2711_);
v_a_2888_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2865_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2865_);
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
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v_a_2855_);
lean_dec(v_a_2853_);
lean_dec_ref(v_00_u03b2_2851_);
lean_dec_ref(v_q_2850_);
lean_dec_ref(v_p_2847_);
lean_del_object(v___x_2844_);
lean_del_object(v___x_2839_);
lean_del_object(v___x_2834_);
lean_dec_ref(v_binderType_2711_);
lean_dec(v_binderName_2710_);
v_a_2896_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2863_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2863_);
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
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec(v_a_2855_);
lean_dec(v_a_2853_);
lean_dec_ref(v_00_u03b2_2851_);
lean_dec_ref(v_q_2850_);
lean_dec_ref(v_p_2847_);
lean_del_object(v___x_2844_);
lean_dec(v_fst_2841_);
lean_del_object(v___x_2839_);
lean_dec(v_fst_2837_);
lean_del_object(v___x_2834_);
lean_dec_ref(v_binderType_2711_);
lean_dec(v_binderName_2710_);
v_a_2904_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2861_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2861_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec(v_a_2855_);
lean_dec(v_a_2853_);
lean_dec_ref(v_00_u03b2_2851_);
lean_dec_ref(v_q_2850_);
lean_dec_ref(v_p_2847_);
lean_del_object(v___x_2844_);
lean_dec(v_snd_2842_);
lean_dec(v_fst_2841_);
lean_del_object(v___x_2839_);
lean_dec(v_fst_2837_);
lean_del_object(v___x_2834_);
lean_dec_ref(v_binderType_2711_);
lean_dec(v_binderName_2710_);
v_a_2912_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2859_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2859_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec(v_a_2853_);
lean_dec_ref(v_00_u03b2_2851_);
lean_dec_ref(v_q_2850_);
lean_dec_ref(v_p_2847_);
lean_del_object(v___x_2844_);
lean_dec(v_snd_2842_);
lean_dec(v_fst_2841_);
lean_del_object(v___x_2839_);
lean_dec(v_fst_2837_);
lean_del_object(v___x_2834_);
lean_dec_ref(v_arg_2719_);
lean_dec_ref(v_binderType_2711_);
lean_dec(v_binderName_2710_);
v_a_2920_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2854_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2854_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec_ref(v_00_u03b2_2851_);
lean_dec_ref(v_q_2850_);
lean_dec_ref(v_p_2847_);
lean_dec_ref(v___f_2846_);
lean_del_object(v___x_2844_);
lean_dec(v_snd_2842_);
lean_dec(v_fst_2841_);
lean_del_object(v___x_2839_);
lean_dec(v_fst_2837_);
lean_del_object(v___x_2834_);
lean_dec_ref(v_arg_2719_);
lean_dec_ref(v_binderType_2711_);
lean_dec(v_binderName_2710_);
v_a_2928_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2852_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2852_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
lean_dec(v___x_2831_);
lean_dec_ref(v_arg_2719_);
lean_dec_ref(v_binderType_2711_);
lean_dec(v_binderName_2710_);
v___x_2939_ = lean_box(0);
v___x_2940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2939_);
return v___x_2940_;
}
}
}
}
}
}
else
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
lean_dec_ref(v_e_2696_);
v___x_2941_ = lean_box(0);
v___x_2942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
return v___x_2942_;
}
v___jp_2707_:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2708_ = lean_box(0);
v___x_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
return v___x_2709_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___boxed(lean_object* v_e_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f(v_e_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_);
lean_dec(v_a_2952_);
lean_dec_ref(v_a_2951_);
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_a_2944_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg(lean_object* v_fvarId_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2958_ = l_Lean_Expr_fvar___override(v_fvarId_2955_);
v___x_2959_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2958_, v___y_2956_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg___boxed(lean_object* v_fvarId_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg(v_fvarId_2960_, v___y_2961_);
lean_dec(v___y_2961_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___lam__0(lean_object* v___y_2964_, lean_object* v_k_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v_b_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_){
_start:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = l_Lean_Expr_fvarId_x21(v_b_2970_);
v___x_2977_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg(v___x_2976_, v___y_2964_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v___x_2979_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref_known(v___x_2977_, 1);
lean_inc(v___y_2974_);
lean_inc_ref(v___y_2973_);
lean_inc(v___y_2972_);
lean_inc_ref(v___y_2971_);
lean_inc(v___y_2964_);
lean_inc_ref(v___y_2969_);
lean_inc(v___y_2968_);
lean_inc_ref(v___y_2967_);
lean_inc(v___y_2966_);
v___x_2979_ = lean_apply_11(v_k_2965_, v_a_2978_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2964_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, lean_box(0));
return v___x_2979_;
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
lean_dec_ref(v_k_2965_);
v_a_2980_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2977_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2977_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v___y_2988_, lean_object* v_k_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v_b_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___lam__0(v___y_2988_, v_k_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v_b_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec_ref(v_b_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec(v___y_2988_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg(lean_object* v_k_3001_, lean_object* v_name_3002_, uint8_t v_bi_3003_, lean_object* v_type_3004_, uint8_t v_kind_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
lean_object* v___f_3016_; lean_object* v___x_3017_; 
lean_inc_ref(v___y_3009_);
lean_inc(v___y_3008_);
lean_inc_ref(v___y_3007_);
lean_inc(v___y_3006_);
lean_inc(v___y_3010_);
v___f_3016_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_3016_, 0, v___y_3010_);
lean_closure_set(v___f_3016_, 1, v_k_3001_);
lean_closure_set(v___f_3016_, 2, v___y_3006_);
lean_closure_set(v___f_3016_, 3, v___y_3007_);
lean_closure_set(v___f_3016_, 4, v___y_3008_);
lean_closure_set(v___f_3016_, 5, v___y_3009_);
v___x_3017_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3002_, v_bi_3003_, v_type_3004_, v___f_3016_, v_kind_3005_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_);
if (lean_obj_tag(v___x_3017_) == 0)
{
return v___x_3017_;
}
else
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3025_ == 0)
{
v___x_3020_ = v___x_3017_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3017_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3018_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___boxed(lean_object* v_k_3026_, lean_object* v_name_3027_, lean_object* v_bi_3028_, lean_object* v_type_3029_, lean_object* v_kind_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_){
_start:
{
uint8_t v_bi_boxed_3041_; uint8_t v_kind_boxed_3042_; lean_object* v_res_3043_; 
v_bi_boxed_3041_ = lean_unbox(v_bi_3028_);
v_kind_boxed_3042_ = lean_unbox(v_kind_3030_);
v_res_3043_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg(v_k_3026_, v_name_3027_, v_bi_boxed_3041_, v_type_3029_, v_kind_boxed_3042_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3031_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg(lean_object* v_name_3044_, uint8_t v_bi_3045_, lean_object* v_type_3046_, lean_object* v_k_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
uint8_t v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = 0;
v___x_3059_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg(v_k_3047_, v_name_3044_, v_bi_3045_, v_type_3046_, v___x_3058_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg___boxed(lean_object* v_name_3060_, lean_object* v_bi_3061_, lean_object* v_type_3062_, lean_object* v_k_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
uint8_t v_bi_boxed_3074_; lean_object* v_res_3075_; 
v_bi_boxed_3074_ = lean_unbox(v_bi_3061_);
v_res_3075_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg(v_name_3060_, v_bi_boxed_3074_, v_type_3062_, v_k_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___lam__0___boxed(lean_object* v_xs_3076_, lean_object* v_body_3077_, lean_object* v_x_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___lam__0(v_xs_3076_, v_body_3077_, v_x_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go(lean_object* v_xs_3090_, lean_object* v_e_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
if (lean_obj_tag(v_e_3091_) == 7)
{
lean_object* v_binderName_3102_; lean_object* v_binderType_3103_; lean_object* v_body_3104_; uint8_t v_binderInfo_3105_; uint8_t v___x_3106_; 
v_binderName_3102_ = lean_ctor_get(v_e_3091_, 0);
v_binderType_3103_ = lean_ctor_get(v_e_3091_, 1);
v_body_3104_ = lean_ctor_get(v_e_3091_, 2);
v_binderInfo_3105_ = lean_ctor_get_uint8(v_e_3091_, sizeof(void*)*3 + 8);
v___x_3106_ = l_Lean_Expr_isForall(v_body_3104_);
if (v___x_3106_ == 0)
{
lean_object* v___x_3107_; lean_object* v___x_3108_; uint8_t v___x_3109_; 
v___x_3107_ = lean_array_get_size(v_xs_3090_);
v___x_3108_ = lean_unsigned_to_nat(0u);
v___x_3109_ = lean_nat_dec_eq(v___x_3107_, v___x_3108_);
if (v___x_3109_ == 0)
{
uint8_t v___x_3110_; lean_object* v___x_3111_; 
v___x_3110_ = 1;
lean_inc_ref(v_xs_3090_);
v___x_3111_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_3091_, v___x_3108_, v___x_3107_, v_xs_3090_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; lean_object* v___x_3113_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
lean_inc_n(v_a_3112_, 2);
lean_dec_ref_known(v___x_3111_, 1);
v___x_3113_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f(v_a_3112_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3198_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3116_ = v___x_3113_;
v_isShared_3117_ = v_isSharedCheck_3198_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3113_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3198_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
if (lean_obj_tag(v_a_3114_) == 1)
{
lean_object* v_val_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3193_; 
lean_del_object(v___x_3116_);
v_val_3118_ = lean_ctor_get(v_a_3114_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v_a_3114_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3120_ = v_a_3114_;
v_isShared_3121_ = v_isSharedCheck_3193_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_val_3118_);
lean_dec(v_a_3114_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3193_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v_fst_3122_; lean_object* v_snd_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3192_; 
v_fst_3122_ = lean_ctor_get(v_val_3118_, 0);
v_snd_3123_ = lean_ctor_get(v_val_3118_, 1);
v_isSharedCheck_3192_ = !lean_is_exclusive(v_val_3118_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3125_ = v_val_3118_;
v_isShared_3126_ = v_isSharedCheck_3192_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_snd_3123_);
lean_inc(v_fst_3122_);
lean_dec(v_val_3118_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3192_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3127_; 
lean_inc_ref(v_xs_3090_);
v___x_3127_ = l_Lean_Meta_Sym_Simp_mkForallCongrFor(v_xs_3090_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; uint8_t v___x_3129_; lean_object* v___x_3130_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3128_);
lean_dec_ref_known(v___x_3127_, 1);
v___x_3129_ = 1;
v___x_3130_ = l_Lean_Meta_mkLambdaFVars(v_xs_3090_, v_a_3112_, v___x_3109_, v___x_3110_, v___x_3109_, v___x_3110_, v___x_3129_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3132_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3131_);
lean_dec_ref_known(v___x_3130_, 1);
lean_inc(v_fst_3122_);
v___x_3132_ = l_Lean_Meta_mkLambdaFVars(v_xs_3090_, v_fst_3122_, v___x_3109_, v___x_3110_, v___x_3109_, v___x_3110_, v___x_3129_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; lean_object* v___x_3134_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_a_3133_);
lean_dec_ref_known(v___x_3132_, 1);
v___x_3134_ = l_Lean_Meta_mkLambdaFVars(v_xs_3090_, v_snd_3123_, v___x_3109_, v___x_3110_, v___x_3109_, v___x_3110_, v___x_3129_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_a_3135_);
lean_dec_ref_known(v___x_3134_, 1);
v___x_3136_ = l_Lean_mkApp3(v_a_3128_, v_a_3131_, v_a_3133_, v_a_3135_);
v___x_3137_ = l_Lean_Meta_Sym_mkForallFVarsS(v_xs_3090_, v_fst_3122_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3151_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3140_ = v___x_3137_;
v_isShared_3141_ = v_isSharedCheck_3151_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3137_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3151_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 1, v___x_3136_);
lean_ctor_set(v___x_3125_, 0, v_a_3138_);
v___x_3143_ = v___x_3125_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3138_);
lean_ctor_set(v_reuseFailAlloc_3150_, 1, v___x_3136_);
v___x_3143_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
lean_object* v___x_3145_; 
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 0, v___x_3143_);
v___x_3145_ = v___x_3120_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
lean_object* v___x_3147_; 
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 0, v___x_3145_);
v___x_3147_ = v___x_3140_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3145_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
}
else
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec_ref(v___x_3136_);
lean_del_object(v___x_3125_);
lean_del_object(v___x_3120_);
v_a_3152_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3137_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3137_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec(v_a_3133_);
lean_dec(v_a_3131_);
lean_dec(v_a_3128_);
lean_del_object(v___x_3125_);
lean_dec(v_fst_3122_);
lean_del_object(v___x_3120_);
lean_dec_ref(v_xs_3090_);
v_a_3160_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3134_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3134_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_dec(v_a_3131_);
lean_dec(v_a_3128_);
lean_del_object(v___x_3125_);
lean_dec(v_snd_3123_);
lean_dec(v_fst_3122_);
lean_del_object(v___x_3120_);
lean_dec_ref(v_xs_3090_);
v_a_3168_ = lean_ctor_get(v___x_3132_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3132_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3132_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3132_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
lean_dec(v_a_3128_);
lean_del_object(v___x_3125_);
lean_dec(v_snd_3123_);
lean_dec(v_fst_3122_);
lean_del_object(v___x_3120_);
lean_dec_ref(v_xs_3090_);
v_a_3176_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3130_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3130_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3176_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
else
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3191_; 
lean_del_object(v___x_3125_);
lean_dec(v_snd_3123_);
lean_dec(v_fst_3122_);
lean_del_object(v___x_3120_);
lean_dec(v_a_3112_);
lean_dec_ref(v_xs_3090_);
v_a_3184_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v___x_3127_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3127_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3184_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
}
}
else
{
lean_object* v___x_3194_; lean_object* v___x_3196_; 
lean_dec(v_a_3114_);
lean_dec(v_a_3112_);
lean_dec_ref(v_xs_3090_);
v___x_3194_ = lean_box(0);
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 0, v___x_3194_);
v___x_3196_ = v___x_3116_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3194_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
else
{
lean_dec(v_a_3112_);
lean_dec_ref(v_xs_3090_);
return v___x_3113_;
}
}
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_dec_ref(v_xs_3090_);
v_a_3199_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_3111_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3111_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
else
{
lean_object* v___x_3207_; 
lean_dec_ref(v_xs_3090_);
v___x_3207_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f(v_e_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
return v___x_3207_;
}
}
else
{
lean_object* v___f_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
lean_inc_ref(v_body_3104_);
lean_inc_ref(v_binderType_3103_);
lean_inc(v_binderName_3102_);
lean_dec_ref_known(v_e_3091_, 3);
lean_inc_ref(v_xs_3090_);
v___f_3208_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___lam__0___boxed), 13, 2);
lean_closure_set(v___f_3208_, 0, v_xs_3090_);
lean_closure_set(v___f_3208_, 1, v_body_3104_);
v___x_3209_ = lean_unsigned_to_nat(0u);
v___x_3210_ = lean_array_get_size(v_xs_3090_);
v___x_3211_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_binderType_3103_, v___x_3209_, v___x_3210_, v_xs_3090_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v___x_3213_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_a_3212_);
lean_dec_ref_known(v___x_3211_, 1);
v___x_3213_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg(v_binderName_3102_, v_binderInfo_3105_, v_a_3212_, v___f_3208_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
return v___x_3213_;
}
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
lean_dec_ref(v___f_3208_);
lean_dec(v_binderName_3102_);
v_a_3214_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_3211_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3211_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
lean_dec_ref(v_e_3091_);
lean_dec_ref(v_xs_3090_);
v___x_3222_ = lean_box(0);
v___x_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
return v___x_3223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___lam__0(lean_object* v_xs_3224_, lean_object* v_body_3225_, lean_object* v_x_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3237_ = lean_array_push(v_xs_3224_, v_x_3226_);
v___x_3238_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go(v___x_3237_, v_body_3225_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___boxed(lean_object* v_xs_3239_, lean_object* v_e_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go(v_xs_3239_, v_e_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_, v_a_3248_, v_a_3249_);
lean_dec(v_a_3249_);
lean_dec_ref(v_a_3248_);
lean_dec(v_a_3247_);
lean_dec_ref(v_a_3246_);
lean_dec(v_a_3245_);
lean_dec_ref(v_a_3244_);
lean_dec(v_a_3243_);
lean_dec_ref(v_a_3242_);
lean_dec(v_a_3241_);
return v_res_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0(lean_object* v_fvarId_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg(v_fvarId_3252_, v___y_3254_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___boxed(lean_object* v_fvarId_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0(v_fvarId_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2(lean_object* v_00_u03b1_3270_, lean_object* v_k_3271_, lean_object* v_name_3272_, uint8_t v_bi_3273_, lean_object* v_type_3274_, uint8_t v_kind_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_){
_start:
{
lean_object* v___x_3286_; 
v___x_3286_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg(v_k_3271_, v_name_3272_, v_bi_3273_, v_type_3274_, v_kind_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3287_, lean_object* v_k_3288_, lean_object* v_name_3289_, lean_object* v_bi_3290_, lean_object* v_type_3291_, lean_object* v_kind_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
uint8_t v_bi_boxed_3303_; uint8_t v_kind_boxed_3304_; lean_object* v_res_3305_; 
v_bi_boxed_3303_ = lean_unbox(v_bi_3290_);
v_kind_boxed_3304_ = lean_unbox(v_kind_3292_);
v_res_3305_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2(v_00_u03b1_3287_, v_k_3288_, v_name_3289_, v_bi_boxed_3303_, v_type_3291_, v_kind_boxed_3304_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0(lean_object* v_00_u03b1_3306_, lean_object* v_name_3307_, uint8_t v_bi_3308_, lean_object* v_type_3309_, lean_object* v_k_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v___x_3321_; 
v___x_3321_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg(v_name_3307_, v_bi_3308_, v_type_3309_, v_k_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___boxed(lean_object* v_00_u03b1_3322_, lean_object* v_name_3323_, lean_object* v_bi_3324_, lean_object* v_type_3325_, lean_object* v_k_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
uint8_t v_bi_boxed_3337_; lean_object* v_res_3338_; 
v_bi_boxed_3337_ = lean_unbox(v_bi_3324_);
v_res_3338_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0(v_00_u03b1_3322_, v_name_3323_, v_bi_boxed_3337_, v_type_3325_, v_k_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3327_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f(lean_object* v_e_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_){
_start:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; uint8_t v___x_3360_; 
v___x_3358_ = l_Lean_Expr_getForallBody(v_e_3341_);
v___x_3359_ = l_Lean_Expr_cleanupAnnotations(v___x_3358_);
v___x_3360_ = l_Lean_Expr_isApp(v___x_3359_);
if (v___x_3360_ == 0)
{
lean_dec_ref(v___x_3359_);
lean_dec_ref(v_e_3341_);
goto v___jp_3352_;
}
else
{
lean_object* v_arg_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v_arg_3361_ = lean_ctor_get(v___x_3359_, 1);
lean_inc_ref(v_arg_3361_);
v___x_3362_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3359_);
v___x_3363_ = l_Lean_Expr_isApp(v___x_3362_);
if (v___x_3363_ == 0)
{
lean_dec_ref(v___x_3362_);
lean_dec_ref(v_arg_3361_);
lean_dec_ref(v_e_3341_);
goto v___jp_3352_;
}
else
{
lean_object* v_arg_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; uint8_t v___x_3367_; 
v_arg_3364_ = lean_ctor_get(v___x_3362_, 1);
lean_inc_ref(v_arg_3364_);
v___x_3365_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3362_);
v___x_3366_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1));
v___x_3367_ = l_Lean_Expr_isConstOf(v___x_3365_, v___x_3366_);
lean_dec_ref(v___x_3365_);
if (v___x_3367_ == 0)
{
lean_dec_ref(v_arg_3364_);
lean_dec_ref(v_arg_3361_);
lean_dec_ref(v_e_3341_);
goto v___jp_3352_;
}
else
{
lean_object* v___x_3368_; 
v___x_3368_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(v_arg_3364_);
lean_dec_ref(v_arg_3364_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v___x_3369_; 
v___x_3369_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(v_arg_3361_);
lean_dec_ref(v_arg_3361_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v___x_3370_; lean_object* v___x_3371_; 
lean_dec_ref(v_e_3341_);
v___x_3370_ = lean_box(0);
v___x_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3370_);
return v___x_3371_;
}
else
{
lean_dec_ref_known(v___x_3369_, 1);
goto v___jp_3355_;
}
}
else
{
lean_dec_ref_known(v___x_3368_, 1);
lean_dec_ref(v_arg_3361_);
goto v___jp_3355_;
}
}
}
}
v___jp_3352_:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3353_ = lean_box(0);
v___x_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
return v___x_3354_;
}
v___jp_3355_:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f___closed__0));
v___x_3357_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go(v___x_3356_, v_e_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_);
return v___x_3357_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f___boxed(lean_object* v_e_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f(v_e_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
lean_dec(v_a_3381_);
lean_dec_ref(v_a_3380_);
lean_dec(v_a_3379_);
lean_dec_ref(v_a_3378_);
lean_dec(v_a_3377_);
lean_dec_ref(v_a_3376_);
lean_dec(v_a_3375_);
lean_dec_ref(v_a_3374_);
lean_dec(v_a_3373_);
return v_res_3383_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__2(void){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3389_ = lean_box(0);
v___x_3390_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__1));
v___x_3391_ = l_Lean_mkConst(v___x_3390_, v___x_3389_);
return v___x_3391_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__7(void){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3400_ = lean_box(0);
v___x_3401_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__6));
v___x_3402_ = l_Lean_mkConst(v___x_3401_, v___x_3400_);
return v___x_3402_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__10(void){
_start:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3408_ = lean_box(0);
v___x_3409_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__9));
v___x_3410_ = l_Lean_mkConst(v___x_3409_, v___x_3408_);
return v___x_3410_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__13(void){
_start:
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3416_ = lean_box(0);
v___x_3417_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__12));
v___x_3418_ = l_Lean_mkConst(v___x_3417_, v___x_3416_);
return v___x_3418_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__18(void){
_start:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3428_ = lean_box(0);
v___x_3429_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__17));
v___x_3430_ = l_Lean_mkConst(v___x_3429_, v___x_3428_);
return v___x_3430_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__19(void){
_start:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3431_ = lean_unsigned_to_nat(0u);
v___x_3432_ = l_Lean_Level_ofNat(v___x_3431_);
return v___x_3432_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__20(void){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__19, &l_Lean_Meta_Grind_NormSym_simpForall___closed__19_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__19);
v___x_3434_ = l_Lean_mkSort(v___x_3433_);
return v___x_3434_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__23(void){
_start:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3438_ = lean_box(0);
v___x_3439_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__22));
v___x_3440_ = l_Lean_mkConst(v___x_3439_, v___x_3438_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpForall(lean_object* v_e_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_){
_start:
{
lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; 
if (lean_obj_tag(v_e_3441_) == 7)
{
lean_object* v_binderName_3546_; lean_object* v_binderType_3547_; lean_object* v_body_3548_; uint8_t v_binderInfo_3549_; uint8_t v___x_3550_; 
v_binderName_3546_ = lean_ctor_get(v_e_3441_, 0);
v_binderType_3547_ = lean_ctor_get(v_e_3441_, 1);
v_body_3548_ = lean_ctor_get(v_e_3441_, 2);
v_binderInfo_3549_ = lean_ctor_get_uint8(v_e_3441_, sizeof(void*)*3 + 8);
v___x_3550_ = l_Lean_Expr_hasLooseBVars(v_body_3548_);
if (v___x_3550_ == 0)
{
uint8_t v___x_3551_; lean_object* v___x_3552_; 
v___x_3551_ = 1;
lean_inc_ref(v_binderType_3547_);
v___x_3552_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3547_, v_a_3448_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; uint8_t v___x_3556_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3553_);
lean_dec_ref_known(v___x_3552_, 1);
v___x_3554_ = l_Lean_Expr_cleanupAnnotations(v_a_3553_);
v___x_3555_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__6));
v___x_3556_ = l_Lean_Expr_isConstOf(v___x_3554_, v___x_3555_);
if (v___x_3556_ == 0)
{
lean_object* v___x_3557_; uint8_t v___x_3558_; 
v___x_3557_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_3558_ = l_Lean_Expr_isConstOf(v___x_3554_, v___x_3557_);
lean_dec_ref(v___x_3554_);
if (v___x_3558_ == 0)
{
lean_object* v___x_3559_; 
lean_inc_ref(v_body_3548_);
v___x_3559_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_body_3548_, v_a_3448_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v_a_3560_; lean_object* v___x_3561_; uint8_t v___x_3562_; 
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_a_3560_);
lean_dec_ref_known(v___x_3559_, 1);
v___x_3561_ = l_Lean_Expr_cleanupAnnotations(v_a_3560_);
v___x_3562_ = l_Lean_Expr_isConstOf(v___x_3561_, v___x_3555_);
if (v___x_3562_ == 0)
{
uint8_t v___x_3563_; 
v___x_3563_ = l_Lean_Expr_isConstOf(v___x_3561_, v___x_3557_);
lean_dec_ref(v___x_3561_);
if (v___x_3563_ == 0)
{
lean_object* v___x_3564_; 
lean_inc_ref(v_binderType_3547_);
v___x_3564_ = l_Lean_Meta_isProp(v_binderType_3547_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; size_t v___x_3566_; size_t v___x_3567_; uint8_t v___x_3568_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3565_);
lean_dec_ref_known(v___x_3564_, 1);
v___x_3566_ = lean_ptr_addr(v_binderType_3547_);
v___x_3567_ = lean_ptr_addr(v_body_3548_);
v___x_3568_ = lean_usize_dec_eq(v___x_3566_, v___x_3567_);
if (v___x_3568_ == 0)
{
lean_dec(v_a_3565_);
v___y_3453_ = v_a_3442_;
v___y_3454_ = v_a_3443_;
v___y_3455_ = v_a_3444_;
v___y_3456_ = v_a_3445_;
v___y_3457_ = v_a_3446_;
v___y_3458_ = v_a_3447_;
v___y_3459_ = v_a_3448_;
v___y_3460_ = v_a_3449_;
v___y_3461_ = v_a_3450_;
goto v___jp_3452_;
}
else
{
uint8_t v___x_3569_; 
v___x_3569_ = lean_unbox(v_a_3565_);
lean_dec(v_a_3565_);
if (v___x_3569_ == 0)
{
v___y_3453_ = v_a_3442_;
v___y_3454_ = v_a_3443_;
v___y_3455_ = v_a_3444_;
v___y_3456_ = v_a_3445_;
v___y_3457_ = v_a_3446_;
v___y_3458_ = v_a_3447_;
v___y_3459_ = v_a_3448_;
v___y_3460_ = v_a_3449_;
v___y_3461_ = v_a_3450_;
goto v___jp_3452_;
}
else
{
lean_object* v___x_3570_; 
lean_inc_ref(v_binderType_3547_);
lean_dec_ref_known(v_e_3441_, 3);
v___x_3570_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3445_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3581_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3573_ = v___x_3570_;
v_isShared_3574_ = v_isSharedCheck_3581_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3570_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3581_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3579_; 
v___x_3575_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__2, &l_Lean_Meta_Grind_NormSym_simpForall___closed__2_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__2);
v___x_3576_ = l_Lean_Expr_app___override(v___x_3575_, v_binderType_3547_);
v___x_3577_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3577_, 0, v_a_3571_);
lean_ctor_set(v___x_3577_, 1, v___x_3576_);
lean_ctor_set_uint8(v___x_3577_, sizeof(void*)*2, v___x_3551_);
lean_ctor_set_uint8(v___x_3577_, sizeof(void*)*2 + 1, v___x_3563_);
if (v_isShared_3574_ == 0)
{
lean_ctor_set(v___x_3573_, 0, v___x_3577_);
v___x_3579_ = v___x_3573_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
else
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
lean_dec_ref(v_binderType_3547_);
v_a_3582_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v___x_3570_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3570_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
}
}
else
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec_ref_known(v_e_3441_, 3);
v_a_3590_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3564_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3564_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
else
{
lean_object* v___x_3598_; 
lean_inc_ref(v_binderType_3547_);
lean_dec_ref_known(v_e_3441_, 3);
v___x_3598_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3445_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3600_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_a_3599_);
lean_dec_ref_known(v___x_3598_, 1);
lean_inc_ref(v_binderType_3547_);
v___x_3600_ = l_Lean_Meta_getLevel(v_binderType_3547_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3614_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3603_ = v___x_3600_;
v_isShared_3604_ = v_isSharedCheck_3614_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3600_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3614_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3612_; 
v___x_3605_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__4));
v___x_3606_ = lean_box(0);
v___x_3607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3607_, 0, v_a_3601_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = l_Lean_mkConst(v___x_3605_, v___x_3607_);
v___x_3609_ = l_Lean_Expr_app___override(v___x_3608_, v_binderType_3547_);
v___x_3610_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3610_, 0, v_a_3599_);
lean_ctor_set(v___x_3610_, 1, v___x_3609_);
lean_ctor_set_uint8(v___x_3610_, sizeof(void*)*2, v___x_3551_);
lean_ctor_set_uint8(v___x_3610_, sizeof(void*)*2 + 1, v___x_3562_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 0, v___x_3610_);
v___x_3612_ = v___x_3603_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3610_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_dec(v_a_3599_);
lean_dec_ref(v_binderType_3547_);
v_a_3615_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3600_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3600_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec_ref(v_binderType_3547_);
v_a_3623_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3598_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3598_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
}
else
{
lean_object* v___x_3631_; 
lean_dec_ref(v___x_3561_);
lean_inc_ref(v_binderType_3547_);
v___x_3631_ = l_Lean_Meta_isProp(v_binderType_3547_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v_a_3632_; uint8_t v___x_3633_; 
v_a_3632_ = lean_ctor_get(v___x_3631_, 0);
lean_inc(v_a_3632_);
lean_dec_ref_known(v___x_3631_, 1);
v___x_3633_ = lean_unbox(v_a_3632_);
lean_dec(v_a_3632_);
if (v___x_3633_ == 0)
{
v___y_3453_ = v_a_3442_;
v___y_3454_ = v_a_3443_;
v___y_3455_ = v_a_3444_;
v___y_3456_ = v_a_3445_;
v___y_3457_ = v_a_3446_;
v___y_3458_ = v_a_3447_;
v___y_3459_ = v_a_3448_;
v___y_3460_ = v_a_3449_;
v___y_3461_ = v_a_3450_;
goto v___jp_3452_;
}
else
{
lean_object* v___x_3634_; 
lean_inc_ref_n(v_binderType_3547_, 2);
lean_dec_ref_known(v_e_3441_, 3);
v___x_3634_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_binderType_3547_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3645_; 
v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3637_ = v___x_3634_;
v_isShared_3638_ = v_isSharedCheck_3645_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3634_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3645_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3643_; 
v___x_3639_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__7, &l_Lean_Meta_Grind_NormSym_simpForall___closed__7_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__7);
v___x_3640_ = l_Lean_Expr_app___override(v___x_3639_, v_binderType_3547_);
v___x_3641_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3641_, 0, v_a_3635_);
lean_ctor_set(v___x_3641_, 1, v___x_3640_);
lean_ctor_set_uint8(v___x_3641_, sizeof(void*)*2, v___x_3558_);
lean_ctor_set_uint8(v___x_3641_, sizeof(void*)*2 + 1, v___x_3558_);
if (v_isShared_3638_ == 0)
{
lean_ctor_set(v___x_3637_, 0, v___x_3641_);
v___x_3643_ = v___x_3637_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3641_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
else
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
lean_dec_ref(v_binderType_3547_);
v_a_3646_ = lean_ctor_get(v___x_3634_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3634_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3634_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3646_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
}
else
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3661_; 
lean_dec_ref_known(v_e_3441_, 3);
v_a_3654_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3656_ = v___x_3631_;
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3631_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3659_; 
if (v_isShared_3657_ == 0)
{
v___x_3659_ = v___x_3656_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
}
}
else
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3669_; 
lean_dec_ref_known(v_e_3441_, 3);
v_a_3662_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3664_ = v___x_3559_;
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3559_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3667_; 
if (v_isShared_3665_ == 0)
{
v___x_3667_ = v___x_3664_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3662_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
}
else
{
lean_object* v___x_3670_; 
lean_inc_ref(v_body_3548_);
v___x_3670_ = l_Lean_Meta_isProp(v_body_3548_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3682_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3673_ = v___x_3670_;
v_isShared_3674_ = v_isSharedCheck_3682_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3670_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3682_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
uint8_t v___x_3675_; 
v___x_3675_ = lean_unbox(v_a_3671_);
lean_dec(v_a_3671_);
if (v___x_3675_ == 0)
{
lean_del_object(v___x_3673_);
v___y_3453_ = v_a_3442_;
v___y_3454_ = v_a_3443_;
v___y_3455_ = v_a_3444_;
v___y_3456_ = v_a_3445_;
v___y_3457_ = v_a_3446_;
v___y_3458_ = v_a_3447_;
v___y_3459_ = v_a_3448_;
v___y_3460_ = v_a_3449_;
v___y_3461_ = v_a_3450_;
goto v___jp_3452_;
}
else
{
lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3680_; 
lean_inc_ref_n(v_body_3548_, 2);
lean_dec_ref_known(v_e_3441_, 3);
v___x_3676_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__10, &l_Lean_Meta_Grind_NormSym_simpForall___closed__10_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__10);
v___x_3677_ = l_Lean_Expr_app___override(v___x_3676_, v_body_3548_);
v___x_3678_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3678_, 0, v_body_3548_);
lean_ctor_set(v___x_3678_, 1, v___x_3677_);
lean_ctor_set_uint8(v___x_3678_, sizeof(void*)*2, v___x_3551_);
lean_ctor_set_uint8(v___x_3678_, sizeof(void*)*2 + 1, v___x_3556_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 0, v___x_3678_);
v___x_3680_ = v___x_3673_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v___x_3678_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_dec_ref_known(v_e_3441_, 3);
v_a_3683_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3670_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3670_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
}
else
{
lean_object* v___x_3691_; 
lean_dec_ref(v___x_3554_);
lean_inc_ref(v_body_3548_);
v___x_3691_ = l_Lean_Meta_isProp(v_body_3548_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v_a_3692_; uint8_t v___x_3693_; 
v_a_3692_ = lean_ctor_get(v___x_3691_, 0);
lean_inc(v_a_3692_);
lean_dec_ref_known(v___x_3691_, 1);
v___x_3693_ = lean_unbox(v_a_3692_);
lean_dec(v_a_3692_);
if (v___x_3693_ == 0)
{
v___y_3453_ = v_a_3442_;
v___y_3454_ = v_a_3443_;
v___y_3455_ = v_a_3444_;
v___y_3456_ = v_a_3445_;
v___y_3457_ = v_a_3446_;
v___y_3458_ = v_a_3447_;
v___y_3459_ = v_a_3448_;
v___y_3460_ = v_a_3449_;
v___y_3461_ = v_a_3450_;
goto v___jp_3452_;
}
else
{
lean_object* v___x_3694_; 
lean_inc_ref(v_body_3548_);
lean_dec_ref_known(v_e_3441_, 3);
v___x_3694_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3445_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3705_; 
v_a_3695_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3697_ = v___x_3694_;
v_isShared_3698_ = v_isSharedCheck_3705_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3694_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3705_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3703_; 
v___x_3699_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__13, &l_Lean_Meta_Grind_NormSym_simpForall___closed__13_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__13);
v___x_3700_ = l_Lean_Expr_app___override(v___x_3699_, v_body_3548_);
v___x_3701_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3701_, 0, v_a_3695_);
lean_ctor_set(v___x_3701_, 1, v___x_3700_);
lean_ctor_set_uint8(v___x_3701_, sizeof(void*)*2, v___x_3551_);
lean_ctor_set_uint8(v___x_3701_, sizeof(void*)*2 + 1, v___x_3550_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set(v___x_3697_, 0, v___x_3701_);
v___x_3703_ = v___x_3697_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3701_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
else
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3713_; 
lean_dec_ref(v_body_3548_);
v_a_3706_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3708_ = v___x_3694_;
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3694_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_a_3706_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
}
}
else
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3721_; 
lean_dec_ref_known(v_e_3441_, 3);
v_a_3714_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3716_ = v___x_3691_;
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3691_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3721_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
lean_object* v___x_3719_; 
if (v_isShared_3717_ == 0)
{
v___x_3719_ = v___x_3716_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3720_; 
v_reuseFailAlloc_3720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3720_, 0, v_a_3714_);
v___x_3719_ = v_reuseFailAlloc_3720_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
return v___x_3719_;
}
}
}
}
}
else
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
lean_dec_ref_known(v_e_3441_, 3);
v_a_3722_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3552_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3552_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
else
{
uint8_t v___x_3730_; lean_object* v___x_3731_; 
v___x_3730_ = 0;
lean_inc_ref(v_binderType_3547_);
v___x_3731_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3547_, v_a_3448_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v_a_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; uint8_t v___x_3735_; 
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
lean_inc(v_a_3732_);
lean_dec_ref_known(v___x_3731_, 1);
v___x_3733_ = l_Lean_Expr_cleanupAnnotations(v_a_3732_);
v___x_3734_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__6));
v___x_3735_ = l_Lean_Expr_isConstOf(v___x_3733_, v___x_3734_);
if (v___x_3735_ == 0)
{
lean_object* v___x_3736_; uint8_t v___x_3737_; 
v___x_3736_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_3737_ = l_Lean_Expr_isConstOf(v___x_3733_, v___x_3736_);
lean_dec_ref(v___x_3733_);
if (v___x_3737_ == 0)
{
v___y_3453_ = v_a_3442_;
v___y_3454_ = v_a_3443_;
v___y_3455_ = v_a_3444_;
v___y_3456_ = v_a_3445_;
v___y_3457_ = v_a_3446_;
v___y_3458_ = v_a_3447_;
v___y_3459_ = v_a_3448_;
v___y_3460_ = v_a_3449_;
v___y_3461_ = v_a_3450_;
goto v___jp_3452_;
}
else
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3738_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__15));
v___x_3739_ = lean_box(0);
v___x_3740_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v___x_3738_, v___x_3739_, v_a_3446_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_a_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_a_3741_);
lean_dec_ref_known(v___x_3740_, 1);
v___x_3742_ = lean_unsigned_to_nat(1u);
v___x_3743_ = lean_mk_empty_array_with_capacity(v___x_3742_);
v___x_3744_ = lean_array_push(v___x_3743_, v_a_3741_);
lean_inc_ref(v_body_3548_);
v___x_3745_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_body_3548_, v___x_3744_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v___x_3747_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc_n(v_a_3746_, 2);
lean_dec_ref_known(v___x_3745_, 1);
v___x_3747_ = l_Lean_Meta_isProp(v_a_3746_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3747_) == 0)
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3760_; 
v_a_3748_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3750_ = v___x_3747_;
v_isShared_3751_ = v_isSharedCheck_3760_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3747_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3760_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
uint8_t v___x_3752_; 
v___x_3752_ = lean_unbox(v_a_3748_);
lean_dec(v_a_3748_);
if (v___x_3752_ == 0)
{
lean_del_object(v___x_3750_);
lean_dec(v_a_3746_);
v___y_3453_ = v_a_3442_;
v___y_3454_ = v_a_3443_;
v___y_3455_ = v_a_3444_;
v___y_3456_ = v_a_3445_;
v___y_3457_ = v_a_3446_;
v___y_3458_ = v_a_3447_;
v___y_3459_ = v_a_3448_;
v___y_3460_ = v_a_3449_;
v___y_3461_ = v_a_3450_;
goto v___jp_3452_;
}
else
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3758_; 
lean_inc_ref(v_body_3548_);
lean_inc_ref(v_binderType_3547_);
lean_inc(v_binderName_3546_);
lean_dec_ref_known(v_e_3441_, 3);
v___x_3753_ = l_Lean_mkLambda(v_binderName_3546_, v_binderInfo_3549_, v_binderType_3547_, v_body_3548_);
v___x_3754_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__18, &l_Lean_Meta_Grind_NormSym_simpForall___closed__18_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__18);
v___x_3755_ = l_Lean_Expr_app___override(v___x_3754_, v___x_3753_);
v___x_3756_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3756_, 0, v_a_3746_);
lean_ctor_set(v___x_3756_, 1, v___x_3755_);
lean_ctor_set_uint8(v___x_3756_, sizeof(void*)*2, v___x_3550_);
lean_ctor_set_uint8(v___x_3756_, sizeof(void*)*2 + 1, v___x_3730_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 0, v___x_3756_);
v___x_3758_ = v___x_3750_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___x_3756_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_dec(v_a_3746_);
lean_dec_ref_known(v_e_3441_, 3);
v_a_3761_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3747_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3747_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
else
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
lean_dec_ref_known(v_e_3441_, 3);
v_a_3769_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3745_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3745_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_a_3769_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_dec_ref_known(v_e_3441_, 3);
v_a_3777_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3740_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3740_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
}
else
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
lean_dec_ref(v___x_3733_);
lean_inc_ref(v_body_3548_);
lean_inc_ref(v_binderType_3547_);
lean_inc(v_binderName_3546_);
v___x_3785_ = l_Lean_mkLambda(v_binderName_3546_, v_binderInfo_3549_, v_binderType_3547_, v_body_3548_);
lean_inc(v_a_3450_);
lean_inc_ref(v_a_3449_);
lean_inc(v_a_3448_);
lean_inc_ref(v_a_3447_);
lean_inc_ref(v___x_3785_);
v___x_3786_ = lean_infer_type(v___x_3785_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_a_3787_);
lean_dec_ref_known(v___x_3786_, 1);
v___x_3788_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__20, &l_Lean_Meta_Grind_NormSym_simpForall___closed__20_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__20);
lean_inc_ref(v_binderType_3547_);
lean_inc(v_binderName_3546_);
v___x_3789_ = l_Lean_mkForall(v_binderName_3546_, v_binderInfo_3549_, v_binderType_3547_, v___x_3788_);
v___x_3790_ = l_Lean_Meta_isExprDefEq(v_a_3787_, v___x_3789_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v_a_3791_; uint8_t v___x_3792_; 
v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
lean_inc(v_a_3791_);
lean_dec_ref_known(v___x_3790_, 1);
v___x_3792_ = lean_unbox(v_a_3791_);
lean_dec(v_a_3791_);
if (v___x_3792_ == 0)
{
lean_dec_ref(v___x_3785_);
v___y_3453_ = v_a_3442_;
v___y_3454_ = v_a_3443_;
v___y_3455_ = v_a_3444_;
v___y_3456_ = v_a_3445_;
v___y_3457_ = v_a_3446_;
v___y_3458_ = v_a_3447_;
v___y_3459_ = v_a_3448_;
v___y_3460_ = v_a_3449_;
v___y_3461_ = v_a_3450_;
goto v___jp_3452_;
}
else
{
lean_object* v___x_3793_; 
lean_dec_ref_known(v_e_3441_, 3);
v___x_3793_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3445_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3804_; 
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3796_ = v___x_3793_;
v_isShared_3797_ = v_isSharedCheck_3804_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3793_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3804_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3802_; 
v___x_3798_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__23, &l_Lean_Meta_Grind_NormSym_simpForall___closed__23_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__23);
v___x_3799_ = l_Lean_Expr_app___override(v___x_3798_, v___x_3785_);
v___x_3800_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3800_, 0, v_a_3794_);
lean_ctor_set(v___x_3800_, 1, v___x_3799_);
lean_ctor_set_uint8(v___x_3800_, sizeof(void*)*2, v___x_3550_);
lean_ctor_set_uint8(v___x_3800_, sizeof(void*)*2 + 1, v___x_3730_);
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 0, v___x_3800_);
v___x_3802_ = v___x_3796_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v___x_3800_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3812_; 
lean_dec_ref(v___x_3785_);
v_a_3805_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3807_ = v___x_3793_;
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3793_);
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
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_dec_ref(v___x_3785_);
lean_dec_ref_known(v_e_3441_, 3);
v_a_3813_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3790_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3790_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
else
{
lean_object* v_a_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3828_; 
lean_dec_ref(v___x_3785_);
lean_dec_ref_known(v_e_3441_, 3);
v_a_3821_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3823_ = v___x_3786_;
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_a_3821_);
lean_dec(v___x_3786_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
if (v_isShared_3824_ == 0)
{
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_a_3821_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
}
}
}
else
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3836_; 
lean_dec_ref_known(v_e_3441_, 3);
v_a_3829_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3831_ = v___x_3731_;
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3731_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
}
else
{
lean_object* v___x_3837_; lean_object* v___x_3838_; 
lean_dec_ref(v_e_3441_);
v___x_3837_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_3838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3837_);
return v___x_3838_;
}
v___jp_3452_:
{
lean_object* v___x_3462_; 
lean_inc_ref(v_e_3441_);
v___x_3462_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f(v_e_3441_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3537_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3465_ = v___x_3462_;
v_isShared_3466_ = v_isSharedCheck_3537_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3462_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3537_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
if (lean_obj_tag(v_a_3463_) == 1)
{
lean_object* v_val_3467_; lean_object* v_fst_3468_; lean_object* v_snd_3469_; uint8_t v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3473_; 
lean_dec_ref(v_e_3441_);
v_val_3467_ = lean_ctor_get(v_a_3463_, 0);
lean_inc(v_val_3467_);
lean_dec_ref_known(v_a_3463_, 1);
v_fst_3468_ = lean_ctor_get(v_val_3467_, 0);
lean_inc(v_fst_3468_);
v_snd_3469_ = lean_ctor_get(v_val_3467_, 1);
lean_inc(v_snd_3469_);
lean_dec(v_val_3467_);
v___x_3470_ = 0;
v___x_3471_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3471_, 0, v_fst_3468_);
lean_ctor_set(v___x_3471_, 1, v_snd_3469_);
lean_ctor_set_uint8(v___x_3471_, sizeof(void*)*2, v___x_3470_);
lean_ctor_set_uint8(v___x_3471_, sizeof(void*)*2 + 1, v___x_3470_);
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 0, v___x_3471_);
v___x_3473_ = v___x_3465_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
else
{
lean_object* v___x_3475_; 
lean_del_object(v___x_3465_);
lean_dec(v_a_3463_);
v___x_3475_ = l_Lean_Meta_Grind_forallImpAnd_x3f(v_e_3441_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3528_; 
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3478_ = v___x_3475_;
v_isShared_3479_ = v_isSharedCheck_3528_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3475_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3528_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
if (lean_obj_tag(v_a_3476_) == 1)
{
lean_object* v_val_3480_; lean_object* v_snd_3481_; lean_object* v_fst_3482_; lean_object* v_fst_3483_; lean_object* v_snd_3484_; lean_object* v___x_3485_; 
lean_del_object(v___x_3478_);
v_val_3480_ = lean_ctor_get(v_a_3476_, 0);
lean_inc(v_val_3480_);
lean_dec_ref_known(v_a_3476_, 1);
v_snd_3481_ = lean_ctor_get(v_val_3480_, 1);
lean_inc(v_snd_3481_);
v_fst_3482_ = lean_ctor_get(v_val_3480_, 0);
lean_inc(v_fst_3482_);
lean_dec(v_val_3480_);
v_fst_3483_ = lean_ctor_get(v_snd_3481_, 0);
lean_inc(v_fst_3483_);
v_snd_3484_ = lean_ctor_get(v_snd_3481_, 1);
lean_inc(v_snd_3484_);
lean_dec(v_snd_3481_);
v___x_3485_ = l_Lean_Meta_Sym_shareCommonInc(v_fst_3482_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3487_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v___x_3485_, 1);
v___x_3487_ = l_Lean_Meta_Sym_shareCommonInc(v_fst_3483_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3489_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v___x_3487_, 1);
v___x_3489_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v_a_3486_, v_a_3488_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3499_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3492_ = v___x_3489_;
v_isShared_3493_ = v_isSharedCheck_3499_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3489_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3499_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
uint8_t v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3497_; 
v___x_3494_ = 0;
v___x_3495_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3495_, 0, v_a_3490_);
lean_ctor_set(v___x_3495_, 1, v_snd_3484_);
lean_ctor_set_uint8(v___x_3495_, sizeof(void*)*2, v___x_3494_);
lean_ctor_set_uint8(v___x_3495_, sizeof(void*)*2 + 1, v___x_3494_);
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v___x_3495_);
v___x_3497_ = v___x_3492_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3495_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
else
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
lean_dec(v_snd_3484_);
v_a_3500_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3489_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3489_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3500_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec(v_a_3486_);
lean_dec(v_snd_3484_);
v_a_3508_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3487_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3487_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
lean_dec(v_snd_3484_);
lean_dec(v_fst_3483_);
v_a_3516_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3485_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3485_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
else
{
lean_object* v___x_3524_; lean_object* v___x_3526_; 
lean_dec(v_a_3476_);
v___x_3524_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 0, v___x_3524_);
v___x_3526_ = v___x_3478_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
v_a_3529_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3475_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3475_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
}
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
lean_dec_ref(v_e_3441_);
v_a_3538_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3462_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3462_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpForall___boxed(lean_object* v_e_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_Lean_Meta_Grind_NormSym_simpForall(v_e_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_);
lean_dec(v_a_3848_);
lean_dec_ref(v_a_3847_);
lean_dec(v_a_3846_);
lean_dec_ref(v_a_3845_);
lean_dec(v_a_3844_);
lean_dec_ref(v_a_3843_);
lean_dec(v_a_3842_);
lean_dec_ref(v_a_3841_);
lean_dec(v_a_3840_);
return v_res_3850_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpExists___closed__6(void){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3864_ = lean_box(0);
v___x_3865_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___closed__5));
v___x_3866_ = l_Lean_mkConst(v___x_3865_, v___x_3864_);
return v___x_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists(lean_object* v_e_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_){
_start:
{
lean_object* v___x_3899_; uint8_t v___x_3900_; 
v___x_3899_ = l_Lean_Expr_cleanupAnnotations(v_e_3882_);
v___x_3900_ = l_Lean_Expr_isApp(v___x_3899_);
if (v___x_3900_ == 0)
{
lean_dec_ref(v___x_3899_);
goto v___jp_3896_;
}
else
{
lean_object* v_arg_3901_; lean_object* v___x_3902_; uint8_t v___x_3903_; 
v_arg_3901_ = lean_ctor_get(v___x_3899_, 1);
lean_inc_ref(v_arg_3901_);
v___x_3902_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3899_);
v___x_3903_ = l_Lean_Expr_isApp(v___x_3902_);
if (v___x_3903_ == 0)
{
lean_dec_ref(v___x_3902_);
lean_dec_ref(v_arg_3901_);
goto v___jp_3896_;
}
else
{
lean_object* v_arg_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; uint8_t v___x_3907_; 
v_arg_3904_ = lean_ctor_get(v___x_3902_, 1);
lean_inc_ref(v_arg_3904_);
v___x_3905_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3902_);
v___x_3906_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg___closed__1));
v___x_3907_ = l_Lean_Expr_isConstOf(v___x_3905_, v___x_3906_);
if (v___x_3907_ == 0)
{
lean_dec_ref(v___x_3905_);
lean_dec_ref(v_arg_3904_);
lean_dec_ref(v_arg_3901_);
goto v___jp_3896_;
}
else
{
if (lean_obj_tag(v_arg_3901_) == 6)
{
lean_object* v_binderName_3908_; lean_object* v_body_3909_; lean_object* v_u_3910_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; uint8_t v___x_3998_; 
v_binderName_3908_ = lean_ctor_get(v_arg_3901_, 0);
lean_inc(v_binderName_3908_);
v_body_3909_ = lean_ctor_get(v_arg_3901_, 2);
lean_inc_ref(v_body_3909_);
lean_dec_ref_known(v_arg_3901_, 3);
v_u_3910_ = l_Lean_Expr_constLevels_x21(v___x_3905_);
v___x_3998_ = l_Lean_Expr_isApp(v_body_3909_);
if (v___x_3998_ == 0)
{
lean_dec(v_binderName_3908_);
lean_dec_ref(v___x_3905_);
v___y_3912_ = v_a_3883_;
v___y_3913_ = v_a_3884_;
v___y_3914_ = v_a_3885_;
v___y_3915_ = v_a_3886_;
v___y_3916_ = v_a_3887_;
v___y_3917_ = v_a_3888_;
v___y_3918_ = v_a_3889_;
v___y_3919_ = v_a_3890_;
v___y_3920_ = v_a_3891_;
goto v___jp_3911_;
}
else
{
lean_object* v___x_3999_; lean_object* v___x_4000_; uint8_t v___x_4001_; 
v___x_3999_ = l_Lean_Expr_getAppNumArgs(v_body_3909_);
v___x_4000_ = lean_unsigned_to_nat(2u);
v___x_4001_ = lean_nat_dec_eq(v___x_3999_, v___x_4000_);
lean_dec(v___x_3999_);
if (v___x_4001_ == 0)
{
lean_dec(v_binderName_3908_);
lean_dec_ref(v___x_3905_);
v___y_3912_ = v_a_3883_;
v___y_3913_ = v_a_3884_;
v___y_3914_ = v_a_3885_;
v___y_3915_ = v_a_3886_;
v___y_3916_ = v_a_3887_;
v___y_3917_ = v_a_3888_;
v___y_3918_ = v_a_3889_;
v___y_3919_ = v_a_3890_;
v___y_3920_ = v_a_3891_;
goto v___jp_3911_;
}
else
{
lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4002_ = l_Lean_Expr_appFn_x21(v_body_3909_);
v___x_4003_ = l_Lean_Expr_appFn_x21(v___x_4002_);
if (lean_obj_tag(v___x_4003_) == 4)
{
lean_object* v_declName_4004_; lean_object* v___x_4005_; uint8_t v___x_4006_; 
v_declName_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc(v_declName_4004_);
lean_dec_ref_known(v___x_4003_, 2);
v___x_4005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1));
v___x_4006_ = lean_name_eq(v_declName_4004_, v___x_4005_);
if (v___x_4006_ == 0)
{
lean_object* v___x_4007_; uint8_t v___x_4008_; 
v___x_4007_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS___closed__1));
v___x_4008_ = lean_name_eq(v_declName_4004_, v___x_4007_);
lean_dec(v_declName_4004_);
if (v___x_4008_ == 0)
{
lean_dec_ref(v___x_4002_);
lean_dec(v_binderName_3908_);
lean_dec_ref(v___x_3905_);
v___y_3912_ = v_a_3883_;
v___y_3913_ = v_a_3884_;
v___y_3914_ = v_a_3885_;
v___y_3915_ = v_a_3886_;
v___y_3916_ = v_a_3887_;
v___y_3917_ = v_a_3888_;
v___y_3918_ = v_a_3889_;
v___y_3919_ = v_a_3890_;
v___y_3920_ = v_a_3891_;
goto v___jp_3911_;
}
else
{
lean_object* v_b_4009_; lean_object* v_b_4010_; uint8_t v___x_4011_; 
v_b_4009_ = l_Lean_Expr_appArg_x21(v___x_4002_);
lean_dec_ref(v___x_4002_);
v_b_4010_ = l_Lean_Expr_appArg_x21(v_body_3909_);
v___x_4011_ = l_Lean_Expr_hasLooseBVars(v_b_4009_);
if (v___x_4011_ == 0)
{
uint8_t v___x_4012_; lean_object* v___x_4013_; 
lean_dec_ref(v_body_3909_);
v___x_4012_ = 0;
lean_inc_ref(v_arg_3904_);
v___x_4013_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_binderName_3908_, v___x_4012_, v_arg_3904_, v_b_4010_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_object* v_a_4014_; lean_object* v___x_4015_; 
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
lean_inc_n(v_a_4014_, 2);
lean_dec_ref_known(v___x_4013_, 1);
lean_inc_ref(v_arg_3904_);
v___x_4015_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v___x_3905_, v_arg_3904_, v_a_4014_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; lean_object* v___x_4017_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc(v_a_4016_);
lean_dec_ref_known(v___x_4015_, 1);
lean_inc_ref(v_b_4009_);
v___x_4017_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v_b_4009_, v_a_4016_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
if (lean_obj_tag(v___x_4017_) == 0)
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4029_; 
v_a_4018_ = lean_ctor_get(v___x_4017_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_4017_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_4020_ = v___x_4017_;
v_isShared_4021_ = v_isSharedCheck_4029_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_4017_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4029_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4027_; 
v___x_4022_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___closed__8));
v___x_4023_ = l_Lean_mkConst(v___x_4022_, v_u_3910_);
v___x_4024_ = l_Lean_mkApp3(v___x_4023_, v_arg_3904_, v_a_4014_, v_b_4009_);
v___x_4025_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_4025_, 0, v_a_4018_);
lean_ctor_set(v___x_4025_, 1, v___x_4024_);
lean_ctor_set_uint8(v___x_4025_, sizeof(void*)*2, v___x_4006_);
lean_ctor_set_uint8(v___x_4025_, sizeof(void*)*2 + 1, v___x_4006_);
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 0, v___x_4025_);
v___x_4027_ = v___x_4020_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v___x_4025_);
v___x_4027_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
return v___x_4027_;
}
}
}
else
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4037_; 
lean_dec(v_a_4014_);
lean_dec_ref(v_b_4009_);
lean_dec(v_u_3910_);
lean_dec_ref(v_arg_3904_);
v_a_4030_ = lean_ctor_get(v___x_4017_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4017_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4032_ = v___x_4017_;
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_4017_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4035_; 
if (v_isShared_4033_ == 0)
{
v___x_4035_ = v___x_4032_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_a_4030_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
}
}
else
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
lean_dec(v_a_4014_);
lean_dec_ref(v_b_4009_);
lean_dec(v_u_3910_);
lean_dec_ref(v_arg_3904_);
v_a_4038_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_4015_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4015_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
else
{
lean_object* v_a_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4053_; 
lean_dec_ref(v_b_4009_);
lean_dec(v_u_3910_);
lean_dec_ref(v___x_3905_);
lean_dec_ref(v_arg_3904_);
v_a_4046_ = lean_ctor_get(v___x_4013_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4013_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4048_ = v___x_4013_;
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_a_4046_);
lean_dec(v___x_4013_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4051_; 
if (v_isShared_4049_ == 0)
{
v___x_4051_ = v___x_4048_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_a_4046_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
else
{
uint8_t v___x_4054_; 
v___x_4054_ = l_Lean_Expr_hasLooseBVars(v_b_4010_);
if (v___x_4054_ == 0)
{
uint8_t v___x_4055_; lean_object* v___x_4056_; 
lean_dec_ref(v_body_3909_);
v___x_4055_ = 0;
lean_inc_ref(v_arg_3904_);
v___x_4056_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_binderName_3908_, v___x_4055_, v_arg_3904_, v_b_4009_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_object* v_a_4057_; lean_object* v___x_4058_; 
v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
lean_inc_n(v_a_4057_, 2);
lean_dec_ref_known(v___x_4056_, 1);
lean_inc_ref(v_arg_3904_);
v___x_4058_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v___x_3905_, v_arg_3904_, v_a_4057_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
if (lean_obj_tag(v___x_4058_) == 0)
{
lean_object* v_a_4059_; lean_object* v___x_4060_; 
v_a_4059_ = lean_ctor_get(v___x_4058_, 0);
lean_inc(v_a_4059_);
lean_dec_ref_known(v___x_4058_, 1);
lean_inc_ref(v_b_4010_);
v___x_4060_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v_a_4059_, v_b_4010_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4072_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4063_ = v___x_4060_;
v_isShared_4064_ = v_isSharedCheck_4072_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4060_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4072_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4070_; 
v___x_4065_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___closed__10));
v___x_4066_ = l_Lean_mkConst(v___x_4065_, v_u_3910_);
v___x_4067_ = l_Lean_mkApp3(v___x_4066_, v_arg_3904_, v_a_4057_, v_b_4010_);
v___x_4068_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_4068_, 0, v_a_4061_);
lean_ctor_set(v___x_4068_, 1, v___x_4067_);
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*2, v___x_4006_);
lean_ctor_set_uint8(v___x_4068_, sizeof(void*)*2 + 1, v___x_4006_);
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 0, v___x_4068_);
v___x_4070_ = v___x_4063_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4068_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_dec(v_a_4057_);
lean_dec_ref(v_b_4010_);
lean_dec(v_u_3910_);
lean_dec_ref(v_arg_3904_);
v_a_4073_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4060_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4060_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_dec(v_a_4057_);
lean_dec_ref(v_b_4010_);
lean_dec(v_u_3910_);
lean_dec_ref(v_arg_3904_);
v_a_4081_ = lean_ctor_get(v___x_4058_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4058_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4058_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4058_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
lean_dec_ref(v_b_4010_);
lean_dec(v_u_3910_);
lean_dec_ref(v___x_3905_);
lean_dec_ref(v_arg_3904_);
v_a_4089_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4056_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4056_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
else
{
lean_dec_ref(v_b_4010_);
lean_dec_ref(v_b_4009_);
lean_dec(v_binderName_3908_);
lean_dec_ref(v___x_3905_);
v___y_3912_ = v_a_3883_;
v___y_3913_ = v_a_3884_;
v___y_3914_ = v_a_3885_;
v___y_3915_ = v_a_3886_;
v___y_3916_ = v_a_3887_;
v___y_3917_ = v_a_3888_;
v___y_3918_ = v_a_3889_;
v___y_3919_ = v_a_3890_;
v___y_3920_ = v_a_3891_;
goto v___jp_3911_;
}
}
}
}
else
{
lean_object* v_pRaw_4097_; lean_object* v_qRaw_4098_; uint8_t v___x_4099_; lean_object* v___x_4100_; 
lean_dec(v_declName_4004_);
v_pRaw_4097_ = l_Lean_Expr_appArg_x21(v___x_4002_);
lean_dec_ref(v___x_4002_);
v_qRaw_4098_ = l_Lean_Expr_appArg_x21(v_body_3909_);
lean_dec_ref(v_body_3909_);
v___x_4099_ = 0;
lean_inc_ref(v_arg_3904_);
lean_inc(v_binderName_3908_);
v___x_4100_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_binderName_3908_, v___x_4099_, v_arg_3904_, v_pRaw_4097_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_object* v_a_4101_; lean_object* v___x_4102_; 
v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
lean_inc(v_a_4101_);
lean_dec_ref_known(v___x_4100_, 1);
lean_inc_ref(v_arg_3904_);
v___x_4102_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_binderName_3908_, v___x_4099_, v_arg_3904_, v_qRaw_4098_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v_a_4103_; lean_object* v___x_4104_; 
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
lean_inc(v_a_4103_);
lean_dec_ref_known(v___x_4102_, 1);
lean_inc(v_a_4101_);
lean_inc_ref(v_arg_3904_);
lean_inc_ref(v___x_3905_);
v___x_4104_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v___x_3905_, v_arg_3904_, v_a_4101_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
if (lean_obj_tag(v___x_4104_) == 0)
{
lean_object* v_a_4105_; lean_object* v___x_4106_; 
v_a_4105_ = lean_ctor_get(v___x_4104_, 0);
lean_inc(v_a_4105_);
lean_dec_ref_known(v___x_4104_, 1);
lean_inc(v_a_4103_);
lean_inc_ref(v_arg_3904_);
v___x_4106_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v___x_3905_, v_arg_3904_, v_a_4103_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v_a_4107_; lean_object* v___x_4108_; 
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
lean_inc(v_a_4107_);
lean_dec_ref_known(v___x_4106_, 1);
v___x_4108_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_a_4105_, v_a_4107_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4121_; 
v_a_4109_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4111_ = v___x_4108_;
v_isShared_4112_ = v_isSharedCheck_4121_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v___x_4108_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4121_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; uint8_t v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4119_; 
v___x_4113_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___closed__12));
v___x_4114_ = l_Lean_mkConst(v___x_4113_, v_u_3910_);
v___x_4115_ = l_Lean_mkApp3(v___x_4114_, v_arg_3904_, v_a_4101_, v_a_4103_);
v___x_4116_ = 0;
v___x_4117_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_4117_, 0, v_a_4109_);
lean_ctor_set(v___x_4117_, 1, v___x_4115_);
lean_ctor_set_uint8(v___x_4117_, sizeof(void*)*2, v___x_4116_);
lean_ctor_set_uint8(v___x_4117_, sizeof(void*)*2 + 1, v___x_4116_);
if (v_isShared_4112_ == 0)
{
lean_ctor_set(v___x_4111_, 0, v___x_4117_);
v___x_4119_ = v___x_4111_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v___x_4117_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
else
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4129_; 
lean_dec(v_a_4103_);
lean_dec(v_a_4101_);
lean_dec(v_u_3910_);
lean_dec_ref(v_arg_3904_);
v_a_4122_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4124_ = v___x_4108_;
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___x_4108_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4127_; 
if (v_isShared_4125_ == 0)
{
v___x_4127_ = v___x_4124_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4122_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
}
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4137_; 
lean_dec(v_a_4105_);
lean_dec(v_a_4103_);
lean_dec(v_a_4101_);
lean_dec(v_u_3910_);
lean_dec_ref(v_arg_3904_);
v_a_4130_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4132_ = v___x_4106_;
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4106_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4135_; 
if (v_isShared_4133_ == 0)
{
v___x_4135_ = v___x_4132_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4130_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
else
{
lean_object* v_a_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4145_; 
lean_dec(v_a_4103_);
lean_dec(v_a_4101_);
lean_dec(v_u_3910_);
lean_dec_ref(v___x_3905_);
lean_dec_ref(v_arg_3904_);
v_a_4138_ = lean_ctor_get(v___x_4104_, 0);
v_isSharedCheck_4145_ = !lean_is_exclusive(v___x_4104_);
if (v_isSharedCheck_4145_ == 0)
{
v___x_4140_ = v___x_4104_;
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_a_4138_);
lean_dec(v___x_4104_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4145_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v___x_4143_; 
if (v_isShared_4141_ == 0)
{
v___x_4143_ = v___x_4140_;
goto v_reusejp_4142_;
}
else
{
lean_object* v_reuseFailAlloc_4144_; 
v_reuseFailAlloc_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4144_, 0, v_a_4138_);
v___x_4143_ = v_reuseFailAlloc_4144_;
goto v_reusejp_4142_;
}
v_reusejp_4142_:
{
return v___x_4143_;
}
}
}
}
else
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4153_; 
lean_dec(v_a_4101_);
lean_dec(v_u_3910_);
lean_dec_ref(v___x_3905_);
lean_dec_ref(v_arg_3904_);
v_a_4146_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4148_ = v___x_4102_;
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4102_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4151_; 
if (v_isShared_4149_ == 0)
{
v___x_4151_ = v___x_4148_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_a_4146_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
}
}
else
{
lean_object* v_a_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4161_; 
lean_dec_ref(v_qRaw_4098_);
lean_dec(v_u_3910_);
lean_dec(v_binderName_3908_);
lean_dec_ref(v___x_3905_);
lean_dec_ref(v_arg_3904_);
v_a_4154_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4156_ = v___x_4100_;
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_a_4154_);
lean_dec(v___x_4100_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4159_; 
if (v_isShared_4157_ == 0)
{
v___x_4159_ = v___x_4156_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_a_4154_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
}
}
else
{
lean_object* v___x_4162_; lean_object* v___x_4163_; 
lean_dec_ref(v___x_4003_);
lean_dec_ref(v___x_4002_);
lean_dec(v_u_3910_);
lean_dec_ref(v_body_3909_);
lean_dec(v_binderName_3908_);
lean_dec_ref(v___x_3905_);
lean_dec_ref(v_arg_3904_);
v___x_4162_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4162_);
return v___x_4163_;
}
}
}
v___jp_3911_:
{
uint8_t v___x_3921_; 
v___x_3921_ = l_Lean_Expr_hasLooseBVars(v_body_3909_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; 
lean_inc_ref(v_arg_3904_);
v___x_3922_ = l_Lean_Meta_isProp(v_arg_3904_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v_a_3923_; uint8_t v___x_3924_; 
v_a_3923_ = lean_ctor_get(v___x_3922_, 0);
lean_inc(v_a_3923_);
lean_dec_ref_known(v___x_3922_, 1);
v___x_3924_ = lean_unbox(v_a_3923_);
if (v___x_3924_ == 0)
{
lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3925_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___closed__1));
lean_inc(v_u_3910_);
v___x_3926_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v___x_3925_, v_u_3910_, v___y_3916_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v_a_3927_; lean_object* v___x_3928_; 
v_a_3927_ = lean_ctor_get(v___x_3926_, 0);
lean_inc(v_a_3927_);
lean_dec_ref_known(v___x_3926_, 1);
lean_inc_ref(v_arg_3904_);
v___x_3928_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_a_3927_, v_arg_3904_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3930_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3929_);
lean_dec_ref_known(v___x_3928_, 1);
v___x_3930_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_3929_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_);
if (lean_obj_tag(v___x_3930_) == 0)
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3945_; 
v_a_3931_ = lean_ctor_get(v___x_3930_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3933_ = v___x_3930_;
v_isShared_3934_ = v_isSharedCheck_3945_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3930_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3945_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
if (lean_obj_tag(v_a_3931_) == 1)
{
lean_object* v_val_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; uint8_t v___x_3940_; uint8_t v___x_3941_; lean_object* v___x_3943_; 
v_val_3935_ = lean_ctor_get(v_a_3931_, 0);
lean_inc(v_val_3935_);
lean_dec_ref_known(v_a_3931_, 1);
v___x_3936_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___closed__3));
v___x_3937_ = l_Lean_mkConst(v___x_3936_, v_u_3910_);
lean_inc_ref(v_body_3909_);
v___x_3938_ = l_Lean_mkApp3(v___x_3937_, v_arg_3904_, v_val_3935_, v_body_3909_);
v___x_3939_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3939_, 0, v_body_3909_);
lean_ctor_set(v___x_3939_, 1, v___x_3938_);
v___x_3940_ = lean_unbox(v_a_3923_);
lean_ctor_set_uint8(v___x_3939_, sizeof(void*)*2, v___x_3940_);
v___x_3941_ = lean_unbox(v_a_3923_);
lean_dec(v_a_3923_);
lean_ctor_set_uint8(v___x_3939_, sizeof(void*)*2 + 1, v___x_3941_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 0, v___x_3939_);
v___x_3943_ = v___x_3933_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v___x_3939_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
else
{
lean_del_object(v___x_3933_);
lean_dec(v_a_3931_);
lean_dec(v_a_3923_);
lean_dec(v_u_3910_);
lean_dec_ref(v_body_3909_);
lean_dec_ref(v_arg_3904_);
goto v___jp_3893_;
}
}
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_dec(v_a_3923_);
lean_dec(v_u_3910_);
lean_dec_ref(v_body_3909_);
lean_dec_ref(v_arg_3904_);
v_a_3946_ = lean_ctor_get(v___x_3930_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3930_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3930_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
lean_dec(v_a_3923_);
lean_dec(v_u_3910_);
lean_dec_ref(v_body_3909_);
lean_dec_ref(v_arg_3904_);
v_a_3954_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3928_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3928_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
else
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3969_; 
lean_dec(v_a_3923_);
lean_dec(v_u_3910_);
lean_dec_ref(v_body_3909_);
lean_dec_ref(v_arg_3904_);
v_a_3962_ = lean_ctor_get(v___x_3926_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3964_ = v___x_3926_;
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3926_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3967_; 
if (v_isShared_3965_ == 0)
{
v___x_3967_ = v___x_3964_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3962_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
}
}
else
{
lean_object* v___x_3970_; 
lean_dec(v_a_3923_);
lean_dec(v_u_3910_);
lean_inc_ref(v_body_3909_);
lean_inc_ref(v_arg_3904_);
v___x_3970_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v_arg_3904_, v_body_3909_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3981_; 
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3973_ = v___x_3970_;
v_isShared_3974_ = v_isSharedCheck_3981_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3970_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3981_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3979_; 
v___x_3975_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpExists___closed__6, &l_Lean_Meta_Grind_NormSym_simpExists___closed__6_once, _init_l_Lean_Meta_Grind_NormSym_simpExists___closed__6);
v___x_3976_ = l_Lean_mkAppB(v___x_3975_, v_arg_3904_, v_body_3909_);
v___x_3977_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3977_, 0, v_a_3971_);
lean_ctor_set(v___x_3977_, 1, v___x_3976_);
lean_ctor_set_uint8(v___x_3977_, sizeof(void*)*2, v___x_3921_);
lean_ctor_set_uint8(v___x_3977_, sizeof(void*)*2 + 1, v___x_3921_);
if (v_isShared_3974_ == 0)
{
lean_ctor_set(v___x_3973_, 0, v___x_3977_);
v___x_3979_ = v___x_3973_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v___x_3977_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_dec_ref(v_body_3909_);
lean_dec_ref(v_arg_3904_);
v_a_3982_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3970_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3970_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_dec(v_u_3910_);
lean_dec_ref(v_body_3909_);
lean_dec_ref(v_arg_3904_);
v_a_3990_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3922_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3922_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
else
{
lean_dec(v_u_3910_);
lean_dec_ref(v_body_3909_);
lean_dec_ref(v_arg_3904_);
goto v___jp_3893_;
}
}
}
else
{
lean_object* v___x_4164_; lean_object* v___x_4165_; 
lean_dec_ref(v___x_3905_);
lean_dec_ref(v_arg_3904_);
lean_dec_ref(v_arg_3901_);
v___x_4164_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_4165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4164_);
return v___x_4165_;
}
}
}
}
v___jp_3893_:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_3895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3894_);
return v___x_3895_;
}
v___jp_3896_:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3897_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
return v___x_3898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists___boxed(lean_object* v_e_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l_Lean_Meta_Grind_NormSym_simpExists(v_e_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_);
lean_dec(v_a_4175_);
lean_dec_ref(v_a_4174_);
lean_dec(v_a_4173_);
lean_dec_ref(v_a_4172_);
lean_dec(v_a_4171_);
lean_dec_ref(v_a_4170_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
return v_res_4177_;
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

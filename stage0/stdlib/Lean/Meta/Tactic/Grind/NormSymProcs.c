// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.NormSymProcs
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Sym.Simp.Result import Lean.Meta.Sym.Simp.App import Lean.Meta.Match.MatcherInfo import Lean.Meta.Sym.AlphaShareBuilder import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.InferType import Lean.Meta.Sym.SynthInstance import Lean.Meta.AppBuilder import Lean.Meta.Tactic.Grind.ForallAnd import Lean.Meta.CtorRecognizer import Init.Grind.Norm import Init.Grind.Util import Init.Grind.Lemmas import Init.ByCases
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
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_forallImpAnd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_Sym_getTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_sort___override(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_Sym_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_betaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__1_value),LEAN_SCALAR_PTR_LITERAL(208, 215, 171, 150, 192, 180, 249, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__3_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__4_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decide"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__6_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__7_value),LEAN_SCALAR_PTR_LITERAL(16, 96, 65, 173, 152, 155, 4, 222)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__9_value),LEAN_SCALAR_PTR_LITERAL(160, 26, 8, 228, 104, 32, 82, 85)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__11_value),LEAN_SCALAR_PTR_LITERAL(90, 191, 239, 225, 113, 224, 109, 182)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__12_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "bool_eq_to_prop"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(79, 89, 141, 151, 119, 96, 24, 167)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpEq___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__4;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpEq___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "eq_false_eq"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__6_value),LEAN_SCALAR_PTR_LITERAL(79, 24, 241, 157, 245, 218, 196, 160)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpEq___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__8;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpEq___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "eq_true_eq"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__9_value),LEAN_SCALAR_PTR_LITERAL(100, 12, 190, 92, 208, 172, 117, 90)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpEq___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__11;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpEq___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "eq_self"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__12_value),LEAN_SCALAR_PTR_LITERAL(224, 148, 98, 216, 254, 239, 13, 169)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__13_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpEq___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "flip_bool_eq"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__15_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__14_value),LEAN_SCALAR_PTR_LITERAL(19, 65, 30, 112, 127, 84, 12, 55)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpEq___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__16;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpEq___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__18_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__17_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__18_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpEq___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpEq___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__19_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpEq___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpEq___closed__20_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpForall___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpForall___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpForall___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "forall_forall_or"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 112, 166, 94, 237, 48, 167, 129)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpForall___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "forall_or_forall"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__2_value),LEAN_SCALAR_PTR_LITERAL(121, 14, 212, 131, 198, 226, 199, 154)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpForall___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "imp_self_eq"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 96, 8, 70, 216, 37, 74, 175)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpForall___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__6;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpForall___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "imp_true_eq"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__7_value),LEAN_SCALAR_PTR_LITERAL(23, 129, 235, 110, 107, 55, 234, 42)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpForall___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__9;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpForall___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "imp_false_eq"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__10_value),LEAN_SCALAR_PTR_LITERAL(217, 93, 174, 85, 201, 7, 0, 65)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpForall___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__12;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpForall___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "true_imp_eq"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__13_value),LEAN_SCALAR_PTR_LITERAL(20, 154, 121, 57, 70, 129, 111, 154)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpForall___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__15;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpForall___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "false_imp_eq"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__16_value),LEAN_SCALAR_PTR_LITERAL(127, 143, 249, 102, 140, 8, 231, 12)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpForall___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__18;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpForall___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__7_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__19_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__20_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpForall___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "forall_true"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__22_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__21_value),LEAN_SCALAR_PTR_LITERAL(87, 243, 84, 112, 33, 203, 156, 65)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpForall___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__23;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpForall___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__24;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpForall___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__25;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpForall___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "forall_false"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__26_value),LEAN_SCALAR_PTR_LITERAL(12, 96, 31, 202, 138, 131, 44, 134)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpForall___closed__27_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpForall___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpForall___closed__28;
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
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpExists___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "exists_and_right"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__7_value),LEAN_SCALAR_PTR_LITERAL(70, 93, 78, 251, 76, 254, 187, 237)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpExists___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "exists_and_left"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__9_value),LEAN_SCALAR_PTR_LITERAL(211, 136, 99, 9, 218, 202, 25, 69)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpExists___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "exists_or"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__12_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__11_value),LEAN_SCALAR_PTR_LITERAL(161, 112, 226, 203, 229, 162, 152, 185)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(lean_object* v_declName_1_, lean_object* v_us_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = l_Lean_Expr_const___override(v_declName_1_, v_us_2_);
v___x_6_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_5_, v___y_3_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1_ = stack[0].m_obj;
lean_object* v_us_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v_res_7_;
v_res_7_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v_declName_1_, v_us_2_, v___y_3_);
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg___boxed(lean_object* v_declName_8_, lean_object* v_us_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v_declName_8_, v_us_9_, v___y_10_);
lean_dec(v___y_10_);
return v_res_12_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0(lean_object* v_declName_13_, lean_object* v_us_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v_declName_13_, v_us_14_, v___y_19_);
return v___x_25_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_13_ = stack[0].m_obj;
lean_object* v_us_14_ = stack[1].m_obj;
lean_object* v___y_15_ = stack[2].m_obj;
lean_object* v___y_16_ = stack[3].m_obj;
lean_object* v___y_17_ = stack[4].m_obj;
lean_object* v___y_18_ = stack[5].m_obj;
lean_object* v___y_19_ = stack[6].m_obj;
lean_object* v___y_20_ = stack[7].m_obj;
lean_object* v___y_21_ = stack[8].m_obj;
lean_object* v___y_22_ = stack[9].m_obj;
lean_object* v___y_23_ = stack[10].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0(v_declName_13_, v_us_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___boxed(lean_object* v_declName_27_, lean_object* v_us_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0(v_declName_27_, v_us_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
lean_dec(v___y_35_);
lean_dec_ref(v___y_34_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
lean_dec(v___y_31_);
lean_dec_ref(v___y_30_);
lean_dec(v___y_29_);
return v_res_39_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(lean_object* v_f_40_, lean_object* v_a_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v___y_50_; lean_object* v___x_53_; uint8_t v_debug_54_; 
v___x_53_ = lean_st_ref_get(v___y_43_);
v_debug_54_ = lean_ctor_get_uint8(v___x_53_, sizeof(void*)*12);
lean_dec(v___x_53_);
if (v_debug_54_ == 0)
{
v___y_50_ = v___y_43_;
goto v___jp_49_;
}
else
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_40_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
if (lean_obj_tag(v___x_55_) == 0)
{
lean_object* v___x_56_; 
lean_dec_ref_known(v___x_55_, 1);
v___x_56_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_dec_ref_known(v___x_56_, 1);
v___y_50_ = v___y_43_;
goto v___jp_49_;
}
else
{
lean_object* v_a_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_64_; 
lean_dec_ref(v_a_41_);
lean_dec_ref(v_f_40_);
v_a_57_ = lean_ctor_get(v___x_56_, 0);
v_isSharedCheck_64_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_64_ == 0)
{
v___x_59_ = v___x_56_;
v_isShared_60_ = v_isSharedCheck_64_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_a_57_);
lean_dec(v___x_56_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_64_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_62_; 
if (v_isShared_60_ == 0)
{
v___x_62_ = v___x_59_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_a_57_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
}
else
{
lean_object* v_a_65_; lean_object* v___x_67_; uint8_t v_isShared_68_; uint8_t v_isSharedCheck_72_; 
lean_dec_ref(v_a_41_);
lean_dec_ref(v_f_40_);
v_a_65_ = lean_ctor_get(v___x_55_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_55_);
if (v_isSharedCheck_72_ == 0)
{
v___x_67_ = v___x_55_;
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
else
{
lean_inc(v_a_65_);
lean_dec(v___x_55_);
v___x_67_ = lean_box(0);
v_isShared_68_ = v_isSharedCheck_72_;
goto v_resetjp_66_;
}
v_resetjp_66_:
{
lean_object* v___x_70_; 
if (v_isShared_68_ == 0)
{
v___x_70_ = v___x_67_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_a_65_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
}
v___jp_49_:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = l_Lean_Expr_app___override(v_f_40_, v_a_41_);
v___x_52_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_51_, v___y_50_);
return v___x_52_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_40_ = stack[0].m_obj;
lean_object* v_a_41_ = stack[1].m_obj;
lean_object* v___y_42_ = stack[2].m_obj;
lean_object* v___y_43_ = stack[3].m_obj;
lean_object* v___y_44_ = stack[4].m_obj;
lean_object* v___y_45_ = stack[5].m_obj;
lean_object* v___y_46_ = stack[6].m_obj;
lean_object* v___y_47_ = stack[7].m_obj;
lean_object* v_res_73_;
v_res_73_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_f_40_, v_a_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_);
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg___boxed(lean_object* v_f_74_, lean_object* v_a_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_f_74_, v_a_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
return v_res_83_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1(lean_object* v_f_84_, lean_object* v_a_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_f_84_, v_a_85_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
return v___x_96_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_84_ = stack[0].m_obj;
lean_object* v_a_85_ = stack[1].m_obj;
lean_object* v___y_86_ = stack[2].m_obj;
lean_object* v___y_87_ = stack[3].m_obj;
lean_object* v___y_88_ = stack[4].m_obj;
lean_object* v___y_89_ = stack[5].m_obj;
lean_object* v___y_90_ = stack[6].m_obj;
lean_object* v___y_91_ = stack[7].m_obj;
lean_object* v___y_92_ = stack[8].m_obj;
lean_object* v___y_93_ = stack[9].m_obj;
lean_object* v___y_94_ = stack[10].m_obj;
lean_object* v_res_97_;
v_res_97_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1(v_f_84_, v_a_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
stack->m_obj
 = v_res_97_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___boxed(lean_object* v_f_98_, lean_object* v_a_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1(v_f_98_, v_a_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
return v_res_110_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(lean_object* v_p_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS___closed__1));
v___x_126_ = lean_box(0);
v___x_127_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v___x_125_, v___x_126_, v_a_119_);
if (lean_obj_tag(v___x_127_) == 0)
{
lean_object* v_a_128_; lean_object* v___x_129_; 
v_a_128_ = lean_ctor_get(v___x_127_, 0);
lean_inc(v_a_128_);
lean_dec_ref_known(v___x_127_, 1);
v___x_129_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_a_128_, v_p_114_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_);
return v___x_129_;
}
else
{
lean_dec_ref(v_p_114_);
return v___x_127_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_114_ = stack[0].m_obj;
lean_object* v_a_115_ = stack[1].m_obj;
lean_object* v_a_116_ = stack[2].m_obj;
lean_object* v_a_117_ = stack[3].m_obj;
lean_object* v_a_118_ = stack[4].m_obj;
lean_object* v_a_119_ = stack[5].m_obj;
lean_object* v_a_120_ = stack[6].m_obj;
lean_object* v_a_121_ = stack[7].m_obj;
lean_object* v_a_122_ = stack[8].m_obj;
lean_object* v_a_123_ = stack[9].m_obj;
lean_object* v_res_130_;
v_res_130_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_p_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_);
stack->m_obj
 = v_res_130_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS___boxed(lean_object* v_p_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_p_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
lean_dec(v_a_138_);
lean_dec_ref(v_a_137_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
return v_res_142_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(lean_object* v_f_143_, lean_object* v_a_u2081_144_, lean_object* v_a_u2082_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_f_143_, v_a_u2081_144_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___x_155_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
lean_inc(v_a_154_);
lean_dec_ref_known(v___x_153_, 1);
v___x_155_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_a_154_, v_a_u2082_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
return v___x_155_;
}
else
{
lean_dec_ref(v_a_u2082_145_);
return v___x_153_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_143_ = stack[0].m_obj;
lean_object* v_a_u2081_144_ = stack[1].m_obj;
lean_object* v_a_u2082_145_ = stack[2].m_obj;
lean_object* v___y_146_ = stack[3].m_obj;
lean_object* v___y_147_ = stack[4].m_obj;
lean_object* v___y_148_ = stack[5].m_obj;
lean_object* v___y_149_ = stack[6].m_obj;
lean_object* v___y_150_ = stack[7].m_obj;
lean_object* v___y_151_ = stack[8].m_obj;
lean_object* v_res_156_;
v_res_156_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v_f_143_, v_a_u2081_144_, v_a_u2082_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
stack->m_obj
 = v_res_156_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg___boxed(lean_object* v_f_157_, lean_object* v_a_u2081_158_, lean_object* v_a_u2082_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v_f_157_, v_a_u2081_158_, v_a_u2082_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
return v_res_167_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(lean_object* v_p_171_, lean_object* v_q_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS___closed__1));
v___x_184_ = lean_box(0);
v___x_185_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v___x_183_, v___x_184_, v_a_177_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_187_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_185_, 1);
v___x_187_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v_a_186_, v_p_171_, v_q_172_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
return v___x_187_;
}
else
{
lean_dec_ref(v_q_172_);
lean_dec_ref(v_p_171_);
return v___x_185_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_171_ = stack[0].m_obj;
lean_object* v_q_172_ = stack[1].m_obj;
lean_object* v_a_173_ = stack[2].m_obj;
lean_object* v_a_174_ = stack[3].m_obj;
lean_object* v_a_175_ = stack[4].m_obj;
lean_object* v_a_176_ = stack[5].m_obj;
lean_object* v_a_177_ = stack[6].m_obj;
lean_object* v_a_178_ = stack[7].m_obj;
lean_object* v_a_179_ = stack[8].m_obj;
lean_object* v_a_180_ = stack[9].m_obj;
lean_object* v_a_181_ = stack[10].m_obj;
lean_object* v_res_188_;
v_res_188_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v_p_171_, v_q_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
stack->m_obj
 = v_res_188_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS___boxed(lean_object* v_p_189_, lean_object* v_q_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v_p_189_, v_q_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
return v_res_201_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0(lean_object* v_f_202_, lean_object* v_a_u2081_203_, lean_object* v_a_u2082_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v_f_202_, v_a_u2081_203_, v_a_u2082_204_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
return v___x_215_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_202_ = stack[0].m_obj;
lean_object* v_a_u2081_203_ = stack[1].m_obj;
lean_object* v_a_u2082_204_ = stack[2].m_obj;
lean_object* v___y_205_ = stack[3].m_obj;
lean_object* v___y_206_ = stack[4].m_obj;
lean_object* v___y_207_ = stack[5].m_obj;
lean_object* v___y_208_ = stack[6].m_obj;
lean_object* v___y_209_ = stack[7].m_obj;
lean_object* v___y_210_ = stack[8].m_obj;
lean_object* v___y_211_ = stack[9].m_obj;
lean_object* v___y_212_ = stack[10].m_obj;
lean_object* v___y_213_ = stack[11].m_obj;
lean_object* v_res_216_;
v_res_216_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0(v_f_202_, v_a_u2081_203_, v_a_u2082_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
stack->m_obj
 = v_res_216_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___boxed(lean_object* v_f_217_, lean_object* v_a_u2081_218_, lean_object* v_a_u2082_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0(v_f_217_, v_a_u2081_218_, v_a_u2082_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
return v_res_230_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(lean_object* v_p_234_, lean_object* v_q_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1));
v___x_244_ = lean_box(0);
v___x_245_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v___x_243_, v___x_244_, v_a_237_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v_a_246_; lean_object* v___x_247_; 
v_a_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_a_246_);
lean_dec_ref_known(v___x_245_, 1);
v___x_247_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v_a_246_, v_p_234_, v_q_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_);
return v___x_247_;
}
else
{
lean_dec_ref(v_q_235_);
lean_dec_ref(v_p_234_);
return v___x_245_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_234_ = stack[0].m_obj;
lean_object* v_q_235_ = stack[1].m_obj;
lean_object* v_a_236_ = stack[2].m_obj;
lean_object* v_a_237_ = stack[3].m_obj;
lean_object* v_a_238_ = stack[4].m_obj;
lean_object* v_a_239_ = stack[5].m_obj;
lean_object* v_a_240_ = stack[6].m_obj;
lean_object* v_a_241_ = stack[7].m_obj;
lean_object* v_res_248_;
v_res_248_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_p_234_, v_q_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_);
stack->m_obj
 = v_res_248_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___boxed(lean_object* v_p_249_, lean_object* v_q_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_p_249_, v_q_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_);
lean_dec(v_a_256_);
lean_dec_ref(v_a_255_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
return v_res_258_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS(lean_object* v_p_259_, lean_object* v_q_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_p_259_, v_q_260_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
return v___x_271_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_259_ = stack[0].m_obj;
lean_object* v_q_260_ = stack[1].m_obj;
lean_object* v_a_261_ = stack[2].m_obj;
lean_object* v_a_262_ = stack[3].m_obj;
lean_object* v_a_263_ = stack[4].m_obj;
lean_object* v_a_264_ = stack[5].m_obj;
lean_object* v_a_265_ = stack[6].m_obj;
lean_object* v_a_266_ = stack[7].m_obj;
lean_object* v_a_267_ = stack[8].m_obj;
lean_object* v_a_268_ = stack[9].m_obj;
lean_object* v_a_269_ = stack[10].m_obj;
lean_object* v_res_272_;
v_res_272_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS(v_p_259_, v_q_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_);
stack->m_obj
 = v_res_272_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___boxed(lean_object* v_p_273_, lean_object* v_q_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS(v_p_273_, v_q_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
return v_res_285_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg(lean_object* v_u_289_, lean_object* v_00_u03b1_290_, lean_object* v_p_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_299_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg___closed__1));
v___x_300_ = lean_box(0);
v___x_301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_301_, 0, v_u_289_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v___x_299_, v___x_301_, v_a_293_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_304_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_303_);
lean_dec_ref_known(v___x_302_, 1);
v___x_304_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v_a_303_, v_00_u03b1_290_, v_p_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_);
return v___x_304_;
}
else
{
lean_dec_ref(v_p_291_);
lean_dec_ref(v_00_u03b1_290_);
return v___x_302_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_289_ = stack[0].m_obj;
lean_object* v_00_u03b1_290_ = stack[1].m_obj;
lean_object* v_p_291_ = stack[2].m_obj;
lean_object* v_a_292_ = stack[3].m_obj;
lean_object* v_a_293_ = stack[4].m_obj;
lean_object* v_a_294_ = stack[5].m_obj;
lean_object* v_a_295_ = stack[6].m_obj;
lean_object* v_a_296_ = stack[7].m_obj;
lean_object* v_a_297_ = stack[8].m_obj;
lean_object* v_res_305_;
v_res_305_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg(v_u_289_, v_00_u03b1_290_, v_p_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_);
stack->m_obj
 = v_res_305_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg___boxed(lean_object* v_u_306_, lean_object* v_00_u03b1_307_, lean_object* v_p_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg(v_u_306_, v_00_u03b1_307_, v_p_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
return v_res_316_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS(lean_object* v_u_317_, lean_object* v_00_u03b1_318_, lean_object* v_p_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg(v_u_317_, v_00_u03b1_318_, v_p_319_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
return v___x_330_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_317_ = stack[0].m_obj;
lean_object* v_00_u03b1_318_ = stack[1].m_obj;
lean_object* v_p_319_ = stack[2].m_obj;
lean_object* v_a_320_ = stack[3].m_obj;
lean_object* v_a_321_ = stack[4].m_obj;
lean_object* v_a_322_ = stack[5].m_obj;
lean_object* v_a_323_ = stack[6].m_obj;
lean_object* v_a_324_ = stack[7].m_obj;
lean_object* v_a_325_ = stack[8].m_obj;
lean_object* v_a_326_ = stack[9].m_obj;
lean_object* v_a_327_ = stack[10].m_obj;
lean_object* v_a_328_ = stack[11].m_obj;
lean_object* v_res_331_;
v_res_331_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS(v_u_317_, v_00_u03b1_318_, v_p_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
stack->m_obj
 = v_res_331_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___boxed(lean_object* v_u_332_, lean_object* v_00_u03b1_333_, lean_object* v_p_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS(v_u_332_, v_00_u03b1_333_, v_p_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec(v_a_339_);
lean_dec_ref(v_a_338_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
return v_res_345_;
}
}
lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___redArg(lean_object* v_e_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
if (lean_obj_tag(v_e_348_) == 10)
{
lean_object* v_expr_356_; lean_object* v___x_357_; 
v_expr_356_ = lean_ctor_get(v_e_348_, 1);
lean_inc_ref_n(v_expr_356_, 2);
lean_dec_ref_known(v_e_348_, 2);
v___x_357_ = l_Lean_Meta_Sym_mkEqRefl(v_expr_356_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_367_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_367_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_367_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_367_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
uint8_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_362_ = 0;
v___x_363_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_363_, 0, v_expr_356_);
lean_ctor_set(v___x_363_, 1, v_a_358_);
lean_ctor_set_uint8(v___x_363_, sizeof(void*)*2, v___x_362_);
lean_ctor_set_uint8(v___x_363_, sizeof(void*)*2 + 1, v___x_362_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_363_);
v___x_365_ = v___x_360_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec_ref(v_expr_356_);
v_a_368_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_357_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_357_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
else
{
lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec_ref(v_e_348_);
v___x_376_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_NormSym_eraseMData___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_348_ = stack[0].m_obj;
lean_object* v_a_349_ = stack[1].m_obj;
lean_object* v_a_350_ = stack[2].m_obj;
lean_object* v_a_351_ = stack[3].m_obj;
lean_object* v_a_352_ = stack[4].m_obj;
lean_object* v_a_353_ = stack[5].m_obj;
lean_object* v_a_354_ = stack[6].m_obj;
lean_object* v_res_378_;
v_res_378_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v_e_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
stack->m_obj
 = v_res_378_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___redArg___boxed(lean_object* v_e_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v_e_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
return v_res_387_;
}
}
lean_object* l_Lean_Meta_Grind_NormSym_eraseMData(lean_object* v_e_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v_e_388_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
return v___x_399_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_NormSym_eraseMData_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_388_ = stack[0].m_obj;
lean_object* v_a_389_ = stack[1].m_obj;
lean_object* v_a_390_ = stack[2].m_obj;
lean_object* v_a_391_ = stack[3].m_obj;
lean_object* v_a_392_ = stack[4].m_obj;
lean_object* v_a_393_ = stack[5].m_obj;
lean_object* v_a_394_ = stack[6].m_obj;
lean_object* v_a_395_ = stack[7].m_obj;
lean_object* v_a_396_ = stack[8].m_obj;
lean_object* v_a_397_ = stack[9].m_obj;
lean_object* v_res_400_;
v_res_400_ = l_Lean_Meta_Grind_NormSym_eraseMData(v_e_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
stack->m_obj
 = v_res_400_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___boxed(lean_object* v_e_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Meta_Grind_NormSym_eraseMData(v_e_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
return v_res_412_;
}
}
lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(lean_object* v_e_420_){
_start:
{
lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_425_ = l_Lean_Expr_cleanupAnnotations(v_e_420_);
v___x_426_ = l_Lean_Expr_isApp(v___x_425_);
if (v___x_426_ == 0)
{
lean_dec_ref(v___x_425_);
goto v___jp_422_;
}
else
{
lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_427_ = l_Lean_Expr_appFnCleanup___redArg(v___x_425_);
v___x_428_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__3));
v___x_429_ = l_Lean_Expr_isConstOf(v___x_427_, v___x_428_);
lean_dec_ref(v___x_427_);
if (v___x_429_ == 0)
{
goto v___jp_422_;
}
else
{
uint8_t v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = 0;
v___x_431_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_429_, v___x_430_);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
}
v___jp_422_:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_NormSym_preMatchCond___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_420_ = stack[0].m_obj;
lean_object* v_res_433_;
v_res_433_ = l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(v_e_420_);
stack->m_obj
 = v_res_433_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___boxed(lean_object* v_e_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(v_e_434_);
return v_res_436_;
}
}
lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond(lean_object* v_e_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(v_e_437_);
return v___x_448_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_NormSym_preMatchCond_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_437_ = stack[0].m_obj;
lean_object* v_a_438_ = stack[1].m_obj;
lean_object* v_a_439_ = stack[2].m_obj;
lean_object* v_a_440_ = stack[3].m_obj;
lean_object* v_a_441_ = stack[4].m_obj;
lean_object* v_a_442_ = stack[5].m_obj;
lean_object* v_a_443_ = stack[6].m_obj;
lean_object* v_a_444_ = stack[7].m_obj;
lean_object* v_a_445_ = stack[8].m_obj;
lean_object* v_a_446_ = stack[9].m_obj;
lean_object* v_res_449_;
v_res_449_ = l_Lean_Meta_Grind_NormSym_preMatchCond(v_e_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
stack->m_obj
 = v_res_449_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___boxed(lean_object* v_e_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Meta_Grind_NormSym_preMatchCond(v_e_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
lean_dec(v_a_451_);
return v_res_461_;
}
}
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(lean_object* v_declName_462_, lean_object* v___y_463_){
_start:
{
lean_object* v___x_465_; lean_object* v_env_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_465_ = lean_st_ref_get(v___y_463_);
v_env_466_ = lean_ctor_get(v___x_465_, 0);
lean_inc_ref(v_env_466_);
lean_dec(v___x_465_);
v___x_467_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_466_, v_declName_462_);
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_462_ = stack[0].m_obj;
lean_object* v___y_463_ = stack[1].m_obj;
lean_object* v_res_469_;
v_res_469_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(v_declName_462_, v___y_463_);
stack->m_obj
 = v_res_469_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg___boxed(lean_object* v_declName_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(v_declName_470_, v___y_471_);
lean_dec(v___y_471_);
return v_res_473_;
}
}
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0(lean_object* v_declName_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(v_declName_474_, v___y_483_);
return v___x_485_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_474_ = stack[0].m_obj;
lean_object* v___y_475_ = stack[1].m_obj;
lean_object* v___y_476_ = stack[2].m_obj;
lean_object* v___y_477_ = stack[3].m_obj;
lean_object* v___y_478_ = stack[4].m_obj;
lean_object* v___y_479_ = stack[5].m_obj;
lean_object* v___y_480_ = stack[6].m_obj;
lean_object* v___y_481_ = stack[7].m_obj;
lean_object* v___y_482_ = stack[8].m_obj;
lean_object* v___y_483_ = stack[9].m_obj;
lean_object* v_res_486_;
v_res_486_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0(v_declName_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
stack->m_obj
 = v_res_486_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___boxed(lean_object* v_declName_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0(v_declName_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
return v_res_498_;
}
}
lean_object* l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(lean_object* v_e_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
if (lean_obj_tag(v_e_504_) == 5)
{
lean_object* v_fn_518_; lean_object* v_arg_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v_fn_518_ = lean_ctor_get(v_e_504_, 0);
lean_inc_ref(v_fn_518_);
v_arg_519_ = lean_ctor_get(v_e_504_, 1);
lean_inc_ref(v_arg_519_);
lean_inc_ref(v_e_504_);
v___x_520_ = l_Lean_Expr_cleanupAnnotations(v_e_504_);
v___x_521_ = l_Lean_Expr_isApp(v___x_520_);
if (v___x_521_ == 0)
{
lean_dec_ref(v___x_520_);
lean_dec_ref(v_arg_519_);
lean_dec_ref_known(v_e_504_, 2);
lean_dec_ref(v_fn_518_);
goto v___jp_515_;
}
else
{
lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_522_ = l_Lean_Expr_appFnCleanup___redArg(v___x_520_);
v___x_523_ = l_Lean_Expr_isApp(v___x_522_);
if (v___x_523_ == 0)
{
lean_dec_ref(v___x_522_);
lean_dec_ref(v_arg_519_);
lean_dec_ref_known(v_e_504_, 2);
lean_dec_ref(v_fn_518_);
goto v___jp_515_;
}
else
{
lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v___x_524_ = l_Lean_Expr_appFnCleanup___redArg(v___x_522_);
v___x_525_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___closed__1));
v___x_526_ = l_Lean_Expr_isConstOf(v___x_524_, v___x_525_);
lean_dec_ref(v___x_524_);
if (v___x_526_ == 0)
{
lean_dec_ref(v_arg_519_);
lean_dec_ref_known(v_e_504_, 2);
lean_dec_ref(v_fn_518_);
goto v___jp_515_;
}
else
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_Expr_getAppFn(v_arg_519_);
if (lean_obj_tag(v___x_527_) == 4)
{
lean_object* v_declName_528_; lean_object* v___x_529_; lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_571_; 
v_declName_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_declName_528_);
lean_dec_ref_known(v___x_527_, 2);
v___x_529_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(v_declName_528_, v_a_513_);
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_571_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_571_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_571_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
if (lean_obj_tag(v_a_530_) == 1)
{
lean_object* v_val_534_; lean_object* v_numParams_535_; lean_object* v_numDiscrs_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
lean_del_object(v___x_532_);
v_val_534_ = lean_ctor_get(v_a_530_, 0);
lean_inc(v_val_534_);
lean_dec_ref_known(v_a_530_, 1);
v_numParams_535_ = lean_ctor_get(v_val_534_, 0);
lean_inc(v_numParams_535_);
v_numDiscrs_536_ = lean_ctor_get(v_val_534_, 1);
lean_inc(v_numDiscrs_536_);
lean_dec(v_val_534_);
v___x_537_ = lean_unsigned_to_nat(1u);
v___x_538_ = lean_nat_add(v_numParams_535_, v___x_537_);
lean_dec(v_numParams_535_);
v___x_539_ = lean_nat_add(v___x_538_, v_numDiscrs_536_);
lean_dec(v_numDiscrs_536_);
lean_inc_ref(v_arg_519_);
v___x_540_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_arg_519_, v___x_538_, v___x_539_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
lean_dec(v___x_539_);
lean_dec(v___x_538_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_542_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_a_541_);
lean_dec_ref_known(v___x_540_, 1);
v___x_542_ = l_Lean_Meta_Sym_Simp_mkCongrArg___redArg(v_e_504_, v_fn_518_, v_arg_519_, v_a_541_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_565_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_565_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_565_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_565_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
if (lean_obj_tag(v_a_543_) == 0)
{
uint8_t v_contextDependent_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v_contextDependent_547_ = lean_ctor_get_uint8(v_a_543_, 1);
lean_dec_ref_known(v_a_543_, 0);
v___x_548_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_526_, v_contextDependent_547_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_548_);
v___x_550_ = v___x_545_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
else
{
lean_object* v_e_x27_552_; lean_object* v_proof_553_; uint8_t v_contextDependent_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_564_; 
v_e_x27_552_ = lean_ctor_get(v_a_543_, 0);
v_proof_553_ = lean_ctor_get(v_a_543_, 1);
v_contextDependent_554_ = lean_ctor_get_uint8(v_a_543_, sizeof(void*)*2 + 1);
v_isSharedCheck_564_ = !lean_is_exclusive(v_a_543_);
if (v_isSharedCheck_564_ == 0)
{
v___x_556_ = v_a_543_;
v_isShared_557_ = v_isSharedCheck_564_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_proof_553_);
lean_inc(v_e_x27_552_);
lean_dec(v_a_543_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_564_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_e_x27_552_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v_proof_553_);
lean_ctor_set_uint8(v_reuseFailAlloc_563_, sizeof(void*)*2 + 1, v_contextDependent_554_);
v___x_559_ = v_reuseFailAlloc_563_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_561_; 
lean_ctor_set_uint8(v___x_559_, sizeof(void*)*2, v___x_526_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_559_);
v___x_561_ = v___x_545_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
}
}
else
{
return v___x_542_;
}
}
else
{
lean_dec_ref(v_arg_519_);
lean_dec_ref(v_fn_518_);
lean_dec_ref_known(v_e_504_, 2);
return v___x_540_;
}
}
else
{
uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_569_; 
lean_dec(v_a_530_);
lean_dec_ref(v_arg_519_);
lean_dec_ref_known(v_e_504_, 2);
lean_dec_ref(v_fn_518_);
v___x_566_ = 0;
v___x_567_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_526_, v___x_566_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_567_);
v___x_569_ = v___x_532_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
else
{
uint8_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec_ref(v___x_527_);
lean_dec_ref(v_arg_519_);
lean_dec_ref_known(v_e_504_, 2);
lean_dec_ref(v_fn_518_);
v___x_572_ = 0;
v___x_573_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_526_, v___x_572_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
}
}
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; 
lean_dec_ref(v_e_504_);
v___x_575_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
v___jp_515_:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
return v___x_517_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_504_ = stack[0].m_obj;
lean_object* v_a_505_ = stack[1].m_obj;
lean_object* v_a_506_ = stack[2].m_obj;
lean_object* v_a_507_ = stack[3].m_obj;
lean_object* v_a_508_ = stack[4].m_obj;
lean_object* v_a_509_ = stack[5].m_obj;
lean_object* v_a_510_ = stack[6].m_obj;
lean_object* v_a_511_ = stack[7].m_obj;
lean_object* v_a_512_ = stack[8].m_obj;
lean_object* v_a_513_ = stack[9].m_obj;
lean_object* v_res_577_;
v_res_577_ = l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(v_e_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
stack->m_obj
 = v_res_577_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___boxed(lean_object* v_e_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(v_e_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_a_582_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
return v_res_589_;
}
}
uint8_t l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(lean_object* v_declName_613_){
_start:
{
uint8_t v___y_615_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__10));
v___x_623_ = lean_name_eq(v_declName_613_, v___x_622_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__12));
v___x_625_ = lean_name_eq(v_declName_613_, v___x_624_);
v___y_615_ = v___x_625_;
goto v___jp_614_;
}
else
{
v___y_615_ = v___x_623_;
goto v___jp_614_;
}
v___jp_614_:
{
if (v___y_615_ == 0)
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__2));
v___x_617_ = lean_name_eq(v_declName_613_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; uint8_t v___x_619_; 
v___x_618_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__5));
v___x_619_ = lean_name_eq(v_declName_613_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_620_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__8));
v___x_621_ = lean_name_eq(v_declName_613_, v___x_620_);
return v___x_621_;
}
else
{
return v___x_619_;
}
}
else
{
return v___x_617_;
}
}
else
{
return v___y_615_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_613_ = stack[0].m_obj;
uint8_t v_res_626_;
v_res_626_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(v_declName_613_);
stack->m_num = v_res_626_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___boxed(lean_object* v_declName_627_){
_start:
{
uint8_t v_res_628_; lean_object* v_r_629_; 
v_res_628_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(v_declName_627_);
lean_dec(v_declName_627_);
v_r_629_ = lean_box(v_res_628_);
return v_r_629_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(lean_object* v_u_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = l_Lean_Expr_sort___override(v_u_630_);
v___x_634_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_633_, v___y_631_);
return v___x_634_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_630_ = stack[0].m_obj;
lean_object* v___y_631_ = stack[1].m_obj;
lean_object* v_res_635_;
v_res_635_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v_u_630_, v___y_631_);
stack->m_obj
 = v_res_635_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg___boxed(lean_object* v_u_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v_u_636_, v___y_637_);
lean_dec(v___y_637_);
return v_res_639_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(lean_object* v_u_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v_u_640_, v___y_645_);
return v___x_651_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_640_ = stack[0].m_obj;
lean_object* v___y_641_ = stack[1].m_obj;
lean_object* v___y_642_ = stack[2].m_obj;
lean_object* v___y_643_ = stack[3].m_obj;
lean_object* v___y_644_ = stack[4].m_obj;
lean_object* v___y_645_ = stack[5].m_obj;
lean_object* v___y_646_ = stack[6].m_obj;
lean_object* v___y_647_ = stack[7].m_obj;
lean_object* v___y_648_ = stack[8].m_obj;
lean_object* v___y_649_ = stack[9].m_obj;
lean_object* v_res_652_;
v_res_652_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v_u_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
stack->m_obj
 = v_res_652_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___boxed(lean_object* v_u_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v_u_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec_ref(v___y_657_);
lean_dec(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec(v___y_654_);
return v_res_664_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(lean_object* v_f_665_, lean_object* v_a_u2081_666_, lean_object* v_a_u2082_667_, lean_object* v_a_u2083_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v_f_665_, v_a_u2081_666_, v_a_u2082_667_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
if (lean_obj_tag(v___x_676_) == 0)
{
lean_object* v_a_677_; lean_object* v___x_678_; 
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref_known(v___x_676_, 1);
v___x_678_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_a_677_, v_a_u2083_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
return v___x_678_;
}
else
{
lean_dec_ref(v_a_u2083_668_);
return v___x_676_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_665_ = stack[0].m_obj;
lean_object* v_a_u2081_666_ = stack[1].m_obj;
lean_object* v_a_u2082_667_ = stack[2].m_obj;
lean_object* v_a_u2083_668_ = stack[3].m_obj;
lean_object* v___y_669_ = stack[4].m_obj;
lean_object* v___y_670_ = stack[5].m_obj;
lean_object* v___y_671_ = stack[6].m_obj;
lean_object* v___y_672_ = stack[7].m_obj;
lean_object* v___y_673_ = stack[8].m_obj;
lean_object* v___y_674_ = stack[9].m_obj;
lean_object* v_res_679_;
v_res_679_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v_f_665_, v_a_u2081_666_, v_a_u2082_667_, v_a_u2083_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_);
stack->m_obj
 = v_res_679_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg___boxed(lean_object* v_f_680_, lean_object* v_a_u2081_681_, lean_object* v_a_u2082_682_, lean_object* v_a_u2083_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v_f_680_, v_a_u2081_681_, v_a_u2082_682_, v_a_u2083_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
return v_res_691_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__4(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = lean_box(0);
v___x_701_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__3));
v___x_702_ = l_Lean_mkConst(v___x_701_, v___x_700_);
return v___x_702_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__8(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_710_ = lean_box(0);
v___x_711_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__7));
v___x_712_ = l_Lean_mkConst(v___x_711_, v___x_710_);
return v___x_712_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__11(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = lean_box(0);
v___x_719_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__10));
v___x_720_ = l_Lean_mkConst(v___x_719_, v___x_718_);
return v___x_720_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__16(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = lean_box(0);
v___x_730_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__15));
v___x_731_ = l_Lean_mkConst(v___x_730_, v___x_729_);
return v___x_731_;
}
}
lean_object* l_Lean_Meta_Grind_NormSym_simpEq(lean_object* v_e_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_754_ = l_Lean_Expr_cleanupAnnotations(v_e_740_);
v___x_755_ = l_Lean_Expr_isApp(v___x_754_);
if (v___x_755_ == 0)
{
lean_dec_ref(v___x_754_);
goto v___jp_751_;
}
else
{
lean_object* v_arg_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v_arg_756_ = lean_ctor_get(v___x_754_, 1);
lean_inc_ref(v_arg_756_);
v___x_757_ = l_Lean_Expr_appFnCleanup___redArg(v___x_754_);
v___x_758_ = l_Lean_Expr_isApp(v___x_757_);
if (v___x_758_ == 0)
{
lean_dec_ref(v___x_757_);
lean_dec_ref(v_arg_756_);
goto v___jp_751_;
}
else
{
lean_object* v_arg_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v_arg_759_ = lean_ctor_get(v___x_757_, 1);
lean_inc_ref(v_arg_759_);
v___x_760_ = l_Lean_Expr_appFnCleanup___redArg(v___x_757_);
v___x_761_ = l_Lean_Expr_isApp(v___x_760_);
if (v___x_761_ == 0)
{
lean_dec_ref(v___x_760_);
lean_dec_ref(v_arg_759_);
lean_dec_ref(v_arg_756_);
goto v___jp_751_;
}
else
{
lean_object* v_arg_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v_arg_762_ = lean_ctor_get(v___x_760_, 1);
lean_inc_ref(v_arg_762_);
v___x_763_ = l_Lean_Expr_appFnCleanup___redArg(v___x_760_);
v___x_764_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__1));
v___x_765_ = l_Lean_Expr_isConstOf(v___x_763_, v___x_764_);
if (v___x_765_ == 0)
{
lean_dec_ref(v___x_763_);
lean_dec_ref(v_arg_762_);
lean_dec_ref(v_arg_759_);
lean_dec_ref(v_arg_756_);
goto v___jp_751_;
}
else
{
lean_object* v___x_766_; 
lean_inc_ref(v_arg_762_);
v___x_766_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_762_, v_a_747_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_940_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_940_ == 0)
{
v___x_769_ = v___x_766_;
v_isShared_770_ = v_isSharedCheck_940_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_766_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_940_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
uint8_t v___y_772_; uint8_t v___y_773_; lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_839_ = l_Lean_Expr_cleanupAnnotations(v_a_767_);
v___x_840_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__5));
v___x_841_ = l_Lean_Expr_isConstOf(v___x_839_, v___x_840_);
lean_dec_ref(v___x_839_);
if (v___x_841_ == 0)
{
size_t v___x_842_; size_t v___x_843_; uint8_t v___x_844_; 
lean_del_object(v___x_769_);
v___x_842_ = lean_ptr_addr(v_arg_759_);
v___x_843_ = lean_ptr_addr(v_arg_756_);
v___x_844_ = lean_usize_dec_eq(v___x_842_, v___x_843_);
if (v___x_844_ == 0)
{
uint8_t v___x_845_; 
lean_dec_ref(v___x_763_);
lean_dec_ref(v_arg_762_);
lean_inc_ref(v_arg_756_);
v___x_845_ = l_Lean_Expr_isTrue(v_arg_756_);
if (v___x_845_ == 0)
{
uint8_t v___x_846_; 
v___x_846_ = l_Lean_Expr_isFalse(v_arg_756_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec_ref(v_arg_759_);
v___x_847_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_847_, 0, v___x_846_);
lean_ctor_set_uint8(v___x_847_, 1, v___x_846_);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
else
{
lean_object* v___x_849_; 
lean_inc_ref(v_arg_759_);
v___x_849_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_759_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_860_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_860_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_860_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_860_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_854_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpEq___closed__8, &l_Lean_Meta_Grind_NormSym_simpEq___closed__8_once, _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__8);
v___x_855_ = l_Lean_Expr_app___override(v___x_854_, v_arg_759_);
v___x_856_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_856_, 0, v_a_850_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*2, v___x_845_);
lean_ctor_set_uint8(v___x_856_, sizeof(void*)*2 + 1, v___x_845_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_856_);
v___x_858_ = v___x_852_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
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
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_dec_ref(v_arg_759_);
v_a_861_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_849_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_849_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
else
{
lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec_ref(v_arg_756_);
v___x_869_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpEq___closed__11, &l_Lean_Meta_Grind_NormSym_simpEq___closed__11_once, _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__11);
lean_inc_ref(v_arg_759_);
v___x_870_ = l_Lean_Expr_app___override(v___x_869_, v_arg_759_);
v___x_871_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_871_, 0, v_arg_759_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
lean_ctor_set_uint8(v___x_871_, sizeof(void*)*2, v___x_765_);
lean_ctor_set_uint8(v___x_871_, sizeof(void*)*2 + 1, v___x_844_);
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
return v___x_872_;
}
}
else
{
lean_object* v___x_873_; 
lean_dec_ref(v_arg_756_);
v___x_873_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_744_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_886_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_886_ == 0)
{
v___x_876_ = v___x_873_;
v_isShared_877_ = v_isSharedCheck_886_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_886_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_878_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__13));
v___x_879_ = l_Lean_Expr_constLevels_x21(v___x_763_);
lean_dec_ref(v___x_763_);
v___x_880_ = l_Lean_mkConst(v___x_878_, v___x_879_);
v___x_881_ = l_Lean_mkAppB(v___x_880_, v_arg_762_, v_arg_759_);
v___x_882_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_882_, 0, v_a_874_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
lean_ctor_set_uint8(v___x_882_, sizeof(void*)*2, v___x_765_);
lean_ctor_set_uint8(v___x_882_, sizeof(void*)*2 + 1, v___x_841_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_882_);
v___x_884_ = v___x_876_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v___x_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_dec_ref(v___x_763_);
lean_dec_ref(v_arg_762_);
lean_dec_ref(v_arg_759_);
v_a_887_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_873_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_873_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
else
{
lean_object* v___x_895_; 
v___x_895_ = l_Lean_Expr_getAppFn(v_arg_756_);
if (lean_obj_tag(v___x_895_) == 4)
{
lean_object* v_declName_896_; uint8_t v___y_898_; lean_object* v___y_899_; uint8_t v___y_900_; lean_object* v___x_923_; uint8_t v___y_925_; uint8_t v___x_935_; 
v_declName_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_declName_896_);
lean_dec_ref_known(v___x_895_, 2);
v___x_923_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__18));
v___x_935_ = lean_name_eq(v_declName_896_, v___x_923_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_936_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__20));
v___x_937_ = lean_name_eq(v_declName_896_, v___x_936_);
v___y_925_ = v___x_937_;
goto v___jp_924_;
}
else
{
v___y_925_ = v___x_935_;
goto v___jp_924_;
}
v___jp_897_:
{
if (v___y_900_ == 0)
{
uint8_t v___x_901_; 
v___x_901_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(v___y_899_);
lean_dec(v___y_899_);
if (v___x_901_ == 0)
{
uint8_t v___x_902_; 
v___x_902_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(v_declName_896_);
lean_dec(v_declName_896_);
v___y_772_ = v___y_900_;
v___y_773_ = v___x_902_;
goto v___jp_771_;
}
else
{
lean_dec(v_declName_896_);
v___y_772_ = v___y_900_;
v___y_773_ = v___x_901_;
goto v___jp_771_;
}
}
else
{
lean_object* v___x_903_; 
lean_dec(v___y_899_);
lean_dec(v_declName_896_);
lean_del_object(v___x_769_);
lean_inc_ref(v_arg_759_);
lean_inc_ref(v_arg_756_);
v___x_903_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v___x_763_, v_arg_762_, v_arg_756_, v_arg_759_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_914_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_914_ == 0)
{
v___x_906_ = v___x_903_;
v_isShared_907_ = v_isSharedCheck_914_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_903_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_914_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_912_; 
v___x_908_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpEq___closed__16, &l_Lean_Meta_Grind_NormSym_simpEq___closed__16_once, _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__16);
v___x_909_ = l_Lean_mkAppB(v___x_908_, v_arg_759_, v_arg_756_);
v___x_910_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_910_, 0, v_a_904_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*2, v___y_898_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*2 + 1, v___y_898_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 0, v___x_910_);
v___x_912_ = v___x_906_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec_ref(v_arg_759_);
lean_dec_ref(v_arg_756_);
v_a_915_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_903_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_903_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
v___jp_924_:
{
if (v___y_925_ == 0)
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_Expr_getAppFn(v_arg_759_);
if (lean_obj_tag(v___x_926_) == 4)
{
lean_object* v_declName_927_; uint8_t v___x_928_; 
v_declName_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_declName_927_);
lean_dec_ref_known(v___x_926_, 2);
v___x_928_ = lean_name_eq(v_declName_927_, v___x_923_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_929_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__20));
v___x_930_ = lean_name_eq(v_declName_927_, v___x_929_);
v___y_898_ = v___y_925_;
v___y_899_ = v_declName_927_;
v___y_900_ = v___x_930_;
goto v___jp_897_;
}
else
{
v___y_898_ = v___y_925_;
v___y_899_ = v_declName_927_;
v___y_900_ = v___x_928_;
goto v___jp_897_;
}
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec_ref(v___x_926_);
lean_dec(v_declName_896_);
lean_del_object(v___x_769_);
lean_dec_ref(v___x_763_);
lean_dec_ref(v_arg_762_);
lean_dec_ref(v_arg_759_);
lean_dec_ref(v_arg_756_);
v___x_931_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_931_, 0, v___y_925_);
lean_ctor_set_uint8(v___x_931_, 1, v___y_925_);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
return v___x_932_;
}
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; 
lean_dec(v_declName_896_);
lean_del_object(v___x_769_);
lean_dec_ref(v___x_763_);
lean_dec_ref(v_arg_762_);
lean_dec_ref(v_arg_759_);
lean_dec_ref(v_arg_756_);
v___x_933_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
return v___x_934_;
}
}
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; 
lean_dec_ref(v___x_895_);
lean_del_object(v___x_769_);
lean_dec_ref(v___x_763_);
lean_dec_ref(v_arg_762_);
lean_dec_ref(v_arg_759_);
lean_dec_ref(v_arg_756_);
v___x_938_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
return v___x_939_;
}
}
v___jp_771_:
{
if (v___y_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_776_; 
lean_dec_ref(v___x_763_);
lean_dec_ref(v_arg_762_);
lean_dec_ref(v_arg_759_);
lean_dec_ref(v_arg_756_);
v___x_774_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_774_, 0, v___y_773_);
lean_ctor_set_uint8(v___x_774_, 1, v___y_773_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 0, v___x_774_);
v___x_776_ = v___x_769_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_774_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
else
{
lean_object* v___x_778_; 
lean_del_object(v___x_769_);
v___x_778_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_744_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_779_);
lean_dec_ref_known(v___x_778_, 1);
v___x_780_ = lean_box(0);
v___x_781_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___redArg(v___x_780_, v_a_745_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_783_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_781_, 1);
lean_inc(v_a_779_);
lean_inc_ref(v_arg_759_);
lean_inc_ref(v_arg_762_);
lean_inc_ref(v___x_763_);
v___x_783_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v___x_763_, v_arg_762_, v_arg_759_, v_a_779_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_785_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v___x_783_, 1);
lean_inc_ref(v_arg_756_);
lean_inc_ref(v___x_763_);
v___x_785_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v___x_763_, v_arg_762_, v_arg_756_, v_a_779_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_787_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
v___x_787_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v___x_763_, v_a_782_, v_a_784_, v_a_786_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_798_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_798_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_798_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_798_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_792_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpEq___closed__4, &l_Lean_Meta_Grind_NormSym_simpEq___closed__4_once, _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__4);
v___x_793_ = l_Lean_mkAppB(v___x_792_, v_arg_759_, v_arg_756_);
v___x_794_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_794_, 0, v_a_788_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
lean_ctor_set_uint8(v___x_794_, sizeof(void*)*2, v___y_772_);
lean_ctor_set_uint8(v___x_794_, sizeof(void*)*2 + 1, v___y_772_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_794_);
v___x_796_ = v___x_790_;
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
lean_dec_ref(v_arg_759_);
lean_dec_ref(v_arg_756_);
v_a_799_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_787_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_787_);
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
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec(v_a_784_);
lean_dec(v_a_782_);
lean_dec_ref(v___x_763_);
lean_dec_ref(v_arg_759_);
lean_dec_ref(v_arg_756_);
v_a_807_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_785_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_785_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec(v_a_782_);
lean_dec(v_a_779_);
lean_dec_ref(v___x_763_);
lean_dec_ref(v_arg_762_);
lean_dec_ref(v_arg_759_);
lean_dec_ref(v_arg_756_);
v_a_815_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_783_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_783_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec(v_a_779_);
lean_dec_ref(v___x_763_);
lean_dec_ref(v_arg_762_);
lean_dec_ref(v_arg_759_);
lean_dec_ref(v_arg_756_);
v_a_823_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_781_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_781_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec_ref(v___x_763_);
lean_dec_ref(v_arg_762_);
lean_dec_ref(v_arg_759_);
lean_dec_ref(v_arg_756_);
v_a_831_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_778_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_778_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec_ref(v___x_763_);
lean_dec_ref(v_arg_762_);
lean_dec_ref(v_arg_759_);
lean_dec_ref(v_arg_756_);
v_a_941_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_766_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_766_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
}
}
v___jp_751_:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_NormSym_simpEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_740_ = stack[0].m_obj;
lean_object* v_a_741_ = stack[1].m_obj;
lean_object* v_a_742_ = stack[2].m_obj;
lean_object* v_a_743_ = stack[3].m_obj;
lean_object* v_a_744_ = stack[4].m_obj;
lean_object* v_a_745_ = stack[5].m_obj;
lean_object* v_a_746_ = stack[6].m_obj;
lean_object* v_a_747_ = stack[7].m_obj;
lean_object* v_a_748_ = stack[8].m_obj;
lean_object* v_a_749_ = stack[9].m_obj;
lean_object* v_res_949_;
v_res_949_ = l_Lean_Meta_Grind_NormSym_simpEq(v_e_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
stack->m_obj
 = v_res_949_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpEq___boxed(lean_object* v_e_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_Meta_Grind_NormSym_simpEq(v_e_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
return v_res_961_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1(lean_object* v_f_962_, lean_object* v_a_u2081_963_, lean_object* v_a_u2082_964_, lean_object* v_a_u2083_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v_f_962_, v_a_u2081_963_, v_a_u2082_964_, v_a_u2083_965_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
return v___x_976_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_962_ = stack[0].m_obj;
lean_object* v_a_u2081_963_ = stack[1].m_obj;
lean_object* v_a_u2082_964_ = stack[2].m_obj;
lean_object* v_a_u2083_965_ = stack[3].m_obj;
lean_object* v___y_966_ = stack[4].m_obj;
lean_object* v___y_967_ = stack[5].m_obj;
lean_object* v___y_968_ = stack[6].m_obj;
lean_object* v___y_969_ = stack[7].m_obj;
lean_object* v___y_970_ = stack[8].m_obj;
lean_object* v___y_971_ = stack[9].m_obj;
lean_object* v___y_972_ = stack[10].m_obj;
lean_object* v___y_973_ = stack[11].m_obj;
lean_object* v___y_974_ = stack[12].m_obj;
lean_object* v_res_977_;
v_res_977_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1(v_f_962_, v_a_u2081_963_, v_a_u2082_964_, v_a_u2083_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
stack->m_obj
 = v_res_977_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___boxed(lean_object* v_f_978_, lean_object* v_a_u2081_979_, lean_object* v_a_u2082_980_, lean_object* v_a_u2083_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1(v_f_978_, v_a_u2081_979_, v_a_u2082_980_, v_a_u2083_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
return v_res_992_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___redArg(lean_object* v_f_993_, lean_object* v_a_u2081_994_, lean_object* v_a_u2082_995_, lean_object* v_a_u2083_996_, lean_object* v_a_u2084_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v_f_993_, v_a_u2081_994_, v_a_u2082_995_, v_a_u2083_996_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___x_1007_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_a_1006_, v_a_u2084_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
return v___x_1007_;
}
else
{
lean_dec_ref(v_a_u2084_997_);
return v___x_1005_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_993_ = stack[0].m_obj;
lean_object* v_a_u2081_994_ = stack[1].m_obj;
lean_object* v_a_u2082_995_ = stack[2].m_obj;
lean_object* v_a_u2083_996_ = stack[3].m_obj;
lean_object* v_a_u2084_997_ = stack[4].m_obj;
lean_object* v___y_998_ = stack[5].m_obj;
lean_object* v___y_999_ = stack[6].m_obj;
lean_object* v___y_1000_ = stack[7].m_obj;
lean_object* v___y_1001_ = stack[8].m_obj;
lean_object* v___y_1002_ = stack[9].m_obj;
lean_object* v___y_1003_ = stack[10].m_obj;
lean_object* v_res_1008_;
v_res_1008_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___redArg(v_f_993_, v_a_u2081_994_, v_a_u2082_995_, v_a_u2083_996_, v_a_u2084_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
stack->m_obj
 = v_res_1008_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___redArg___boxed(lean_object* v_f_1009_, lean_object* v_a_u2081_1010_, lean_object* v_a_u2082_1011_, lean_object* v_a_u2083_1012_, lean_object* v_a_u2084_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___redArg(v_f_1009_, v_a_u2081_1010_, v_a_u2082_1011_, v_a_u2083_1012_, v_a_u2084_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
return v_res_1021_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0(lean_object* v_f_1022_, lean_object* v_a_u2081_1023_, lean_object* v_a_u2082_1024_, lean_object* v_a_u2083_1025_, lean_object* v_a_u2084_1026_, lean_object* v_a_u2085_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___redArg(v_f_1022_, v_a_u2081_1023_, v_a_u2082_1024_, v_a_u2083_1025_, v_a_u2084_1026_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1040_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
lean_dec_ref_known(v___x_1038_, 1);
v___x_1040_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_a_1039_, v_a_u2085_1027_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
return v___x_1040_;
}
else
{
lean_dec_ref(v_a_u2085_1027_);
return v___x_1038_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1022_ = stack[0].m_obj;
lean_object* v_a_u2081_1023_ = stack[1].m_obj;
lean_object* v_a_u2082_1024_ = stack[2].m_obj;
lean_object* v_a_u2083_1025_ = stack[3].m_obj;
lean_object* v_a_u2084_1026_ = stack[4].m_obj;
lean_object* v_a_u2085_1027_ = stack[5].m_obj;
lean_object* v___y_1028_ = stack[6].m_obj;
lean_object* v___y_1029_ = stack[7].m_obj;
lean_object* v___y_1030_ = stack[8].m_obj;
lean_object* v___y_1031_ = stack[9].m_obj;
lean_object* v___y_1032_ = stack[10].m_obj;
lean_object* v___y_1033_ = stack[11].m_obj;
lean_object* v___y_1034_ = stack[12].m_obj;
lean_object* v___y_1035_ = stack[13].m_obj;
lean_object* v___y_1036_ = stack[14].m_obj;
lean_object* v_res_1041_;
v_res_1041_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0(v_f_1022_, v_a_u2081_1023_, v_a_u2082_1024_, v_a_u2083_1025_, v_a_u2084_1026_, v_a_u2085_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
stack->m_obj
 = v_res_1041_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___boxed(lean_object* v_f_1042_, lean_object* v_a_u2081_1043_, lean_object* v_a_u2082_1044_, lean_object* v_a_u2083_1045_, lean_object* v_a_u2084_1046_, lean_object* v_a_u2085_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0(v_f_1042_, v_a_u2081_1043_, v_a_u2082_1044_, v_a_u2083_1045_, v_a_u2084_1046_, v_a_u2085_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
return v_res_1058_;
}
}
lean_object* l_Lean_Meta_Grind_NormSym_simpDIte(lean_object* v_e_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1082_ = l_Lean_Expr_cleanupAnnotations(v_e_1068_);
v___x_1083_ = l_Lean_Expr_isApp(v___x_1082_);
if (v___x_1083_ == 0)
{
lean_dec_ref(v___x_1082_);
goto v___jp_1079_;
}
else
{
lean_object* v_arg_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v_arg_1084_ = lean_ctor_get(v___x_1082_, 1);
lean_inc_ref(v_arg_1084_);
v___x_1085_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1082_);
v___x_1086_ = l_Lean_Expr_isApp(v___x_1085_);
if (v___x_1086_ == 0)
{
lean_dec_ref(v___x_1085_);
lean_dec_ref(v_arg_1084_);
goto v___jp_1079_;
}
else
{
lean_object* v_arg_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v_arg_1087_ = lean_ctor_get(v___x_1085_, 1);
lean_inc_ref(v_arg_1087_);
v___x_1088_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1085_);
v___x_1089_ = l_Lean_Expr_isApp(v___x_1088_);
if (v___x_1089_ == 0)
{
lean_dec_ref(v___x_1088_);
lean_dec_ref(v_arg_1087_);
lean_dec_ref(v_arg_1084_);
goto v___jp_1079_;
}
else
{
lean_object* v_arg_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; 
v_arg_1090_ = lean_ctor_get(v___x_1088_, 1);
lean_inc_ref(v_arg_1090_);
v___x_1091_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1088_);
v___x_1092_ = l_Lean_Expr_isApp(v___x_1091_);
if (v___x_1092_ == 0)
{
lean_dec_ref(v___x_1091_);
lean_dec_ref(v_arg_1090_);
lean_dec_ref(v_arg_1087_);
lean_dec_ref(v_arg_1084_);
goto v___jp_1079_;
}
else
{
lean_object* v_arg_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v_arg_1093_ = lean_ctor_get(v___x_1091_, 1);
lean_inc_ref(v_arg_1093_);
v___x_1094_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1091_);
v___x_1095_ = l_Lean_Expr_isApp(v___x_1094_);
if (v___x_1095_ == 0)
{
lean_dec_ref(v___x_1094_);
lean_dec_ref(v_arg_1093_);
lean_dec_ref(v_arg_1090_);
lean_dec_ref(v_arg_1087_);
lean_dec_ref(v_arg_1084_);
goto v___jp_1079_;
}
else
{
lean_object* v_arg_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v_arg_1096_ = lean_ctor_get(v___x_1094_, 1);
lean_inc_ref(v_arg_1096_);
v___x_1097_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1094_);
v___x_1098_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpDIte___closed__1));
v___x_1099_ = l_Lean_Expr_isConstOf(v___x_1097_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_dec_ref(v___x_1097_);
lean_dec_ref(v_arg_1096_);
lean_dec_ref(v_arg_1093_);
lean_dec_ref(v_arg_1090_);
lean_dec_ref(v_arg_1087_);
lean_dec_ref(v_arg_1084_);
goto v___jp_1079_;
}
else
{
if (lean_obj_tag(v_arg_1087_) == 6)
{
lean_object* v_body_1100_; uint8_t v___x_1101_; 
v_body_1100_ = lean_ctor_get(v_arg_1087_, 2);
lean_inc_ref(v_body_1100_);
lean_dec_ref_known(v_arg_1087_, 3);
v___x_1101_ = l_Lean_Expr_hasLooseBVars(v_body_1100_);
if (v___x_1101_ == 0)
{
if (lean_obj_tag(v_arg_1084_) == 6)
{
lean_object* v_body_1102_; uint8_t v___x_1103_; 
v_body_1102_ = lean_ctor_get(v_arg_1084_, 2);
lean_inc_ref(v_body_1102_);
lean_dec_ref_known(v_arg_1084_, 3);
v___x_1103_ = l_Lean_Expr_hasLooseBVars(v_body_1102_);
if (v___x_1103_ == 0)
{
lean_object* v_us_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v_us_1104_ = l_Lean_Expr_constLevels_x21(v___x_1097_);
lean_dec_ref(v___x_1097_);
v___x_1105_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpDIte___closed__3));
lean_inc(v_us_1104_);
v___x_1106_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v___x_1105_, v_us_1104_, v_a_1073_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; lean_object* v___x_1108_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
lean_dec_ref_known(v___x_1106_, 1);
lean_inc_ref(v_body_1102_);
lean_inc_ref(v_body_1100_);
lean_inc_ref(v_arg_1090_);
lean_inc_ref(v_arg_1093_);
lean_inc_ref(v_arg_1096_);
v___x_1108_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0(v_a_1107_, v_arg_1096_, v_arg_1093_, v_arg_1090_, v_body_1100_, v_body_1102_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1120_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1111_ = v___x_1108_;
v_isShared_1112_ = v_isSharedCheck_1120_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1108_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1120_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1113_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpDIte___closed__5));
v___x_1114_ = l_Lean_mkConst(v___x_1113_, v_us_1104_);
v___x_1115_ = l_Lean_mkApp5(v___x_1114_, v_arg_1093_, v_arg_1096_, v_body_1100_, v_body_1102_, v_arg_1090_);
v___x_1116_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1116_, 0, v_a_1109_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*2, v___x_1103_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*2 + 1, v___x_1103_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 0, v___x_1116_);
v___x_1118_ = v___x_1111_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec(v_us_1104_);
lean_dec_ref(v_body_1102_);
lean_dec_ref(v_body_1100_);
lean_dec_ref(v_arg_1096_);
lean_dec_ref(v_arg_1093_);
lean_dec_ref(v_arg_1090_);
v_a_1121_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1108_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1108_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec(v_us_1104_);
lean_dec_ref(v_body_1102_);
lean_dec_ref(v_body_1100_);
lean_dec_ref(v_arg_1096_);
lean_dec_ref(v_arg_1093_);
lean_dec_ref(v_arg_1090_);
v_a_1129_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1106_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1106_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_dec_ref(v_body_1102_);
lean_dec_ref(v_body_1100_);
lean_dec_ref(v___x_1097_);
lean_dec_ref(v_arg_1096_);
lean_dec_ref(v_arg_1093_);
lean_dec_ref(v_arg_1090_);
v___x_1137_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1137_, 0, v___x_1101_);
lean_ctor_set_uint8(v___x_1137_, 1, v___x_1101_);
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
return v___x_1138_;
}
}
else
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec_ref(v_body_1100_);
lean_dec_ref(v___x_1097_);
lean_dec_ref(v_arg_1096_);
lean_dec_ref(v_arg_1093_);
lean_dec_ref(v_arg_1090_);
lean_dec_ref(v_arg_1084_);
v___x_1139_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1139_, 0, v___x_1101_);
lean_ctor_set_uint8(v___x_1139_, 1, v___x_1101_);
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
return v___x_1140_;
}
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_dec_ref(v_body_1100_);
lean_dec_ref(v___x_1097_);
lean_dec_ref(v_arg_1096_);
lean_dec_ref(v_arg_1093_);
lean_dec_ref(v_arg_1090_);
lean_dec_ref(v_arg_1084_);
v___x_1141_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
return v___x_1142_;
}
}
else
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec_ref(v___x_1097_);
lean_dec_ref(v_arg_1096_);
lean_dec_ref(v_arg_1093_);
lean_dec_ref(v_arg_1090_);
lean_dec_ref(v_arg_1087_);
lean_dec_ref(v_arg_1084_);
v___x_1143_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
return v___x_1144_;
}
}
}
}
}
}
}
v___jp_1079_:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
return v___x_1081_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_NormSym_simpDIte_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1068_ = stack[0].m_obj;
lean_object* v_a_1069_ = stack[1].m_obj;
lean_object* v_a_1070_ = stack[2].m_obj;
lean_object* v_a_1071_ = stack[3].m_obj;
lean_object* v_a_1072_ = stack[4].m_obj;
lean_object* v_a_1073_ = stack[5].m_obj;
lean_object* v_a_1074_ = stack[6].m_obj;
lean_object* v_a_1075_ = stack[7].m_obj;
lean_object* v_a_1076_ = stack[8].m_obj;
lean_object* v_a_1077_ = stack[9].m_obj;
lean_object* v_res_1145_;
v_res_1145_ = l_Lean_Meta_Grind_NormSym_simpDIte(v_e_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
stack->m_obj
 = v_res_1145_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpDIte___boxed(lean_object* v_e_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_Meta_Grind_NormSym_simpDIte(v_e_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
return v_res_1157_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0(lean_object* v_f_1158_, lean_object* v_a_u2081_1159_, lean_object* v_a_u2082_1160_, lean_object* v_a_u2083_1161_, lean_object* v_a_u2084_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___redArg(v_f_1158_, v_a_u2081_1159_, v_a_u2082_1160_, v_a_u2083_1161_, v_a_u2084_1162_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
return v___x_1173_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1158_ = stack[0].m_obj;
lean_object* v_a_u2081_1159_ = stack[1].m_obj;
lean_object* v_a_u2082_1160_ = stack[2].m_obj;
lean_object* v_a_u2083_1161_ = stack[3].m_obj;
lean_object* v_a_u2084_1162_ = stack[4].m_obj;
lean_object* v___y_1163_ = stack[5].m_obj;
lean_object* v___y_1164_ = stack[6].m_obj;
lean_object* v___y_1165_ = stack[7].m_obj;
lean_object* v___y_1166_ = stack[8].m_obj;
lean_object* v___y_1167_ = stack[9].m_obj;
lean_object* v___y_1168_ = stack[10].m_obj;
lean_object* v___y_1169_ = stack[11].m_obj;
lean_object* v___y_1170_ = stack[12].m_obj;
lean_object* v___y_1171_ = stack[13].m_obj;
lean_object* v_res_1174_;
v_res_1174_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0(v_f_1158_, v_a_u2081_1159_, v_a_u2082_1160_, v_a_u2083_1161_, v_a_u2084_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
stack->m_obj
 = v_res_1174_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0___boxed(lean_object* v_f_1175_, lean_object* v_a_u2081_1176_, lean_object* v_a_u2082_1177_, lean_object* v_a_u2083_1178_, lean_object* v_a_u2084_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0_spec__0(v_f_1175_, v_a_u2081_1176_, v_a_u2082_1177_, v_a_u2083_1178_, v_a_u2084_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
return v_res_1190_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(lean_object* v_x_1191_, uint8_t v_bi_1192_, lean_object* v_t_1193_, lean_object* v_b_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___y_1203_; lean_object* v___x_1206_; uint8_t v_debug_1207_; 
v___x_1206_ = lean_st_ref_get(v___y_1196_);
v_debug_1207_ = lean_ctor_get_uint8(v___x_1206_, sizeof(void*)*12);
lean_dec(v___x_1206_);
if (v_debug_1207_ == 0)
{
v___y_1203_ = v___y_1196_;
goto v___jp_1202_;
}
else
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1193_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v___x_1209_; 
lean_dec_ref_known(v___x_1208_, 1);
v___x_1209_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_dec_ref_known(v___x_1209_, 1);
v___y_1203_ = v___y_1196_;
goto v___jp_1202_;
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec_ref(v_b_1194_);
lean_dec_ref(v_t_1193_);
lean_dec(v_x_1191_);
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec_ref(v_b_1194_);
lean_dec_ref(v_t_1193_);
lean_dec(v_x_1191_);
v_a_1218_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1208_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1208_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
v___jp_1202_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = l_Lean_Expr_lam___override(v_x_1191_, v_t_1193_, v_b_1194_, v_bi_1192_);
v___x_1205_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1204_, v___y_1203_);
return v___x_1205_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1191_ = stack[0].m_obj;
uint8_t v_bi_1192_ = stack[1].m_num;
lean_object* v_t_1193_ = stack[2].m_obj;
lean_object* v_b_1194_ = stack[3].m_obj;
lean_object* v___y_1195_ = stack[4].m_obj;
lean_object* v___y_1196_ = stack[5].m_obj;
lean_object* v___y_1197_ = stack[6].m_obj;
lean_object* v___y_1198_ = stack[7].m_obj;
lean_object* v___y_1199_ = stack[8].m_obj;
lean_object* v___y_1200_ = stack[9].m_obj;
lean_object* v_res_1226_;
v_res_1226_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_x_1191_, v_bi_1192_, v_t_1193_, v_b_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
stack->m_obj
 = v_res_1226_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg___boxed(lean_object* v_x_1227_, lean_object* v_bi_1228_, lean_object* v_t_1229_, lean_object* v_b_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
uint8_t v_bi_boxed_1238_; lean_object* v_res_1239_; 
v_bi_boxed_1238_ = lean_unbox(v_bi_1228_);
v_res_1239_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_x_1227_, v_bi_boxed_1238_, v_t_1229_, v_b_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
return v_res_1239_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0(lean_object* v_x_1240_, uint8_t v_bi_1241_, lean_object* v_t_1242_, lean_object* v_b_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_x_1240_, v_bi_1241_, v_t_1242_, v_b_1243_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
return v___x_1254_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1240_ = stack[0].m_obj;
uint8_t v_bi_1241_ = stack[1].m_num;
lean_object* v_t_1242_ = stack[2].m_obj;
lean_object* v_b_1243_ = stack[3].m_obj;
lean_object* v___y_1244_ = stack[4].m_obj;
lean_object* v___y_1245_ = stack[5].m_obj;
lean_object* v___y_1246_ = stack[6].m_obj;
lean_object* v___y_1247_ = stack[7].m_obj;
lean_object* v___y_1248_ = stack[8].m_obj;
lean_object* v___y_1249_ = stack[9].m_obj;
lean_object* v___y_1250_ = stack[10].m_obj;
lean_object* v___y_1251_ = stack[11].m_obj;
lean_object* v___y_1252_ = stack[12].m_obj;
lean_object* v_res_1255_;
v_res_1255_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0(v_x_1240_, v_bi_1241_, v_t_1242_, v_b_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
stack->m_obj
 = v_res_1255_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___boxed(lean_object* v_x_1256_, lean_object* v_bi_1257_, lean_object* v_t_1258_, lean_object* v_b_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
uint8_t v_bi_boxed_1270_; lean_object* v_res_1271_; 
v_bi_boxed_1270_ = lean_unbox(v_bi_1257_);
v_res_1271_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0(v_x_1256_, v_bi_boxed_1270_, v_t_1258_, v_b_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
return v_res_1271_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(lean_object* v_idx_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = l_Lean_Expr_bvar___override(v_idx_1272_);
v___x_1276_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1275_, v___y_1273_);
return v___x_1276_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_idx_1272_ = stack[0].m_obj;
lean_object* v___y_1273_ = stack[1].m_obj;
lean_object* v_res_1277_;
v_res_1277_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(v_idx_1272_, v___y_1273_);
stack->m_obj
 = v_res_1277_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg___boxed(lean_object* v_idx_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(v_idx_1278_, v___y_1279_);
lean_dec(v___y_1279_);
return v_res_1281_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1(lean_object* v_idx_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(v_idx_1282_, v___y_1287_);
return v___x_1293_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_idx_1282_ = stack[0].m_obj;
lean_object* v___y_1283_ = stack[1].m_obj;
lean_object* v___y_1284_ = stack[2].m_obj;
lean_object* v___y_1285_ = stack[3].m_obj;
lean_object* v___y_1286_ = stack[4].m_obj;
lean_object* v___y_1287_ = stack[5].m_obj;
lean_object* v___y_1288_ = stack[6].m_obj;
lean_object* v___y_1289_ = stack[7].m_obj;
lean_object* v___y_1290_ = stack[8].m_obj;
lean_object* v___y_1291_ = stack[9].m_obj;
lean_object* v_res_1294_;
v_res_1294_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1(v_idx_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
stack->m_obj
 = v_res_1294_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___boxed(lean_object* v_idx_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1(v_idx_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
return v_res_1306_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(lean_object* v_x_1307_, uint8_t v_bi_1308_, lean_object* v_t_1309_, lean_object* v_b_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___y_1319_; lean_object* v___x_1322_; uint8_t v_debug_1323_; 
v___x_1322_ = lean_st_ref_get(v___y_1312_);
v_debug_1323_ = lean_ctor_get_uint8(v___x_1322_, sizeof(void*)*12);
lean_dec(v___x_1322_);
if (v_debug_1323_ == 0)
{
v___y_1319_ = v___y_1312_;
goto v___jp_1318_;
}
else
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1309_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v___x_1325_; 
lean_dec_ref_known(v___x_1324_, 1);
v___x_1325_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_dec_ref_known(v___x_1325_, 1);
v___y_1319_ = v___y_1312_;
goto v___jp_1318_;
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec_ref(v_b_1310_);
lean_dec_ref(v_t_1309_);
lean_dec(v_x_1307_);
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1325_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1325_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec_ref(v_b_1310_);
lean_dec_ref(v_t_1309_);
lean_dec(v_x_1307_);
v_a_1334_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1324_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1324_);
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
v___jp_1318_:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = l_Lean_Expr_forallE___override(v_x_1307_, v_t_1309_, v_b_1310_, v_bi_1308_);
v___x_1321_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1320_, v___y_1319_);
return v___x_1321_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1307_ = stack[0].m_obj;
uint8_t v_bi_1308_ = stack[1].m_num;
lean_object* v_t_1309_ = stack[2].m_obj;
lean_object* v_b_1310_ = stack[3].m_obj;
lean_object* v___y_1311_ = stack[4].m_obj;
lean_object* v___y_1312_ = stack[5].m_obj;
lean_object* v___y_1313_ = stack[6].m_obj;
lean_object* v___y_1314_ = stack[7].m_obj;
lean_object* v___y_1315_ = stack[8].m_obj;
lean_object* v___y_1316_ = stack[9].m_obj;
lean_object* v_res_1342_;
v_res_1342_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_x_1307_, v_bi_1308_, v_t_1309_, v_b_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
stack->m_obj
 = v_res_1342_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg___boxed(lean_object* v_x_1343_, lean_object* v_bi_1344_, lean_object* v_t_1345_, lean_object* v_b_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
uint8_t v_bi_boxed_1354_; lean_object* v_res_1355_; 
v_bi_boxed_1354_ = lean_unbox(v_bi_1344_);
v_res_1355_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_x_1343_, v_bi_boxed_1354_, v_t_1345_, v_b_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
return v_res_1355_;
}
}
lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2(lean_object* v_x_1356_, uint8_t v_bi_1357_, lean_object* v_t_1358_, lean_object* v_b_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_x_1356_, v_bi_1357_, v_t_1358_, v_b_1359_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
return v___x_1370_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1356_ = stack[0].m_obj;
uint8_t v_bi_1357_ = stack[1].m_num;
lean_object* v_t_1358_ = stack[2].m_obj;
lean_object* v_b_1359_ = stack[3].m_obj;
lean_object* v___y_1360_ = stack[4].m_obj;
lean_object* v___y_1361_ = stack[5].m_obj;
lean_object* v___y_1362_ = stack[6].m_obj;
lean_object* v___y_1363_ = stack[7].m_obj;
lean_object* v___y_1364_ = stack[8].m_obj;
lean_object* v___y_1365_ = stack[9].m_obj;
lean_object* v___y_1366_ = stack[10].m_obj;
lean_object* v___y_1367_ = stack[11].m_obj;
lean_object* v___y_1368_ = stack[12].m_obj;
lean_object* v_res_1371_;
v_res_1371_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2(v_x_1356_, v_bi_1357_, v_t_1358_, v_b_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
stack->m_obj
 = v_res_1371_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___boxed(lean_object* v_x_1372_, lean_object* v_bi_1373_, lean_object* v_t_1374_, lean_object* v_b_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
uint8_t v_bi_boxed_1386_; lean_object* v_res_1387_; 
v_bi_boxed_1386_ = lean_unbox(v_bi_1373_);
v_res_1387_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2(v_x_1372_, v_bi_boxed_1386_, v_t_1374_, v_b_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v___y_1376_);
return v_res_1387_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__4(void){
_start:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1398_ = lean_box(0);
v___x_1399_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__3));
v___x_1400_ = l_Lean_mkConst(v___x_1399_, v___x_1398_);
return v___x_1400_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__11(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1412_ = lean_box(0);
v___x_1413_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__10));
v___x_1414_ = l_Lean_mkConst(v___x_1413_, v___x_1412_);
return v___x_1414_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__14(void){
_start:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1419_ = lean_box(0);
v___x_1420_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__13));
v___x_1421_ = l_Lean_mkConst(v___x_1420_, v___x_1419_);
return v___x_1421_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__17(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1426_ = lean_box(0);
v___x_1427_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__16));
v___x_1428_ = l_Lean_mkConst(v___x_1427_, v___x_1426_);
return v___x_1428_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__20(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1434_ = lean_box(0);
v___x_1435_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__19));
v___x_1436_ = l_Lean_mkConst(v___x_1435_, v___x_1434_);
return v___x_1436_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__23(void){
_start:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1442_ = lean_box(0);
v___x_1443_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__22));
v___x_1444_ = l_Lean_mkConst(v___x_1443_, v___x_1442_);
return v___x_1444_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__26(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v___x_1450_ = lean_box(0);
v___x_1451_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__25));
v___x_1452_ = l_Lean_mkConst(v___x_1451_, v___x_1450_);
return v___x_1452_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__33(void){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1466_ = lean_box(0);
v___x_1467_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__32));
v___x_1468_ = l_Lean_mkConst(v___x_1467_, v___x_1466_);
return v___x_1468_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__36(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1474_ = lean_box(0);
v___x_1475_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__35));
v___x_1476_ = l_Lean_mkConst(v___x_1475_, v___x_1474_);
return v___x_1476_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__39(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = lean_box(0);
v___x_1483_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__38));
v___x_1484_ = l_Lean_mkConst(v___x_1483_, v___x_1482_);
return v___x_1484_;
}
}
lean_object* l_Lean_Meta_Grind_NormSym_pushNot(lean_object* v_e_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v___y_1497_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1503_; lean_object* v___y_1504_; uint8_t v___y_1505_; lean_object* v___y_1506_; lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; uint8_t v___y_1510_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v___x_1568_ = l_Lean_Expr_cleanupAnnotations(v_e_1485_);
v___x_1569_ = l_Lean_Expr_isApp(v___x_1568_);
if (v___x_1569_ == 0)
{
lean_dec_ref(v___x_1568_);
goto v___jp_1565_;
}
else
{
lean_object* v_arg_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; lean_object* v___y_1575_; lean_object* v___y_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; 
v_arg_1570_ = lean_ctor_get(v___x_1568_, 1);
lean_inc_ref(v_arg_1570_);
v___x_1571_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1568_);
v___x_1572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS___closed__1));
v___x_1573_ = l_Lean_Expr_isConstOf(v___x_1571_, v___x_1572_);
lean_dec_ref(v___x_1571_);
if (v___x_1573_ == 0)
{
lean_dec_ref(v_arg_1570_);
goto v___jp_1565_;
}
else
{
lean_object* v___x_1634_; 
lean_inc_ref(v_arg_1570_);
v___x_1634_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1570_, v_a_1492_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_2018_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_1637_ = v___x_1634_;
v_isShared_1638_ = v_isSharedCheck_2018_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1634_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_2018_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; 
v___x_1639_ = l_Lean_Expr_cleanupAnnotations(v_a_1635_);
v___x_1640_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__6));
v___x_1641_ = l_Lean_Expr_isConstOf(v___x_1639_, v___x_1640_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; uint8_t v___x_1643_; 
v___x_1642_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_1643_ = l_Lean_Expr_isConstOf(v___x_1639_, v___x_1642_);
if (v___x_1643_ == 0)
{
uint8_t v___x_1644_; 
v___x_1644_ = l_Lean_Expr_isApp(v___x_1639_);
if (v___x_1644_ == 0)
{
lean_dec_ref(v___x_1639_);
lean_del_object(v___x_1637_);
v___y_1575_ = v_a_1486_;
v___y_1576_ = v_a_1487_;
v___y_1577_ = v_a_1488_;
v___y_1578_ = v_a_1489_;
v___y_1579_ = v_a_1490_;
v___y_1580_ = v_a_1491_;
v___y_1581_ = v_a_1492_;
v___y_1582_ = v_a_1493_;
v___y_1583_ = v_a_1494_;
goto v___jp_1574_;
}
else
{
lean_object* v_arg_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v_arg_1645_ = lean_ctor_get(v___x_1639_, 1);
lean_inc_ref(v_arg_1645_);
v___x_1646_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1639_);
v___x_1647_ = l_Lean_Expr_isConstOf(v___x_1646_, v___x_1572_);
if (v___x_1647_ == 0)
{
uint8_t v___x_1648_; 
lean_del_object(v___x_1637_);
v___x_1648_ = l_Lean_Expr_isApp(v___x_1646_);
if (v___x_1648_ == 0)
{
lean_dec_ref(v___x_1646_);
lean_dec_ref(v_arg_1645_);
v___y_1575_ = v_a_1486_;
v___y_1576_ = v_a_1487_;
v___y_1577_ = v_a_1488_;
v___y_1578_ = v_a_1489_;
v___y_1579_ = v_a_1490_;
v___y_1580_ = v_a_1491_;
v___y_1581_ = v_a_1492_;
v___y_1582_ = v_a_1493_;
v___y_1583_ = v_a_1494_;
goto v___jp_1574_;
}
else
{
lean_object* v_arg_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; uint8_t v___x_1652_; 
v_arg_1649_ = lean_ctor_get(v___x_1646_, 1);
lean_inc_ref(v_arg_1649_);
v___x_1650_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1646_);
v___x_1651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg___closed__1));
v___x_1652_ = l_Lean_Expr_isConstOf(v___x_1650_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1653_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1));
v___x_1654_ = l_Lean_Expr_isConstOf(v___x_1650_, v___x_1653_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS___closed__1));
v___x_1656_ = l_Lean_Expr_isConstOf(v___x_1650_, v___x_1655_);
if (v___x_1656_ == 0)
{
uint8_t v___x_1657_; 
v___x_1657_ = l_Lean_Expr_isApp(v___x_1650_);
if (v___x_1657_ == 0)
{
lean_dec_ref(v___x_1650_);
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1645_);
v___y_1575_ = v_a_1486_;
v___y_1576_ = v_a_1487_;
v___y_1577_ = v_a_1488_;
v___y_1578_ = v_a_1489_;
v___y_1579_ = v_a_1490_;
v___y_1580_ = v_a_1491_;
v___y_1581_ = v_a_1492_;
v___y_1582_ = v_a_1493_;
v___y_1583_ = v_a_1494_;
goto v___jp_1574_;
}
else
{
lean_object* v_arg_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
v_arg_1658_ = lean_ctor_get(v___x_1650_, 1);
lean_inc_ref(v_arg_1658_);
v___x_1659_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1650_);
v___x_1660_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__1));
v___x_1661_ = l_Lean_Expr_isConstOf(v___x_1659_, v___x_1660_);
if (v___x_1661_ == 0)
{
uint8_t v___x_1662_; 
v___x_1662_ = l_Lean_Expr_isApp(v___x_1659_);
if (v___x_1662_ == 0)
{
lean_dec_ref(v___x_1659_);
lean_dec_ref(v_arg_1658_);
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1645_);
v___y_1575_ = v_a_1486_;
v___y_1576_ = v_a_1487_;
v___y_1577_ = v_a_1488_;
v___y_1578_ = v_a_1489_;
v___y_1579_ = v_a_1490_;
v___y_1580_ = v_a_1491_;
v___y_1581_ = v_a_1492_;
v___y_1582_ = v_a_1493_;
v___y_1583_ = v_a_1494_;
goto v___jp_1574_;
}
else
{
lean_object* v_arg_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; 
v_arg_1663_ = lean_ctor_get(v___x_1659_, 1);
lean_inc_ref(v_arg_1663_);
v___x_1664_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1659_);
v___x_1665_ = l_Lean_Expr_isApp(v___x_1664_);
if (v___x_1665_ == 0)
{
lean_dec_ref(v___x_1664_);
lean_dec_ref(v_arg_1663_);
lean_dec_ref(v_arg_1658_);
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1645_);
v___y_1575_ = v_a_1486_;
v___y_1576_ = v_a_1487_;
v___y_1577_ = v_a_1488_;
v___y_1578_ = v_a_1489_;
v___y_1579_ = v_a_1490_;
v___y_1580_ = v_a_1491_;
v___y_1581_ = v_a_1492_;
v___y_1582_ = v_a_1493_;
v___y_1583_ = v_a_1494_;
goto v___jp_1574_;
}
else
{
lean_object* v_arg_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v_arg_1666_ = lean_ctor_get(v___x_1664_, 1);
lean_inc_ref(v_arg_1666_);
v___x_1667_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1664_);
v___x_1668_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpDIte___closed__3));
v___x_1669_ = l_Lean_Expr_isConstOf(v___x_1667_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_dec_ref(v___x_1667_);
lean_dec_ref(v_arg_1666_);
lean_dec_ref(v_arg_1663_);
lean_dec_ref(v_arg_1658_);
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1645_);
v___y_1575_ = v_a_1486_;
v___y_1576_ = v_a_1487_;
v___y_1577_ = v_a_1488_;
v___y_1578_ = v_a_1489_;
v___y_1579_ = v_a_1490_;
v___y_1580_ = v_a_1491_;
v___y_1581_ = v_a_1492_;
v___y_1582_ = v_a_1493_;
v___y_1583_ = v_a_1494_;
goto v___jp_1574_;
}
else
{
lean_object* v___x_1670_; 
lean_dec_ref(v_arg_1570_);
lean_inc_ref(v_arg_1649_);
v___x_1670_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1649_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; lean_object* v___x_1672_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref_known(v___x_1670_, 1);
lean_inc_ref(v_arg_1645_);
v___x_1672_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1645_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1674_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_a_1673_);
lean_dec_ref_known(v___x_1672_, 1);
lean_inc_ref(v_arg_1658_);
lean_inc_ref(v_arg_1663_);
v___x_1674_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0(v___x_1667_, v_arg_1666_, v_arg_1663_, v_arg_1658_, v_a_1671_, v_a_1673_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1685_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1677_ = v___x_1674_;
v_isShared_1678_ = v_isSharedCheck_1685_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_a_1675_);
lean_dec(v___x_1674_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1685_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1679_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__11, &l_Lean_Meta_Grind_NormSym_pushNot___closed__11_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__11);
v___x_1680_ = l_Lean_mkApp4(v___x_1679_, v_arg_1663_, v_arg_1658_, v_arg_1649_, v_arg_1645_);
v___x_1681_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1681_, 0, v_a_1675_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
lean_ctor_set_uint8(v___x_1681_, sizeof(void*)*2, v___x_1661_);
lean_ctor_set_uint8(v___x_1681_, sizeof(void*)*2 + 1, v___x_1661_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 0, v___x_1681_);
v___x_1683_ = v___x_1677_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
else
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1693_; 
lean_dec_ref(v_arg_1663_);
lean_dec_ref(v_arg_1658_);
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1645_);
v_a_1686_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1693_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1688_ = v___x_1674_;
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1674_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1693_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1691_; 
if (v_isShared_1689_ == 0)
{
v___x_1691_ = v___x_1688_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_a_1686_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
}
}
else
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1701_; 
lean_dec(v_a_1671_);
lean_dec_ref(v___x_1667_);
lean_dec_ref(v_arg_1666_);
lean_dec_ref(v_arg_1663_);
lean_dec_ref(v_arg_1658_);
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1645_);
v_a_1694_ = lean_ctor_get(v___x_1672_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1696_ = v___x_1672_;
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1672_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1701_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1699_; 
if (v_isShared_1697_ == 0)
{
v___x_1699_ = v___x_1696_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1694_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec_ref(v___x_1667_);
lean_dec_ref(v_arg_1666_);
lean_dec_ref(v_arg_1663_);
lean_dec_ref(v_arg_1658_);
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1645_);
v_a_1702_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1670_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1670_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1707_; 
if (v_isShared_1705_ == 0)
{
v___x_1707_ = v___x_1704_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1702_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
}
}
}
}
else
{
uint8_t v___x_1710_; 
lean_dec_ref(v_arg_1570_);
v___x_1710_ = l_Lean_Expr_isProp(v_arg_1658_);
if (v___x_1710_ == 0)
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1645_, v_a_1492_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1785_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1714_ = v___x_1711_;
v_isShared_1715_ = v_isSharedCheck_1785_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1711_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1785_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v___x_1716_ = l_Lean_Expr_cleanupAnnotations(v_a_1712_);
v___x_1717_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__20));
v___x_1718_ = l_Lean_Expr_isConstOf(v___x_1716_, v___x_1717_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; uint8_t v___x_1720_; 
v___x_1719_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__18));
v___x_1720_ = l_Lean_Expr_isConstOf(v___x_1716_, v___x_1719_);
lean_dec_ref(v___x_1716_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1723_; 
lean_dec_ref(v___x_1659_);
lean_dec_ref(v_arg_1658_);
lean_dec_ref(v_arg_1649_);
v___x_1721_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1721_, 0, v___x_1710_);
lean_ctor_set_uint8(v___x_1721_, 1, v___x_1710_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 0, v___x_1721_);
v___x_1723_ = v___x_1714_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
else
{
lean_object* v___x_1725_; 
lean_del_object(v___x_1714_);
v___x_1725_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_1489_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1725_, 1);
lean_inc_ref(v_arg_1649_);
v___x_1727_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v___x_1659_, v_arg_1658_, v_arg_1649_, v_a_1726_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1738_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1730_ = v___x_1727_;
v_isShared_1731_ = v_isSharedCheck_1738_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1727_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1738_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1736_; 
v___x_1732_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__14, &l_Lean_Meta_Grind_NormSym_pushNot___closed__14_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__14);
v___x_1733_ = l_Lean_Expr_app___override(v___x_1732_, v_arg_1649_);
v___x_1734_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1734_, 0, v_a_1728_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
lean_ctor_set_uint8(v___x_1734_, sizeof(void*)*2, v___x_1710_);
lean_ctor_set_uint8(v___x_1734_, sizeof(void*)*2 + 1, v___x_1710_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 0, v___x_1734_);
v___x_1736_ = v___x_1730_;
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
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec_ref(v_arg_1649_);
v_a_1739_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1727_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1727_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec_ref(v___x_1659_);
lean_dec_ref(v_arg_1658_);
lean_dec_ref(v_arg_1649_);
v_a_1747_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1725_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1725_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
else
{
lean_object* v___x_1755_; 
lean_dec_ref(v___x_1716_);
lean_del_object(v___x_1714_);
v___x_1755_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_1489_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1757_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref_known(v___x_1755_, 1);
lean_inc_ref(v_arg_1649_);
v___x_1757_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v___x_1659_, v_arg_1658_, v_arg_1649_, v_a_1756_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1768_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1768_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1768_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; 
v___x_1762_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__17, &l_Lean_Meta_Grind_NormSym_pushNot___closed__17_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__17);
v___x_1763_ = l_Lean_Expr_app___override(v___x_1762_, v_arg_1649_);
v___x_1764_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1764_, 0, v_a_1758_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
lean_ctor_set_uint8(v___x_1764_, sizeof(void*)*2, v___x_1710_);
lean_ctor_set_uint8(v___x_1764_, sizeof(void*)*2 + 1, v___x_1710_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1764_);
v___x_1766_ = v___x_1760_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec_ref(v_arg_1649_);
v_a_1769_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1757_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1757_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec_ref(v___x_1659_);
lean_dec_ref(v_arg_1658_);
lean_dec_ref(v_arg_1649_);
v_a_1777_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1755_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1755_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec_ref(v___x_1659_);
lean_dec_ref(v_arg_1658_);
lean_dec_ref(v_arg_1649_);
v_a_1786_ = lean_ctor_get(v___x_1711_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1711_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1711_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
else
{
lean_object* v___x_1794_; 
lean_inc_ref(v_arg_1645_);
v___x_1794_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1645_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1796_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_a_1795_);
lean_dec_ref_known(v___x_1794_, 1);
lean_inc_ref(v_arg_1649_);
v___x_1796_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v___x_1659_, v_arg_1658_, v_arg_1649_, v_a_1795_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1807_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1807_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1807_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1801_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__20, &l_Lean_Meta_Grind_NormSym_pushNot___closed__20_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__20);
v___x_1802_ = l_Lean_mkAppB(v___x_1801_, v_arg_1649_, v_arg_1645_);
v___x_1803_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1803_, 0, v_a_1797_);
lean_ctor_set(v___x_1803_, 1, v___x_1802_);
lean_ctor_set_uint8(v___x_1803_, sizeof(void*)*2, v___x_1656_);
lean_ctor_set_uint8(v___x_1803_, sizeof(void*)*2 + 1, v___x_1656_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 0, v___x_1803_);
v___x_1805_ = v___x_1799_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1645_);
v_a_1808_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1796_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1796_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
lean_dec_ref(v___x_1659_);
lean_dec_ref(v_arg_1658_);
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1645_);
v_a_1816_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1794_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1794_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1824_; 
lean_dec_ref(v___x_1650_);
lean_dec_ref(v_arg_1570_);
lean_inc_ref(v_arg_1649_);
v___x_1824_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1649_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v___x_1826_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_a_1825_);
lean_dec_ref_known(v___x_1824_, 1);
lean_inc_ref(v_arg_1645_);
v___x_1826_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1645_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1828_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_a_1827_);
lean_dec_ref_known(v___x_1826_, 1);
v___x_1828_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_a_1825_, v_a_1827_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1839_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1839_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1839_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1837_; 
v___x_1833_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__23, &l_Lean_Meta_Grind_NormSym_pushNot___closed__23_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__23);
v___x_1834_ = l_Lean_mkAppB(v___x_1833_, v_arg_1649_, v_arg_1645_);
v___x_1835_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1835_, 0, v_a_1829_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
lean_ctor_set_uint8(v___x_1835_, sizeof(void*)*2, v___x_1654_);
lean_ctor_set_uint8(v___x_1835_, sizeof(void*)*2 + 1, v___x_1654_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1835_);
v___x_1837_ = v___x_1831_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v___x_1835_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1645_);
v_a_1840_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1828_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1828_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_dec(v_a_1825_);
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1645_);
v_a_1848_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1826_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1826_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1645_);
v_a_1856_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1824_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1824_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
}
else
{
lean_object* v___x_1864_; 
lean_dec_ref(v___x_1650_);
lean_dec_ref(v_arg_1570_);
lean_inc_ref(v_arg_1649_);
v___x_1864_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1649_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; lean_object* v___x_1866_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref_known(v___x_1864_, 1);
lean_inc_ref(v_arg_1645_);
v___x_1866_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_arg_1645_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
if (lean_obj_tag(v___x_1866_) == 0)
{
lean_object* v_a_1867_; lean_object* v___x_1868_; 
v_a_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc(v_a_1867_);
lean_dec_ref_known(v___x_1866_, 1);
v___x_1868_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v_a_1865_, v_a_1867_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1879_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1871_ = v___x_1868_;
v_isShared_1872_ = v_isSharedCheck_1879_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1868_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1879_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1877_; 
v___x_1873_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__26, &l_Lean_Meta_Grind_NormSym_pushNot___closed__26_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__26);
v___x_1874_ = l_Lean_mkAppB(v___x_1873_, v_arg_1649_, v_arg_1645_);
v___x_1875_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1875_, 0, v_a_1869_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*2, v___x_1652_);
lean_ctor_set_uint8(v___x_1875_, sizeof(void*)*2 + 1, v___x_1652_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 0, v___x_1875_);
v___x_1877_ = v___x_1871_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1645_);
v_a_1880_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1868_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1868_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec(v_a_1865_);
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1645_);
v_a_1888_ = lean_ctor_get(v___x_1866_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1866_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1866_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1866_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1645_);
v_a_1896_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1864_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1864_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
lean_dec_ref(v___x_1650_);
lean_dec_ref(v_arg_1570_);
v___x_1904_ = lean_unsigned_to_nat(0u);
v___x_1905_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(v___x_1904_, v_a_1490_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref_known(v___x_1905_, 1);
v___x_1907_ = lean_unsigned_to_nat(1u);
v___x_1908_ = lean_mk_empty_array_with_capacity(v___x_1907_);
v___x_1909_ = lean_array_push(v___x_1908_, v_a_1906_);
lean_inc_ref(v_arg_1645_);
v___x_1910_ = l_Lean_Meta_Sym_betaS(v_arg_1645_, v___x_1909_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1912_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_a_1911_);
lean_dec_ref_known(v___x_1910_, 1);
v___x_1912_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_a_1911_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; lean_object* v___x_1914_; uint8_t v___x_1915_; lean_object* v___x_1916_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v___x_1912_, 1);
v___x_1914_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__28));
v___x_1915_ = 0;
lean_inc_ref(v_arg_1649_);
v___x_1916_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v___x_1914_, v___x_1915_, v_arg_1649_, v_a_1913_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v_a_1917_; lean_object* v___x_1918_; 
v_a_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_a_1917_);
lean_dec_ref_known(v___x_1916_, 1);
lean_inc_ref(v_arg_1649_);
v___x_1918_ = l_Lean_Meta_Sym_getLevel___redArg(v_arg_1649_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1932_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1932_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1932_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1923_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__30));
v___x_1924_ = lean_box(0);
v___x_1925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1925_, 0, v_a_1919_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = l_Lean_mkConst(v___x_1923_, v___x_1925_);
v___x_1927_ = l_Lean_mkAppB(v___x_1926_, v_arg_1649_, v_arg_1645_);
v___x_1928_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1928_, 0, v_a_1917_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
lean_ctor_set_uint8(v___x_1928_, sizeof(void*)*2, v___x_1647_);
lean_ctor_set_uint8(v___x_1928_, sizeof(void*)*2 + 1, v___x_1647_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___x_1928_);
v___x_1930_ = v___x_1921_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v_a_1917_);
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1645_);
v_a_1933_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1918_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1918_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1645_);
v_a_1941_ = lean_ctor_get(v___x_1916_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1916_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1916_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1645_);
v_a_1949_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1912_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1912_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
else
{
lean_object* v_a_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1964_; 
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1645_);
v_a_1957_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1959_ = v___x_1910_;
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_a_1957_);
lean_dec(v___x_1910_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1964_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1962_; 
if (v_isShared_1960_ == 0)
{
v___x_1962_ = v___x_1959_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_a_1957_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec_ref(v_arg_1649_);
lean_dec_ref(v_arg_1645_);
v_a_1965_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___x_1905_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1905_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
}
else
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1977_; 
lean_dec_ref(v___x_1646_);
lean_dec_ref(v_arg_1570_);
v___x_1973_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__33, &l_Lean_Meta_Grind_NormSym_pushNot___closed__33_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__33);
lean_inc_ref(v_arg_1645_);
v___x_1974_ = l_Lean_Expr_app___override(v___x_1973_, v_arg_1645_);
v___x_1975_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1975_, 0, v_arg_1645_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
lean_ctor_set_uint8(v___x_1975_, sizeof(void*)*2, v___x_1643_);
lean_ctor_set_uint8(v___x_1975_, sizeof(void*)*2 + 1, v___x_1643_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 0, v___x_1975_);
v___x_1977_ = v___x_1637_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
else
{
lean_object* v___x_1979_; 
lean_dec_ref(v___x_1639_);
lean_del_object(v___x_1637_);
lean_dec_ref(v_arg_1570_);
v___x_1979_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_1489_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1989_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_1989_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1989_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1984_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__36, &l_Lean_Meta_Grind_NormSym_pushNot___closed__36_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__36);
v___x_1985_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1985_, 0, v_a_1980_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
lean_ctor_set_uint8(v___x_1985_, sizeof(void*)*2, v___x_1641_);
lean_ctor_set_uint8(v___x_1985_, sizeof(void*)*2 + 1, v___x_1641_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1985_);
v___x_1987_ = v___x_1982_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
else
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_1997_; 
v_a_1990_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_1997_ == 0)
{
v___x_1992_ = v___x_1979_;
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1979_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_1997_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1995_; 
if (v_isShared_1993_ == 0)
{
v___x_1995_ = v___x_1992_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
v___x_1995_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
return v___x_1995_;
}
}
}
}
}
else
{
lean_object* v___x_1998_; 
lean_dec_ref(v___x_1639_);
lean_del_object(v___x_1637_);
lean_dec_ref(v_arg_1570_);
v___x_1998_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_1489_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2009_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2001_ = v___x_1998_;
v_isShared_2002_ = v_isSharedCheck_2009_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2009_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; uint8_t v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2003_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__39, &l_Lean_Meta_Grind_NormSym_pushNot___closed__39_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__39);
v___x_2004_ = 0;
v___x_2005_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2005_, 0, v_a_1999_);
lean_ctor_set(v___x_2005_, 1, v___x_2003_);
lean_ctor_set_uint8(v___x_2005_, sizeof(void*)*2, v___x_2004_);
lean_ctor_set_uint8(v___x_2005_, sizeof(void*)*2 + 1, v___x_2004_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2005_);
v___x_2007_ = v___x_2001_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
v_a_2010_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_1998_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_1998_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_dec_ref(v_arg_1570_);
v_a_2019_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_1634_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_1634_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
v___jp_1574_:
{
if (lean_obj_tag(v_arg_1570_) == 7)
{
lean_object* v_binderName_1584_; lean_object* v_binderType_1585_; lean_object* v_body_1586_; uint8_t v_binderInfo_1587_; lean_object* v___x_1588_; 
v_binderName_1584_ = lean_ctor_get(v_arg_1570_, 0);
lean_inc(v_binderName_1584_);
v_binderType_1585_ = lean_ctor_get(v_arg_1570_, 1);
lean_inc_ref_n(v_binderType_1585_, 2);
v_body_1586_ = lean_ctor_get(v_arg_1570_, 2);
lean_inc_ref(v_body_1586_);
v_binderInfo_1587_ = lean_ctor_get_uint8(v_arg_1570_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_arg_1570_, 3);
v___x_1588_ = l_Lean_Meta_isProp(v_binderType_1585_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; uint8_t v___x_1590_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1589_);
lean_dec_ref_known(v___x_1588_, 1);
v___x_1590_ = l_Lean_Expr_hasLooseBVars(v_body_1586_);
if (v___x_1590_ == 0)
{
if (v___x_1573_ == 0)
{
lean_dec(v_a_1589_);
v___y_1497_ = v_body_1586_;
v___y_1498_ = v___y_1579_;
v___y_1499_ = v___y_1576_;
v___y_1500_ = v___y_1577_;
v___y_1501_ = v___y_1581_;
v___y_1502_ = v___y_1582_;
v___y_1503_ = v_binderType_1585_;
v___y_1504_ = v___y_1578_;
v___y_1505_ = v_binderInfo_1587_;
v___y_1506_ = v___y_1580_;
v___y_1507_ = v___y_1575_;
v___y_1508_ = v_binderName_1584_;
v___y_1509_ = v___y_1583_;
v___y_1510_ = v___x_1573_;
goto v___jp_1496_;
}
else
{
uint8_t v___x_1591_; 
v___x_1591_ = lean_unbox(v_a_1589_);
if (v___x_1591_ == 0)
{
uint8_t v___x_1592_; 
v___x_1592_ = lean_unbox(v_a_1589_);
lean_dec(v_a_1589_);
v___y_1497_ = v_body_1586_;
v___y_1498_ = v___y_1579_;
v___y_1499_ = v___y_1576_;
v___y_1500_ = v___y_1577_;
v___y_1501_ = v___y_1581_;
v___y_1502_ = v___y_1582_;
v___y_1503_ = v_binderType_1585_;
v___y_1504_ = v___y_1578_;
v___y_1505_ = v_binderInfo_1587_;
v___y_1506_ = v___y_1580_;
v___y_1507_ = v___y_1575_;
v___y_1508_ = v_binderName_1584_;
v___y_1509_ = v___y_1583_;
v___y_1510_ = v___x_1592_;
goto v___jp_1496_;
}
else
{
lean_object* v___x_1593_; 
lean_dec(v_a_1589_);
lean_dec(v_binderName_1584_);
lean_inc_ref(v_body_1586_);
v___x_1593_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_body_1586_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1595_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1593_, 1);
lean_inc_ref(v_binderType_1585_);
v___x_1595_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v_binderType_1585_, v_a_1594_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1606_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1598_ = v___x_1595_;
v_isShared_1599_ = v_isSharedCheck_1606_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1606_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1600_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__4, &l_Lean_Meta_Grind_NormSym_pushNot___closed__4_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__4);
v___x_1601_ = l_Lean_mkAppB(v___x_1600_, v_binderType_1585_, v_body_1586_);
v___x_1602_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1602_, 0, v_a_1596_);
lean_ctor_set(v___x_1602_, 1, v___x_1601_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*2, v___x_1590_);
lean_ctor_set_uint8(v___x_1602_, sizeof(void*)*2 + 1, v___x_1590_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 0, v___x_1602_);
v___x_1604_ = v___x_1598_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1602_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec_ref(v_body_1586_);
lean_dec_ref(v_binderType_1585_);
v_a_1607_ = lean_ctor_get(v___x_1595_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1595_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1595_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1595_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec_ref(v_body_1586_);
lean_dec_ref(v_binderType_1585_);
v_a_1615_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1593_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1593_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
}
else
{
uint8_t v___x_1623_; 
lean_dec(v_a_1589_);
v___x_1623_ = 0;
v___y_1497_ = v_body_1586_;
v___y_1498_ = v___y_1579_;
v___y_1499_ = v___y_1576_;
v___y_1500_ = v___y_1577_;
v___y_1501_ = v___y_1581_;
v___y_1502_ = v___y_1582_;
v___y_1503_ = v_binderType_1585_;
v___y_1504_ = v___y_1578_;
v___y_1505_ = v_binderInfo_1587_;
v___y_1506_ = v___y_1580_;
v___y_1507_ = v___y_1575_;
v___y_1508_ = v_binderName_1584_;
v___y_1509_ = v___y_1583_;
v___y_1510_ = v___x_1623_;
goto v___jp_1496_;
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec_ref(v_body_1586_);
lean_dec_ref(v_binderType_1585_);
lean_dec(v_binderName_1584_);
v_a_1624_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1588_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1588_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
else
{
lean_object* v___x_1632_; lean_object* v___x_1633_; 
lean_dec_ref(v_arg_1570_);
v___x_1632_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
return v___x_1633_;
}
}
}
v___jp_1496_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
lean_inc_ref(v___y_1497_);
lean_inc_ref(v___y_1503_);
lean_inc(v___y_1508_);
v___x_1511_ = l_Lean_mkLambda(v___y_1508_, v___y_1505_, v___y_1503_, v___y_1497_);
v___x_1512_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v___y_1497_, v___y_1507_, v___y_1499_, v___y_1500_, v___y_1504_, v___y_1498_, v___y_1506_, v___y_1501_, v___y_1502_, v___y_1509_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1514_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref_known(v___x_1512_, 1);
lean_inc_ref(v___y_1503_);
v___x_1514_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v___y_1508_, v___y_1505_, v___y_1503_, v_a_1513_, v___y_1504_, v___y_1498_, v___y_1506_, v___y_1501_, v___y_1502_, v___y_1509_);
if (lean_obj_tag(v___x_1514_) == 0)
{
lean_object* v_a_1515_; lean_object* v___x_1516_; 
v_a_1515_ = lean_ctor_get(v___x_1514_, 0);
lean_inc(v_a_1515_);
lean_dec_ref_known(v___x_1514_, 1);
lean_inc_ref(v___y_1503_);
v___x_1516_ = l_Lean_Meta_Sym_getLevel___redArg(v___y_1503_, v___y_1498_, v___y_1506_, v___y_1501_, v___y_1502_, v___y_1509_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1518_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc_n(v_a_1517_, 2);
lean_dec_ref_known(v___x_1516_, 1);
lean_inc_ref(v___y_1503_);
v___x_1518_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg(v_a_1517_, v___y_1503_, v_a_1515_, v___y_1504_, v___y_1498_, v___y_1506_, v___y_1501_, v___y_1502_, v___y_1509_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1532_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1521_ = v___x_1518_;
v_isShared_1522_ = v_isSharedCheck_1532_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1518_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1532_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; 
v___x_1523_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__1));
v___x_1524_ = lean_box(0);
v___x_1525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1525_, 0, v_a_1517_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = l_Lean_mkConst(v___x_1523_, v___x_1525_);
v___x_1527_ = l_Lean_mkAppB(v___x_1526_, v___y_1503_, v___x_1511_);
v___x_1528_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1528_, 0, v_a_1519_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
lean_ctor_set_uint8(v___x_1528_, sizeof(void*)*2, v___y_1510_);
lean_ctor_set_uint8(v___x_1528_, sizeof(void*)*2 + 1, v___y_1510_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v___x_1528_);
v___x_1530_ = v___x_1521_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec(v_a_1517_);
lean_dec_ref(v___x_1511_);
lean_dec_ref(v___y_1503_);
v_a_1533_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1518_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1518_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
else
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1548_; 
lean_dec(v_a_1515_);
lean_dec_ref(v___x_1511_);
lean_dec_ref(v___y_1503_);
v_a_1541_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1548_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1548_ == 0)
{
v___x_1543_ = v___x_1516_;
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1516_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1548_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1546_; 
if (v_isShared_1544_ == 0)
{
v___x_1546_ = v___x_1543_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1541_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
else
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_dec_ref(v___x_1511_);
lean_dec_ref(v___y_1503_);
v_a_1549_ = lean_ctor_get(v___x_1514_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1514_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1514_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1514_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec_ref(v___x_1511_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1503_);
v_a_1557_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1512_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1512_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
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
v___jp_1565_:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
return v___x_1567_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_NormSym_pushNot_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1485_ = stack[0].m_obj;
lean_object* v_a_1486_ = stack[1].m_obj;
lean_object* v_a_1487_ = stack[2].m_obj;
lean_object* v_a_1488_ = stack[3].m_obj;
lean_object* v_a_1489_ = stack[4].m_obj;
lean_object* v_a_1490_ = stack[5].m_obj;
lean_object* v_a_1491_ = stack[6].m_obj;
lean_object* v_a_1492_ = stack[7].m_obj;
lean_object* v_a_1493_ = stack[8].m_obj;
lean_object* v_a_1494_ = stack[9].m_obj;
lean_object* v_res_2027_;
v_res_2027_ = l_Lean_Meta_Grind_NormSym_pushNot(v_e_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
stack->m_obj
 = v_res_2027_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_pushNot___boxed(lean_object* v_e_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_){
_start:
{
lean_object* v_res_2039_; 
v_res_2039_ = l_Lean_Meta_Grind_NormSym_pushNot(v_e_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_);
lean_dec(v_a_2037_);
lean_dec_ref(v_a_2036_);
lean_dec(v_a_2035_);
lean_dec_ref(v_a_2034_);
lean_dec(v_a_2033_);
lean_dec_ref(v_a_2032_);
lean_dec(v_a_2031_);
lean_dec_ref(v_a_2030_);
lean_dec(v_a_2029_);
return v_res_2039_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2045_ = lean_box(0);
v___x_2046_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__1));
v___x_2047_ = l_Lean_mkConst(v___x_2046_, v___x_2045_);
return v___x_2047_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = lean_box(0);
v___x_2054_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__4));
v___x_2055_ = l_Lean_mkConst(v___x_2054_, v___x_2053_);
return v___x_2055_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2059_ = lean_box(0);
v___x_2060_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__7));
v___x_2061_ = l_Lean_mkConst(v___x_2060_, v___x_2059_);
return v___x_2061_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2065_ = lean_box(0);
v___x_2066_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__10));
v___x_2067_ = l_Lean_mkConst(v___x_2066_, v___x_2065_);
return v___x_2067_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2073_ = lean_box(0);
v___x_2074_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__13));
v___x_2075_ = l_Lean_mkConst(v___x_2074_, v___x_2073_);
return v___x_2075_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_box(0);
v___x_2080_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__16));
v___x_2081_ = l_Lean_mkConst(v___x_2080_, v___x_2079_);
return v___x_2081_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2085_ = lean_box(0);
v___x_2086_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__19));
v___x_2087_ = l_Lean_mkConst(v___x_2086_, v___x_2085_);
return v___x_2087_;
}
}
lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg(lean_object* v_e_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v___x_2102_; uint8_t v___x_2103_; 
v___x_2102_ = l_Lean_Expr_cleanupAnnotations(v_e_2088_);
v___x_2103_ = l_Lean_Expr_isApp(v___x_2102_);
if (v___x_2103_ == 0)
{
lean_dec_ref(v___x_2102_);
goto v___jp_2099_;
}
else
{
lean_object* v_arg_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v_arg_2104_ = lean_ctor_get(v___x_2102_, 1);
lean_inc_ref(v_arg_2104_);
v___x_2105_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2102_);
v___x_2106_ = l_Lean_Expr_isApp(v___x_2105_);
if (v___x_2106_ == 0)
{
lean_dec_ref(v___x_2105_);
lean_dec_ref(v_arg_2104_);
goto v___jp_2099_;
}
else
{
lean_object* v_arg_2107_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___x_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v_arg_2107_ = lean_ctor_get(v___x_2105_, 1);
lean_inc_ref(v_arg_2107_);
v___x_2226_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2105_);
v___x_2227_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1));
v___x_2228_ = l_Lean_Expr_isConstOf(v___x_2226_, v___x_2227_);
lean_dec_ref(v___x_2226_);
if (v___x_2228_ == 0)
{
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
goto v___jp_2099_;
}
else
{
lean_object* v___x_2229_; 
lean_inc_ref(v_arg_2107_);
v___x_2229_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_2107_, v_a_2092_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2289_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2289_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2289_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; 
v___x_2234_ = l_Lean_Expr_cleanupAnnotations(v_a_2230_);
v___x_2235_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__6));
v___x_2236_ = l_Lean_Expr_isConstOf(v___x_2234_, v___x_2235_);
if (v___x_2236_ == 0)
{
lean_object* v___x_2237_; uint8_t v___x_2238_; 
v___x_2237_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_2238_ = l_Lean_Expr_isConstOf(v___x_2234_, v___x_2237_);
if (v___x_2238_ == 0)
{
uint8_t v___x_2239_; 
lean_del_object(v___x_2232_);
v___x_2239_ = l_Lean_Expr_isApp(v___x_2234_);
if (v___x_2239_ == 0)
{
lean_dec_ref(v___x_2234_);
v___y_2109_ = v_a_2089_;
v___y_2110_ = v_a_2090_;
v___y_2111_ = v_a_2091_;
v___y_2112_ = v_a_2092_;
v___y_2113_ = v_a_2093_;
v___y_2114_ = v_a_2094_;
goto v___jp_2108_;
}
else
{
lean_object* v_arg_2240_; lean_object* v___x_2241_; uint8_t v___x_2242_; 
v_arg_2240_ = lean_ctor_get(v___x_2234_, 1);
lean_inc_ref(v_arg_2240_);
v___x_2241_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2234_);
v___x_2242_ = l_Lean_Expr_isApp(v___x_2241_);
if (v___x_2242_ == 0)
{
lean_dec_ref(v___x_2241_);
lean_dec_ref(v_arg_2240_);
v___y_2109_ = v_a_2089_;
v___y_2110_ = v_a_2090_;
v___y_2111_ = v_a_2091_;
v___y_2112_ = v_a_2092_;
v___y_2113_ = v_a_2093_;
v___y_2114_ = v_a_2094_;
goto v___jp_2108_;
}
else
{
lean_object* v_arg_2243_; lean_object* v___x_2244_; uint8_t v___x_2245_; 
v_arg_2243_ = lean_ctor_get(v___x_2241_, 1);
lean_inc_ref(v_arg_2243_);
v___x_2244_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2241_);
v___x_2245_ = l_Lean_Expr_isConstOf(v___x_2244_, v___x_2227_);
lean_dec_ref(v___x_2244_);
if (v___x_2245_ == 0)
{
lean_dec_ref(v_arg_2243_);
lean_dec_ref(v_arg_2240_);
v___y_2109_ = v_a_2089_;
v___y_2110_ = v_a_2090_;
v___y_2111_ = v_a_2091_;
v___y_2112_ = v_a_2092_;
v___y_2113_ = v_a_2093_;
v___y_2114_ = v_a_2094_;
goto v___jp_2108_;
}
else
{
lean_object* v___x_2246_; 
lean_dec_ref(v_arg_2107_);
lean_inc_ref(v_arg_2104_);
lean_inc_ref(v_arg_2240_);
v___x_2246_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_arg_2240_, v_arg_2104_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2248_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2246_, 1);
lean_inc_ref(v_arg_2243_);
v___x_2248_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_arg_2243_, v_a_2247_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
if (lean_obj_tag(v___x_2248_) == 0)
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2259_; 
v_a_2249_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2251_ = v___x_2248_;
v_isShared_2252_ = v_isSharedCheck_2259_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2248_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2259_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2257_; 
v___x_2253_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14);
v___x_2254_ = l_Lean_mkApp3(v___x_2253_, v_arg_2243_, v_arg_2240_, v_arg_2104_);
v___x_2255_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2255_, 0, v_a_2249_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
lean_ctor_set_uint8(v___x_2255_, sizeof(void*)*2, v___x_2238_);
lean_ctor_set_uint8(v___x_2255_, sizeof(void*)*2 + 1, v___x_2238_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2255_);
v___x_2257_ = v___x_2251_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2255_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
lean_dec_ref(v_arg_2243_);
lean_dec_ref(v_arg_2240_);
lean_dec_ref(v_arg_2104_);
v_a_2260_ = lean_ctor_get(v___x_2248_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2248_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2248_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2248_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec_ref(v_arg_2243_);
lean_dec_ref(v_arg_2240_);
lean_dec_ref(v_arg_2104_);
v_a_2268_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2246_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2246_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2280_; 
lean_dec_ref(v___x_2234_);
v___x_2276_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17);
v___x_2277_ = l_Lean_Expr_app___override(v___x_2276_, v_arg_2104_);
v___x_2278_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2278_, 0, v_arg_2107_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
lean_ctor_set_uint8(v___x_2278_, sizeof(void*)*2, v___x_2236_);
lean_ctor_set_uint8(v___x_2278_, sizeof(void*)*2 + 1, v___x_2236_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v___x_2278_);
v___x_2280_ = v___x_2232_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v___x_2278_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
else
{
lean_object* v___x_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2287_; 
lean_dec_ref(v___x_2234_);
lean_dec_ref(v_arg_2107_);
v___x_2282_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20);
lean_inc_ref(v_arg_2104_);
v___x_2283_ = l_Lean_Expr_app___override(v___x_2282_, v_arg_2104_);
v___x_2284_ = 0;
v___x_2285_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2285_, 0, v_arg_2104_);
lean_ctor_set(v___x_2285_, 1, v___x_2283_);
lean_ctor_set_uint8(v___x_2285_, sizeof(void*)*2, v___x_2284_);
lean_ctor_set_uint8(v___x_2285_, sizeof(void*)*2 + 1, v___x_2284_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v___x_2285_);
v___x_2287_ = v___x_2232_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
else
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
v_a_2290_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2229_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2229_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
v___jp_2108_:
{
lean_object* v___x_2115_; 
lean_inc_ref(v_arg_2104_);
v___x_2115_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_2104_, v___y_2112_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2217_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2118_ = v___x_2115_;
v_isShared_2119_ = v_isSharedCheck_2217_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2115_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2217_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2120_ = l_Lean_Expr_cleanupAnnotations(v_a_2116_);
v___x_2121_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__6));
v___x_2122_ = l_Lean_Expr_isConstOf(v___x_2120_, v___x_2121_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2123_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_2124_ = l_Lean_Expr_isConstOf(v___x_2120_, v___x_2123_);
if (v___x_2124_ == 0)
{
uint8_t v___x_2125_; 
lean_dec_ref(v_arg_2104_);
v___x_2125_ = l_Lean_Expr_isApp(v___x_2120_);
if (v___x_2125_ == 0)
{
lean_dec_ref(v___x_2120_);
lean_del_object(v___x_2118_);
lean_dec_ref(v_arg_2107_);
goto v___jp_2096_;
}
else
{
lean_object* v_arg_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; 
v_arg_2126_ = lean_ctor_get(v___x_2120_, 1);
lean_inc_ref(v_arg_2126_);
v___x_2127_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2120_);
v___x_2128_ = l_Lean_Expr_isApp(v___x_2127_);
if (v___x_2128_ == 0)
{
lean_dec_ref(v___x_2127_);
lean_dec_ref(v_arg_2126_);
lean_del_object(v___x_2118_);
lean_dec_ref(v_arg_2107_);
goto v___jp_2096_;
}
else
{
lean_object* v_arg_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; 
v_arg_2129_ = lean_ctor_get(v___x_2127_, 1);
lean_inc_ref(v_arg_2129_);
v___x_2130_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2127_);
v___x_2131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1));
v___x_2132_ = l_Lean_Expr_isConstOf(v___x_2130_, v___x_2131_);
lean_dec_ref(v___x_2130_);
if (v___x_2132_ == 0)
{
lean_dec_ref(v_arg_2129_);
lean_dec_ref(v_arg_2126_);
lean_del_object(v___x_2118_);
lean_dec_ref(v_arg_2107_);
goto v___jp_2096_;
}
else
{
uint8_t v___x_2133_; 
v___x_2133_ = l_Lean_Expr_isForall(v_arg_2107_);
if (v___x_2133_ == 0)
{
uint8_t v___x_2134_; 
v___x_2134_ = l_Lean_Expr_isForall(v_arg_2129_);
if (v___x_2134_ == 0)
{
uint8_t v___x_2135_; 
v___x_2135_ = l_Lean_Expr_isForall(v_arg_2126_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; lean_object* v___x_2138_; 
lean_dec_ref(v_arg_2129_);
lean_dec_ref(v_arg_2126_);
lean_dec_ref(v_arg_2107_);
v___x_2136_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2136_, 0, v___x_2135_);
lean_ctor_set_uint8(v___x_2136_, 1, v___x_2135_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2136_);
v___x_2138_ = v___x_2118_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
else
{
lean_object* v___x_2140_; 
lean_del_object(v___x_2118_);
lean_inc_ref(v_arg_2107_);
lean_inc_ref(v_arg_2129_);
v___x_2140_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_arg_2129_, v_arg_2107_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2142_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2140_, 1);
lean_inc_ref(v_arg_2126_);
v___x_2142_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_arg_2126_, v_a_2141_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2153_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2145_ = v___x_2142_;
v_isShared_2146_ = v_isSharedCheck_2153_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2142_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2153_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2147_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2);
v___x_2148_ = l_Lean_mkApp3(v___x_2147_, v_arg_2107_, v_arg_2129_, v_arg_2126_);
v___x_2149_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2149_, 0, v_a_2143_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*2, v___x_2134_);
lean_ctor_set_uint8(v___x_2149_, sizeof(void*)*2 + 1, v___x_2134_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 0, v___x_2149_);
v___x_2151_ = v___x_2145_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2149_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec_ref(v_arg_2129_);
lean_dec_ref(v_arg_2126_);
lean_dec_ref(v_arg_2107_);
v_a_2154_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2142_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2142_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec_ref(v_arg_2129_);
lean_dec_ref(v_arg_2126_);
lean_dec_ref(v_arg_2107_);
v_a_2162_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2140_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2140_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
}
else
{
lean_object* v___x_2170_; 
lean_del_object(v___x_2118_);
lean_inc_ref(v_arg_2126_);
lean_inc_ref(v_arg_2107_);
v___x_2170_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_arg_2107_, v_arg_2126_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2172_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2170_, 1);
lean_inc_ref(v_arg_2129_);
v___x_2172_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_arg_2129_, v_a_2171_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2183_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2175_ = v___x_2172_;
v_isShared_2176_ = v_isSharedCheck_2183_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2172_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2183_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2181_; 
v___x_2177_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5);
v___x_2178_ = l_Lean_mkApp3(v___x_2177_, v_arg_2107_, v_arg_2129_, v_arg_2126_);
v___x_2179_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2179_, 0, v_a_2173_);
lean_ctor_set(v___x_2179_, 1, v___x_2178_);
lean_ctor_set_uint8(v___x_2179_, sizeof(void*)*2, v___x_2133_);
lean_ctor_set_uint8(v___x_2179_, sizeof(void*)*2 + 1, v___x_2133_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v___x_2179_);
v___x_2181_ = v___x_2175_;
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
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec_ref(v_arg_2129_);
lean_dec_ref(v_arg_2126_);
lean_dec_ref(v_arg_2107_);
v_a_2184_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2172_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2172_);
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
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec_ref(v_arg_2129_);
lean_dec_ref(v_arg_2126_);
lean_dec_ref(v_arg_2107_);
v_a_2192_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2170_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2170_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
else
{
lean_object* v___x_2200_; lean_object* v___x_2202_; 
lean_dec_ref(v_arg_2129_);
lean_dec_ref(v_arg_2126_);
lean_dec_ref(v_arg_2107_);
v___x_2200_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2200_, 0, v___x_2124_);
lean_ctor_set_uint8(v___x_2200_, 1, v___x_2124_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2200_);
v___x_2202_ = v___x_2118_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
}
}
else
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2208_; 
lean_dec_ref(v___x_2120_);
v___x_2204_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8);
v___x_2205_ = l_Lean_Expr_app___override(v___x_2204_, v_arg_2107_);
v___x_2206_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2206_, 0, v_arg_2104_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*2, v___x_2122_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*2 + 1, v___x_2122_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2206_);
v___x_2208_ = v___x_2118_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2206_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; uint8_t v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2215_; 
lean_dec_ref(v___x_2120_);
lean_dec_ref(v_arg_2104_);
v___x_2210_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11);
lean_inc_ref(v_arg_2107_);
v___x_2211_ = l_Lean_Expr_app___override(v___x_2210_, v_arg_2107_);
v___x_2212_ = 0;
v___x_2213_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2213_, 0, v_arg_2107_);
lean_ctor_set(v___x_2213_, 1, v___x_2211_);
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*2, v___x_2212_);
lean_ctor_set_uint8(v___x_2213_, sizeof(void*)*2 + 1, v___x_2212_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2213_);
v___x_2215_ = v___x_2118_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
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
lean_dec_ref(v_arg_2107_);
lean_dec_ref(v_arg_2104_);
v_a_2218_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2115_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2115_);
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
}
v___jp_2096_:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2097_);
return v___x_2098_;
}
v___jp_2099_:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
return v___x_2101_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_NormSym_simpOr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2088_ = stack[0].m_obj;
lean_object* v_a_2089_ = stack[1].m_obj;
lean_object* v_a_2090_ = stack[2].m_obj;
lean_object* v_a_2091_ = stack[3].m_obj;
lean_object* v_a_2092_ = stack[4].m_obj;
lean_object* v_a_2093_ = stack[5].m_obj;
lean_object* v_a_2094_ = stack[6].m_obj;
lean_object* v_res_2298_;
v_res_2298_ = l_Lean_Meta_Grind_NormSym_simpOr___redArg(v_e_2088_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
stack->m_obj
 = v_res_2298_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___boxed(lean_object* v_e_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_Meta_Grind_NormSym_simpOr___redArg(v_e_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
lean_dec(v_a_2305_);
lean_dec_ref(v_a_2304_);
lean_dec(v_a_2303_);
lean_dec_ref(v_a_2302_);
lean_dec(v_a_2301_);
lean_dec_ref(v_a_2300_);
return v_res_2307_;
}
}
lean_object* l_Lean_Meta_Grind_NormSym_simpOr(lean_object* v_e_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v___x_2319_; 
v___x_2319_ = l_Lean_Meta_Grind_NormSym_simpOr___redArg(v_e_2308_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
return v___x_2319_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_NormSym_simpOr_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2308_ = stack[0].m_obj;
lean_object* v_a_2309_ = stack[1].m_obj;
lean_object* v_a_2310_ = stack[2].m_obj;
lean_object* v_a_2311_ = stack[3].m_obj;
lean_object* v_a_2312_ = stack[4].m_obj;
lean_object* v_a_2313_ = stack[5].m_obj;
lean_object* v_a_2314_ = stack[6].m_obj;
lean_object* v_a_2315_ = stack[7].m_obj;
lean_object* v_a_2316_ = stack[8].m_obj;
lean_object* v_a_2317_ = stack[9].m_obj;
lean_object* v_res_2320_;
v_res_2320_ = l_Lean_Meta_Grind_NormSym_simpOr(v_e_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
stack->m_obj
 = v_res_2320_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr___boxed(lean_object* v_e_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Lean_Meta_Grind_NormSym_simpOr(v_e_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
lean_dec(v_a_2330_);
lean_dec_ref(v_a_2329_);
lean_dec(v_a_2328_);
lean_dec_ref(v_a_2327_);
lean_dec(v_a_2326_);
lean_dec_ref(v_a_2325_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
lean_dec(v_a_2322_);
return v_res_2332_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2333_ = lean_box(0);
v___x_2334_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__6));
v___x_2335_ = l_Lean_mkConst(v___x_2334_, v___x_2333_);
return v___x_2335_;
}
}
lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0(uint8_t v___x_2336_, uint8_t v___x_2337_, lean_object* v_h_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v___y_2350_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2359_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0, &l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0);
lean_inc_ref(v_h_2338_);
v___x_2360_ = l_Lean_Meta_mkNoConfusion(v___x_2359_, v_h_2338_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; uint8_t v___x_2365_; lean_object* v___x_2366_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2360_, 1);
v___x_2362_ = lean_unsigned_to_nat(1u);
v___x_2363_ = lean_mk_empty_array_with_capacity(v___x_2362_);
v___x_2364_ = lean_array_push(v___x_2363_, v_h_2338_);
v___x_2365_ = 1;
v___x_2366_ = l_Lean_Meta_mkLambdaFVars(v___x_2364_, v_a_2361_, v___x_2336_, v___x_2337_, v___x_2336_, v___x_2337_, v___x_2365_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
lean_dec_ref(v___x_2364_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2368_; uint8_t v_transparency_2369_; uint8_t v___x_2370_; uint8_t v___x_2371_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2368_ = l_Lean_Meta_Context_config(v___y_2344_);
v_transparency_2369_ = lean_ctor_get_uint8(v___x_2368_, 9);
lean_dec_ref(v___x_2368_);
v___x_2370_ = 1;
v___x_2371_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2369_, v___x_2370_);
if (v___x_2371_ == 0)
{
lean_object* v_keyedConfig_2372_; uint8_t v_trackZetaDelta_2373_; lean_object* v_zetaDeltaSet_2374_; lean_object* v_lctx_2375_; lean_object* v_localInstances_2376_; lean_object* v_defEqCtx_x3f_2377_; lean_object* v_synthPendingDepth_2378_; lean_object* v_customCanUnfoldPredicate_x3f_2379_; uint8_t v_univApprox_2380_; uint8_t v_inTypeClassResolution_2381_; uint8_t v_cacheInferType_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v_keyedConfig_2372_ = lean_ctor_get(v___y_2344_, 0);
v_trackZetaDelta_2373_ = lean_ctor_get_uint8(v___y_2344_, sizeof(void*)*7);
v_zetaDeltaSet_2374_ = lean_ctor_get(v___y_2344_, 1);
v_lctx_2375_ = lean_ctor_get(v___y_2344_, 2);
v_localInstances_2376_ = lean_ctor_get(v___y_2344_, 3);
v_defEqCtx_x3f_2377_ = lean_ctor_get(v___y_2344_, 4);
v_synthPendingDepth_2378_ = lean_ctor_get(v___y_2344_, 5);
v_customCanUnfoldPredicate_x3f_2379_ = lean_ctor_get(v___y_2344_, 6);
v_univApprox_2380_ = lean_ctor_get_uint8(v___y_2344_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2381_ = lean_ctor_get_uint8(v___y_2344_, sizeof(void*)*7 + 2);
v_cacheInferType_2382_ = lean_ctor_get_uint8(v___y_2344_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2372_);
v___x_2383_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2370_, v_keyedConfig_2372_);
lean_inc(v_customCanUnfoldPredicate_x3f_2379_);
lean_inc(v_synthPendingDepth_2378_);
lean_inc(v_defEqCtx_x3f_2377_);
lean_inc_ref(v_localInstances_2376_);
lean_inc_ref(v_lctx_2375_);
lean_inc(v_zetaDeltaSet_2374_);
v___x_2384_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2384_, 0, v___x_2383_);
lean_ctor_set(v___x_2384_, 1, v_zetaDeltaSet_2374_);
lean_ctor_set(v___x_2384_, 2, v_lctx_2375_);
lean_ctor_set(v___x_2384_, 3, v_localInstances_2376_);
lean_ctor_set(v___x_2384_, 4, v_defEqCtx_x3f_2377_);
lean_ctor_set(v___x_2384_, 5, v_synthPendingDepth_2378_);
lean_ctor_set(v___x_2384_, 6, v_customCanUnfoldPredicate_x3f_2379_);
lean_ctor_set_uint8(v___x_2384_, sizeof(void*)*7, v_trackZetaDelta_2373_);
lean_ctor_set_uint8(v___x_2384_, sizeof(void*)*7 + 1, v_univApprox_2380_);
lean_ctor_set_uint8(v___x_2384_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2381_);
lean_ctor_set_uint8(v___x_2384_, sizeof(void*)*7 + 3, v_cacheInferType_2382_);
v___x_2385_ = l_Lean_Meta_mkEqFalse_x27(v_a_2367_, v___x_2384_, v___y_2345_, v___y_2346_, v___y_2347_);
lean_dec_ref_known(v___x_2384_, 7);
v___y_2350_ = v___x_2385_;
goto v___jp_2349_;
}
else
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_Meta_mkEqFalse_x27(v_a_2367_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
v___y_2350_ = v___x_2386_;
goto v___jp_2349_;
}
}
else
{
return v___x_2366_;
}
}
else
{
lean_dec_ref(v_h_2338_);
return v___x_2360_;
}
v___jp_2349_:
{
if (lean_obj_tag(v___y_2350_) == 0)
{
return v___y_2350_;
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
v_a_2351_ = lean_ctor_get(v___y_2350_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___y_2350_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___y_2350_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___y_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2336_ = stack[0].m_num;
uint8_t v___x_2337_ = stack[1].m_num;
lean_object* v_h_2338_ = stack[2].m_obj;
lean_object* v___y_2339_ = stack[3].m_obj;
lean_object* v___y_2340_ = stack[4].m_obj;
lean_object* v___y_2341_ = stack[5].m_obj;
lean_object* v___y_2342_ = stack[6].m_obj;
lean_object* v___y_2343_ = stack[7].m_obj;
lean_object* v___y_2344_ = stack[8].m_obj;
lean_object* v___y_2345_ = stack[9].m_obj;
lean_object* v___y_2346_ = stack[10].m_obj;
lean_object* v___y_2347_ = stack[11].m_obj;
lean_object* v_res_2387_;
v_res_2387_ = l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0(v___x_2336_, v___x_2337_, v_h_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
stack->m_obj
 = v_res_2387_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___boxed(lean_object* v___x_2388_, lean_object* v___x_2389_, lean_object* v_h_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
uint8_t v___x_16179__boxed_2401_; uint8_t v___x_16180__boxed_2402_; lean_object* v_res_2403_; 
v___x_16179__boxed_2401_ = lean_unbox(v___x_2388_);
v___x_16180__boxed_2402_ = lean_unbox(v___x_2389_);
v_res_2403_ = l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0(v___x_16179__boxed_2401_, v___x_16180__boxed_2402_, v_h_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec(v___y_2391_);
return v_res_2403_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0(lean_object* v_k_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v_b_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v___x_2416_; 
lean_inc(v___y_2414_);
lean_inc_ref(v___y_2413_);
lean_inc(v___y_2412_);
lean_inc_ref(v___y_2411_);
lean_inc(v___y_2409_);
lean_inc_ref(v___y_2408_);
lean_inc(v___y_2407_);
lean_inc_ref(v___y_2406_);
lean_inc(v___y_2405_);
v___x_2416_ = lean_apply_11(v_k_2404_, v_b_2410_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, lean_box(0));
return v___x_2416_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2404_ = stack[0].m_obj;
lean_object* v___y_2405_ = stack[1].m_obj;
lean_object* v___y_2406_ = stack[2].m_obj;
lean_object* v___y_2407_ = stack[3].m_obj;
lean_object* v___y_2408_ = stack[4].m_obj;
lean_object* v___y_2409_ = stack[5].m_obj;
lean_object* v_b_2410_ = stack[6].m_obj;
lean_object* v___y_2411_ = stack[7].m_obj;
lean_object* v___y_2412_ = stack[8].m_obj;
lean_object* v___y_2413_ = stack[9].m_obj;
lean_object* v___y_2414_ = stack[10].m_obj;
lean_object* v_res_2417_;
v_res_2417_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0(v_k_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v_b_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
stack->m_obj
 = v_res_2417_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v_b_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0(v_k_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v_b_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
return v_res_2430_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(lean_object* v_name_2431_, uint8_t v_bi_2432_, lean_object* v_type_2433_, lean_object* v_k_2434_, uint8_t v_kind_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v___f_2446_; lean_object* v___x_2447_; 
lean_inc(v___y_2440_);
lean_inc_ref(v___y_2439_);
lean_inc(v___y_2438_);
lean_inc_ref(v___y_2437_);
lean_inc(v___y_2436_);
v___f_2446_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_2446_, 0, v_k_2434_);
lean_closure_set(v___f_2446_, 1, v___y_2436_);
lean_closure_set(v___f_2446_, 2, v___y_2437_);
lean_closure_set(v___f_2446_, 3, v___y_2438_);
lean_closure_set(v___f_2446_, 4, v___y_2439_);
lean_closure_set(v___f_2446_, 5, v___y_2440_);
v___x_2447_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2431_, v_bi_2432_, v_type_2433_, v___f_2446_, v_kind_2435_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
if (lean_obj_tag(v___x_2447_) == 0)
{
return v___x_2447_;
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2447_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2447_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2431_ = stack[0].m_obj;
uint8_t v_bi_2432_ = stack[1].m_num;
lean_object* v_type_2433_ = stack[2].m_obj;
lean_object* v_k_2434_ = stack[3].m_obj;
uint8_t v_kind_2435_ = stack[4].m_num;
lean_object* v___y_2436_ = stack[5].m_obj;
lean_object* v___y_2437_ = stack[6].m_obj;
lean_object* v___y_2438_ = stack[7].m_obj;
lean_object* v___y_2439_ = stack[8].m_obj;
lean_object* v___y_2440_ = stack[9].m_obj;
lean_object* v___y_2441_ = stack[10].m_obj;
lean_object* v___y_2442_ = stack[11].m_obj;
lean_object* v___y_2443_ = stack[12].m_obj;
lean_object* v___y_2444_ = stack[13].m_obj;
lean_object* v_res_2456_;
v_res_2456_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(v_name_2431_, v_bi_2432_, v_type_2433_, v_k_2434_, v_kind_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
stack->m_obj
 = v_res_2456_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___boxed(lean_object* v_name_2457_, lean_object* v_bi_2458_, lean_object* v_type_2459_, lean_object* v_k_2460_, lean_object* v_kind_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
uint8_t v_bi_boxed_2472_; uint8_t v_kind_boxed_2473_; lean_object* v_res_2474_; 
v_bi_boxed_2472_ = lean_unbox(v_bi_2458_);
v_kind_boxed_2473_ = lean_unbox(v_kind_2461_);
v_res_2474_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(v_name_2457_, v_bi_boxed_2472_, v_type_2459_, v_k_2460_, v_kind_boxed_2473_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
return v_res_2474_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(lean_object* v_name_2475_, lean_object* v_type_2476_, lean_object* v_k_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
uint8_t v___x_2488_; uint8_t v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = 0;
v___x_2489_ = 0;
v___x_2490_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(v_name_2475_, v___x_2488_, v_type_2476_, v_k_2477_, v___x_2489_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2490_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2475_ = stack[0].m_obj;
lean_object* v_type_2476_ = stack[1].m_obj;
lean_object* v_k_2477_ = stack[2].m_obj;
lean_object* v___y_2478_ = stack[3].m_obj;
lean_object* v___y_2479_ = stack[4].m_obj;
lean_object* v___y_2480_ = stack[5].m_obj;
lean_object* v___y_2481_ = stack[6].m_obj;
lean_object* v___y_2482_ = stack[7].m_obj;
lean_object* v___y_2483_ = stack[8].m_obj;
lean_object* v___y_2484_ = stack[9].m_obj;
lean_object* v___y_2485_ = stack[10].m_obj;
lean_object* v___y_2486_ = stack[11].m_obj;
lean_object* v_res_2491_;
v_res_2491_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_name_2475_, v_type_2476_, v_k_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
stack->m_obj
 = v_res_2491_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg___boxed(lean_object* v_name_2492_, lean_object* v_type_2493_, lean_object* v_k_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_name_2492_, v_type_2493_, v_k_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
return v_res_2505_;
}
}
lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq(lean_object* v_e_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_){
_start:
{
lean_object* v___x_2523_; uint8_t v___x_2524_; 
lean_inc_ref(v_e_2509_);
v___x_2523_ = l_Lean_Expr_cleanupAnnotations(v_e_2509_);
v___x_2524_ = l_Lean_Expr_isApp(v___x_2523_);
if (v___x_2524_ == 0)
{
lean_dec_ref(v___x_2523_);
lean_dec_ref(v_e_2509_);
goto v___jp_2520_;
}
else
{
lean_object* v_arg_2525_; lean_object* v___x_2526_; uint8_t v___x_2527_; 
v_arg_2525_ = lean_ctor_get(v___x_2523_, 1);
lean_inc_ref(v_arg_2525_);
v___x_2526_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2523_);
v___x_2527_ = l_Lean_Expr_isApp(v___x_2526_);
if (v___x_2527_ == 0)
{
lean_dec_ref(v___x_2526_);
lean_dec_ref(v_arg_2525_);
lean_dec_ref(v_e_2509_);
goto v___jp_2520_;
}
else
{
lean_object* v_arg_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v_arg_2528_ = lean_ctor_get(v___x_2526_, 1);
lean_inc_ref(v_arg_2528_);
v___x_2529_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2526_);
v___x_2530_ = l_Lean_Expr_isApp(v___x_2529_);
if (v___x_2530_ == 0)
{
lean_dec_ref(v___x_2529_);
lean_dec_ref(v_arg_2528_);
lean_dec_ref(v_arg_2525_);
lean_dec_ref(v_e_2509_);
goto v___jp_2520_;
}
else
{
lean_object* v___x_2531_; lean_object* v___x_2532_; uint8_t v___x_2533_; 
v___x_2531_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2529_);
v___x_2532_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__1));
v___x_2533_ = l_Lean_Expr_isConstOf(v___x_2531_, v___x_2532_);
lean_dec_ref(v___x_2531_);
if (v___x_2533_ == 0)
{
lean_dec_ref(v_arg_2528_);
lean_dec_ref(v_arg_2525_);
lean_dec_ref(v_e_2509_);
goto v___jp_2520_;
}
else
{
lean_object* v___x_2534_; 
v___x_2534_ = l_Lean_Meta_isConstructorApp_x3f(v_arg_2528_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2604_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2537_ = v___x_2534_;
v_isShared_2538_ = v_isSharedCheck_2604_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2534_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2604_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
if (lean_obj_tag(v_a_2535_) == 1)
{
lean_object* v_val_2539_; lean_object* v___x_2540_; 
lean_del_object(v___x_2537_);
v_val_2539_ = lean_ctor_get(v_a_2535_, 0);
lean_inc(v_val_2539_);
lean_dec_ref_known(v_a_2535_, 1);
v___x_2540_ = l_Lean_Meta_isConstructorApp_x3f(v_arg_2525_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2591_; 
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2543_ = v___x_2540_;
v_isShared_2544_ = v_isSharedCheck_2591_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2540_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2591_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
if (lean_obj_tag(v_a_2541_) == 1)
{
lean_object* v_toConstantVal_2545_; lean_object* v_val_2546_; lean_object* v_toConstantVal_2547_; lean_object* v_name_2548_; lean_object* v_name_2549_; uint8_t v___x_2550_; 
v_toConstantVal_2545_ = lean_ctor_get(v_val_2539_, 0);
lean_inc_ref(v_toConstantVal_2545_);
lean_dec(v_val_2539_);
v_val_2546_ = lean_ctor_get(v_a_2541_, 0);
lean_inc(v_val_2546_);
lean_dec_ref_known(v_a_2541_, 1);
v_toConstantVal_2547_ = lean_ctor_get(v_val_2546_, 0);
lean_inc_ref(v_toConstantVal_2547_);
lean_dec(v_val_2546_);
v_name_2548_ = lean_ctor_get(v_toConstantVal_2545_, 0);
lean_inc(v_name_2548_);
lean_dec_ref(v_toConstantVal_2545_);
v_name_2549_ = lean_ctor_get(v_toConstantVal_2547_, 0);
lean_inc(v_name_2549_);
lean_dec_ref(v_toConstantVal_2547_);
v___x_2550_ = lean_name_eq(v_name_2548_, v_name_2549_);
lean_dec(v_name_2549_);
lean_dec(v_name_2548_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___f_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_del_object(v___x_2543_);
v___x_2551_ = lean_box(v___x_2550_);
v___x_2552_ = lean_box(v___x_2533_);
v___f_2553_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2553_, 0, v___x_2551_);
lean_closure_set(v___f_2553_, 1, v___x_2552_);
v___x_2554_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_reduceCtorEq___closed__1));
v___x_2555_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v___x_2554_, v_e_2509_, v___f_2553_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2557_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___x_2555_, 1);
v___x_2557_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2513_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2566_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2560_ = v___x_2557_;
v_isShared_2561_ = v_isSharedCheck_2566_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2557_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2566_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2562_; lean_object* v___x_2564_; 
v___x_2562_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2562_, 0, v_a_2558_);
lean_ctor_set(v___x_2562_, 1, v_a_2556_);
lean_ctor_set_uint8(v___x_2562_, sizeof(void*)*2, v___x_2533_);
lean_ctor_set_uint8(v___x_2562_, sizeof(void*)*2 + 1, v___x_2550_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v___x_2562_);
v___x_2564_ = v___x_2560_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2562_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_dec(v_a_2556_);
v_a_2567_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2557_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2557_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
else
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2582_; 
v_a_2575_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2582_ == 0)
{
v___x_2577_ = v___x_2555_;
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2555_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2582_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_a_2575_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
else
{
lean_object* v___x_2583_; lean_object* v___x_2585_; 
lean_dec_ref(v_e_2509_);
v___x_2583_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v___x_2583_);
v___x_2585_ = v___x_2543_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
else
{
lean_object* v___x_2587_; lean_object* v___x_2589_; 
lean_dec(v_a_2541_);
lean_dec(v_val_2539_);
lean_dec_ref(v_e_2509_);
v___x_2587_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 0, v___x_2587_);
v___x_2589_ = v___x_2543_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v_val_2539_);
lean_dec_ref(v_e_2509_);
v_a_2592_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2540_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2540_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_object* v___x_2600_; lean_object* v___x_2602_; 
lean_dec(v_a_2535_);
lean_dec_ref(v_arg_2525_);
lean_dec_ref(v_e_2509_);
v___x_2600_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 0, v___x_2600_);
v___x_2602_ = v___x_2537_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec_ref(v_arg_2525_);
lean_dec_ref(v_e_2509_);
v_a_2605_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2534_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2534_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
}
}
}
v___jp_2520_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
return v___x_2522_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_NormSym_reduceCtorEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2509_ = stack[0].m_obj;
lean_object* v_a_2510_ = stack[1].m_obj;
lean_object* v_a_2511_ = stack[2].m_obj;
lean_object* v_a_2512_ = stack[3].m_obj;
lean_object* v_a_2513_ = stack[4].m_obj;
lean_object* v_a_2514_ = stack[5].m_obj;
lean_object* v_a_2515_ = stack[6].m_obj;
lean_object* v_a_2516_ = stack[7].m_obj;
lean_object* v_a_2517_ = stack[8].m_obj;
lean_object* v_a_2518_ = stack[9].m_obj;
lean_object* v_res_2613_;
v_res_2613_ = l_Lean_Meta_Grind_NormSym_reduceCtorEq(v_e_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_);
stack->m_obj
 = v_res_2613_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___boxed(lean_object* v_e_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Lean_Meta_Grind_NormSym_reduceCtorEq(v_e_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_);
lean_dec(v_a_2623_);
lean_dec_ref(v_a_2622_);
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec(v_a_2619_);
lean_dec_ref(v_a_2618_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec(v_a_2615_);
return v_res_2625_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0(lean_object* v_00_u03b1_2626_, lean_object* v_name_2627_, uint8_t v_bi_2628_, lean_object* v_type_2629_, lean_object* v_k_2630_, uint8_t v_kind_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(v_name_2627_, v_bi_2628_, v_type_2629_, v_k_2630_, v_kind_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
return v___x_2642_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2627_ = stack[1].m_obj;
uint8_t v_bi_2628_ = stack[2].m_num;
lean_object* v_type_2629_ = stack[3].m_obj;
lean_object* v_k_2630_ = stack[4].m_obj;
uint8_t v_kind_2631_ = stack[5].m_num;
lean_object* v___y_2632_ = stack[6].m_obj;
lean_object* v___y_2633_ = stack[7].m_obj;
lean_object* v___y_2634_ = stack[8].m_obj;
lean_object* v___y_2635_ = stack[9].m_obj;
lean_object* v___y_2636_ = stack[10].m_obj;
lean_object* v___y_2637_ = stack[11].m_obj;
lean_object* v___y_2638_ = stack[12].m_obj;
lean_object* v___y_2639_ = stack[13].m_obj;
lean_object* v___y_2640_ = stack[14].m_obj;
lean_object* v_res_2643_;
v_res_2643_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0(lean_box(0), v_name_2627_, v_bi_2628_, v_type_2629_, v_k_2630_, v_kind_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
stack->m_obj
 = v_res_2643_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2644_, lean_object* v_name_2645_, lean_object* v_bi_2646_, lean_object* v_type_2647_, lean_object* v_k_2648_, lean_object* v_kind_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
uint8_t v_bi_boxed_2660_; uint8_t v_kind_boxed_2661_; lean_object* v_res_2662_; 
v_bi_boxed_2660_ = lean_unbox(v_bi_2646_);
v_kind_boxed_2661_ = lean_unbox(v_kind_2649_);
v_res_2662_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0(v_00_u03b1_2644_, v_name_2645_, v_bi_boxed_2660_, v_type_2647_, v_k_2648_, v_kind_boxed_2661_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
return v_res_2662_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0(lean_object* v_00_u03b1_2663_, lean_object* v_name_2664_, lean_object* v_type_2665_, lean_object* v_k_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v___x_2677_; 
v___x_2677_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_name_2664_, v_type_2665_, v_k_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
return v___x_2677_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2664_ = stack[1].m_obj;
lean_object* v_type_2665_ = stack[2].m_obj;
lean_object* v_k_2666_ = stack[3].m_obj;
lean_object* v___y_2667_ = stack[4].m_obj;
lean_object* v___y_2668_ = stack[5].m_obj;
lean_object* v___y_2669_ = stack[6].m_obj;
lean_object* v___y_2670_ = stack[7].m_obj;
lean_object* v___y_2671_ = stack[8].m_obj;
lean_object* v___y_2672_ = stack[9].m_obj;
lean_object* v___y_2673_ = stack[10].m_obj;
lean_object* v___y_2674_ = stack[11].m_obj;
lean_object* v___y_2675_ = stack[12].m_obj;
lean_object* v_res_2678_;
v_res_2678_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0(lean_box(0), v_name_2664_, v_type_2665_, v_k_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
stack->m_obj
 = v_res_2678_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___boxed(lean_object* v_00_u03b1_2679_, lean_object* v_name_2680_, lean_object* v_type_2681_, lean_object* v_k_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0(v_00_u03b1_2679_, v_name_2680_, v_type_2681_, v_k_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(lean_object* v_e_2694_){
_start:
{
if (lean_obj_tag(v_e_2694_) == 7)
{
lean_object* v_binderName_2695_; lean_object* v_binderType_2696_; lean_object* v_body_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v_binderName_2695_ = lean_ctor_get(v_e_2694_, 0);
v_binderType_2696_ = lean_ctor_get(v_e_2694_, 1);
v_body_2697_ = lean_ctor_get(v_e_2694_, 2);
lean_inc_ref(v_body_2697_);
lean_inc_ref(v_binderType_2696_);
v___x_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2698_, 0, v_binderType_2696_);
lean_ctor_set(v___x_2698_, 1, v_body_2697_);
lean_inc(v_binderName_2695_);
v___x_2699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2699_, 0, v_binderName_2695_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
return v___x_2700_;
}
else
{
lean_object* v___x_2701_; lean_object* v___x_2702_; uint8_t v___x_2703_; 
v___x_2701_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS___closed__1));
v___x_2702_ = lean_unsigned_to_nat(1u);
v___x_2703_ = l_Lean_Expr_isAppOfArity(v_e_2694_, v___x_2701_, v___x_2702_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2704_; 
v___x_2704_ = lean_box(0);
return v___x_2704_;
}
else
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2705_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__28));
v___x_2706_ = l_Lean_Expr_appArg_x21(v_e_2694_);
v___x_2707_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0, &l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0);
v___x_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2706_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2705_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2709_);
return v___x_2710_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f___boxed(lean_object* v_e_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(v_e_2711_);
lean_dec_ref(v_e_2711_);
return v_res_2712_;
}
}
lean_object* l_Lean_Meta_Grind_NormSym_simpForall___lam__0(lean_object* v_fst_2713_, lean_object* v_a_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2725_ = lean_expr_instantiate1(v_fst_2713_, v_a_2714_);
v___x_2726_ = l_Lean_Meta_getLevel(v___x_2725_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
return v___x_2726_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_NormSym_simpForall___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_2713_ = stack[0].m_obj;
lean_object* v_a_2714_ = stack[1].m_obj;
lean_object* v___y_2715_ = stack[2].m_obj;
lean_object* v___y_2716_ = stack[3].m_obj;
lean_object* v___y_2717_ = stack[4].m_obj;
lean_object* v___y_2718_ = stack[5].m_obj;
lean_object* v___y_2719_ = stack[6].m_obj;
lean_object* v___y_2720_ = stack[7].m_obj;
lean_object* v___y_2721_ = stack[8].m_obj;
lean_object* v___y_2722_ = stack[9].m_obj;
lean_object* v___y_2723_ = stack[10].m_obj;
lean_object* v_res_2727_;
v_res_2727_ = l_Lean_Meta_Grind_NormSym_simpForall___lam__0(v_fst_2713_, v_a_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
stack->m_obj
 = v_res_2727_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpForall___lam__0___boxed(lean_object* v_fst_2728_, lean_object* v_a_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Lean_Meta_Grind_NormSym_simpForall___lam__0(v_fst_2728_, v_a_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v_a_2729_);
lean_dec_ref(v_fst_2728_);
return v_res_2740_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__6(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2756_ = lean_box(0);
v___x_2757_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__5));
v___x_2758_ = l_Lean_mkConst(v___x_2757_, v___x_2756_);
return v___x_2758_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__9(void){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2764_ = lean_box(0);
v___x_2765_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__8));
v___x_2766_ = l_Lean_mkConst(v___x_2765_, v___x_2764_);
return v___x_2766_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__12(void){
_start:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2772_ = lean_box(0);
v___x_2773_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__11));
v___x_2774_ = l_Lean_mkConst(v___x_2773_, v___x_2772_);
return v___x_2774_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__15(void){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2780_ = lean_box(0);
v___x_2781_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__14));
v___x_2782_ = l_Lean_mkConst(v___x_2781_, v___x_2780_);
return v___x_2782_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__18(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2788_ = lean_box(0);
v___x_2789_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__17));
v___x_2790_ = l_Lean_mkConst(v___x_2789_, v___x_2788_);
return v___x_2790_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__23(void){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2800_ = lean_box(0);
v___x_2801_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__22));
v___x_2802_ = l_Lean_mkConst(v___x_2801_, v___x_2800_);
return v___x_2802_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__24(void){
_start:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = lean_unsigned_to_nat(0u);
v___x_2804_ = l_Lean_Level_ofNat(v___x_2803_);
return v___x_2804_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__25(void){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__24, &l_Lean_Meta_Grind_NormSym_simpForall___closed__24_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__24);
v___x_2806_ = l_Lean_mkSort(v___x_2805_);
return v___x_2806_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__28(void){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2810_ = lean_box(0);
v___x_2811_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__27));
v___x_2812_ = l_Lean_mkConst(v___x_2811_, v___x_2810_);
return v___x_2812_;
}
}
lean_object* l_Lean_Meta_Grind_NormSym_simpForall(lean_object* v_e_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_){
_start:
{
lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; 
if (lean_obj_tag(v_e_2813_) == 7)
{
lean_object* v_binderName_2896_; lean_object* v_binderType_2897_; lean_object* v_body_2898_; uint8_t v_binderInfo_2899_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2905_; lean_object* v___y_2906_; lean_object* v___y_2907_; lean_object* v___y_2908_; lean_object* v___y_2909_; uint8_t v___y_2910_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; uint8_t v___x_3138_; 
v_binderName_2896_ = lean_ctor_get(v_e_2813_, 0);
v_binderType_2897_ = lean_ctor_get(v_e_2813_, 1);
v_body_2898_ = lean_ctor_get(v_e_2813_, 2);
v_binderInfo_2899_ = lean_ctor_get_uint8(v_e_2813_, sizeof(void*)*3 + 8);
v___x_3138_ = l_Lean_Expr_hasLooseBVars(v_body_2898_);
if (v___x_3138_ == 0)
{
uint8_t v___x_3139_; lean_object* v___x_3140_; 
v___x_3139_ = 1;
lean_inc_ref(v_binderType_2897_);
v___x_3140_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_2897_, v_a_2820_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; uint8_t v___x_3144_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
lean_dec_ref_known(v___x_3140_, 1);
v___x_3142_ = l_Lean_Expr_cleanupAnnotations(v_a_3141_);
v___x_3143_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__6));
v___x_3144_ = l_Lean_Expr_isConstOf(v___x_3142_, v___x_3143_);
if (v___x_3144_ == 0)
{
lean_object* v___x_3145_; uint8_t v___x_3146_; 
v___x_3145_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_3146_ = l_Lean_Expr_isConstOf(v___x_3142_, v___x_3145_);
lean_dec_ref(v___x_3142_);
if (v___x_3146_ == 0)
{
lean_object* v___x_3147_; 
lean_inc_ref(v_body_2898_);
v___x_3147_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_body_2898_, v_a_2820_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; lean_object* v___x_3149_; uint8_t v___x_3150_; 
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
lean_inc(v_a_3148_);
lean_dec_ref_known(v___x_3147_, 1);
v___x_3149_ = l_Lean_Expr_cleanupAnnotations(v_a_3148_);
v___x_3150_ = l_Lean_Expr_isConstOf(v___x_3149_, v___x_3143_);
if (v___x_3150_ == 0)
{
uint8_t v___x_3151_; 
v___x_3151_ = l_Lean_Expr_isConstOf(v___x_3149_, v___x_3145_);
lean_dec_ref(v___x_3149_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; 
lean_inc_ref(v_binderType_2897_);
v___x_3152_ = l_Lean_Meta_isProp(v_binderType_2897_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; size_t v___x_3154_; size_t v___x_3155_; uint8_t v___x_3156_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_a_3153_);
lean_dec_ref_known(v___x_3152_, 1);
v___x_3154_ = lean_ptr_addr(v_binderType_2897_);
v___x_3155_ = lean_ptr_addr(v_body_2898_);
v___x_3156_ = lean_usize_dec_eq(v___x_3154_, v___x_3155_);
if (v___x_3156_ == 0)
{
lean_dec(v_a_3153_);
v___y_3125_ = v_a_2814_;
v___y_3126_ = v_a_2815_;
v___y_3127_ = v_a_2816_;
v___y_3128_ = v_a_2817_;
v___y_3129_ = v_a_2818_;
v___y_3130_ = v_a_2819_;
v___y_3131_ = v_a_2820_;
v___y_3132_ = v_a_2821_;
v___y_3133_ = v_a_2822_;
goto v___jp_3124_;
}
else
{
uint8_t v___x_3157_; 
v___x_3157_ = lean_unbox(v_a_3153_);
lean_dec(v_a_3153_);
if (v___x_3157_ == 0)
{
v___y_3125_ = v_a_2814_;
v___y_3126_ = v_a_2815_;
v___y_3127_ = v_a_2816_;
v___y_3128_ = v_a_2817_;
v___y_3129_ = v_a_2818_;
v___y_3130_ = v_a_2819_;
v___y_3131_ = v_a_2820_;
v___y_3132_ = v_a_2821_;
v___y_3133_ = v_a_2822_;
goto v___jp_3124_;
}
else
{
lean_object* v___x_3158_; 
lean_inc_ref(v_binderType_2897_);
lean_dec_ref_known(v_e_2813_, 3);
v___x_3158_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2817_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3169_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3161_ = v___x_3158_;
v_isShared_3162_ = v_isSharedCheck_3169_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3158_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3169_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3167_; 
v___x_3163_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__6, &l_Lean_Meta_Grind_NormSym_simpForall___closed__6_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__6);
v___x_3164_ = l_Lean_Expr_app___override(v___x_3163_, v_binderType_2897_);
v___x_3165_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3165_, 0, v_a_3159_);
lean_ctor_set(v___x_3165_, 1, v___x_3164_);
lean_ctor_set_uint8(v___x_3165_, sizeof(void*)*2, v___x_3139_);
lean_ctor_set_uint8(v___x_3165_, sizeof(void*)*2 + 1, v___x_3151_);
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 0, v___x_3165_);
v___x_3167_ = v___x_3161_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v___x_3165_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
else
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3177_; 
lean_dec_ref(v_binderType_2897_);
v_a_3170_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3172_ = v___x_3158_;
v_isShared_3173_ = v_isSharedCheck_3177_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3158_);
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
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_dec_ref_known(v_e_2813_, 3);
v_a_3178_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3152_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3152_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
if (v_isShared_3181_ == 0)
{
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
}
else
{
lean_object* v___x_3186_; 
lean_inc_ref(v_binderType_2897_);
v___x_3186_ = l_Lean_Meta_isProp(v_binderType_2897_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v_a_3187_; uint8_t v___x_3188_; 
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
lean_inc(v_a_3187_);
lean_dec_ref_known(v___x_3186_, 1);
v___x_3188_ = lean_unbox(v_a_3187_);
lean_dec(v_a_3187_);
if (v___x_3188_ == 0)
{
v___y_3125_ = v_a_2814_;
v___y_3126_ = v_a_2815_;
v___y_3127_ = v_a_2816_;
v___y_3128_ = v_a_2817_;
v___y_3129_ = v_a_2818_;
v___y_3130_ = v_a_2819_;
v___y_3131_ = v_a_2820_;
v___y_3132_ = v_a_2821_;
v___y_3133_ = v_a_2822_;
goto v___jp_3124_;
}
else
{
lean_object* v___x_3189_; 
lean_inc_ref(v_binderType_2897_);
lean_dec_ref_known(v_e_2813_, 3);
v___x_3189_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2817_);
if (lean_obj_tag(v___x_3189_) == 0)
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3200_; 
v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3192_ = v___x_3189_;
v_isShared_3193_ = v_isSharedCheck_3200_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3189_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3200_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3198_; 
v___x_3194_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__9, &l_Lean_Meta_Grind_NormSym_simpForall___closed__9_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__9);
v___x_3195_ = l_Lean_Expr_app___override(v___x_3194_, v_binderType_2897_);
v___x_3196_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3196_, 0, v_a_3190_);
lean_ctor_set(v___x_3196_, 1, v___x_3195_);
lean_ctor_set_uint8(v___x_3196_, sizeof(void*)*2, v___x_3139_);
lean_ctor_set_uint8(v___x_3196_, sizeof(void*)*2 + 1, v___x_3150_);
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 0, v___x_3196_);
v___x_3198_ = v___x_3192_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3196_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_dec_ref(v_binderType_2897_);
v_a_3201_ = lean_ctor_get(v___x_3189_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3189_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3189_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3189_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_dec_ref_known(v_e_2813_, 3);
v_a_3209_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3186_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3186_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
}
else
{
lean_object* v___x_3217_; 
lean_dec_ref(v___x_3149_);
lean_inc_ref(v_binderType_2897_);
v___x_3217_ = l_Lean_Meta_isProp(v_binderType_2897_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; uint8_t v___x_3219_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref_known(v___x_3217_, 1);
v___x_3219_ = lean_unbox(v_a_3218_);
lean_dec(v_a_3218_);
if (v___x_3219_ == 0)
{
v___y_3125_ = v_a_2814_;
v___y_3126_ = v_a_2815_;
v___y_3127_ = v_a_2816_;
v___y_3128_ = v_a_2817_;
v___y_3129_ = v_a_2818_;
v___y_3130_ = v_a_2819_;
v___y_3131_ = v_a_2820_;
v___y_3132_ = v_a_2821_;
v___y_3133_ = v_a_2822_;
goto v___jp_3124_;
}
else
{
lean_object* v___x_3220_; 
lean_inc_ref_n(v_binderType_2897_, 2);
lean_dec_ref_known(v_e_2813_, 3);
v___x_3220_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS(v_binderType_2897_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3231_; 
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3223_ = v___x_3220_;
v_isShared_3224_ = v_isSharedCheck_3231_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3220_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3231_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3229_; 
v___x_3225_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__12, &l_Lean_Meta_Grind_NormSym_simpForall___closed__12_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__12);
v___x_3226_ = l_Lean_Expr_app___override(v___x_3225_, v_binderType_2897_);
v___x_3227_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3227_, 0, v_a_3221_);
lean_ctor_set(v___x_3227_, 1, v___x_3226_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*2, v___x_3146_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*2 + 1, v___x_3146_);
if (v_isShared_3224_ == 0)
{
lean_ctor_set(v___x_3223_, 0, v___x_3227_);
v___x_3229_ = v___x_3223_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3227_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
lean_dec_ref(v_binderType_2897_);
v_a_3232_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_3220_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3220_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec_ref_known(v_e_2813_, 3);
v_a_3240_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3217_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3217_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec_ref_known(v_e_2813_, 3);
v_a_3248_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3147_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3147_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
else
{
lean_object* v___x_3256_; 
lean_inc_ref(v_body_2898_);
v___x_3256_ = l_Lean_Meta_isProp(v_body_2898_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3268_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3259_ = v___x_3256_;
v_isShared_3260_ = v_isSharedCheck_3268_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3256_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3268_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
uint8_t v___x_3261_; 
v___x_3261_ = lean_unbox(v_a_3257_);
lean_dec(v_a_3257_);
if (v___x_3261_ == 0)
{
lean_del_object(v___x_3259_);
v___y_3125_ = v_a_2814_;
v___y_3126_ = v_a_2815_;
v___y_3127_ = v_a_2816_;
v___y_3128_ = v_a_2817_;
v___y_3129_ = v_a_2818_;
v___y_3130_ = v_a_2819_;
v___y_3131_ = v_a_2820_;
v___y_3132_ = v_a_2821_;
v___y_3133_ = v_a_2822_;
goto v___jp_3124_;
}
else
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3266_; 
lean_inc_ref_n(v_body_2898_, 2);
lean_dec_ref_known(v_e_2813_, 3);
v___x_3262_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__15, &l_Lean_Meta_Grind_NormSym_simpForall___closed__15_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__15);
v___x_3263_ = l_Lean_Expr_app___override(v___x_3262_, v_body_2898_);
v___x_3264_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3264_, 0, v_body_2898_);
lean_ctor_set(v___x_3264_, 1, v___x_3263_);
lean_ctor_set_uint8(v___x_3264_, sizeof(void*)*2, v___x_3139_);
lean_ctor_set_uint8(v___x_3264_, sizeof(void*)*2 + 1, v___x_3144_);
if (v_isShared_3260_ == 0)
{
lean_ctor_set(v___x_3259_, 0, v___x_3264_);
v___x_3266_ = v___x_3259_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3264_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
}
else
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3276_; 
lean_dec_ref_known(v_e_2813_, 3);
v_a_3269_ = lean_ctor_get(v___x_3256_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3271_ = v___x_3256_;
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3256_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3272_ == 0)
{
v___x_3274_ = v___x_3271_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_a_3269_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
}
else
{
lean_object* v___x_3277_; 
lean_dec_ref(v___x_3142_);
lean_inc_ref(v_body_2898_);
v___x_3277_ = l_Lean_Meta_isProp(v_body_2898_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; uint8_t v___x_3279_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref_known(v___x_3277_, 1);
v___x_3279_ = lean_unbox(v_a_3278_);
lean_dec(v_a_3278_);
if (v___x_3279_ == 0)
{
v___y_3125_ = v_a_2814_;
v___y_3126_ = v_a_2815_;
v___y_3127_ = v_a_2816_;
v___y_3128_ = v_a_2817_;
v___y_3129_ = v_a_2818_;
v___y_3130_ = v_a_2819_;
v___y_3131_ = v_a_2820_;
v___y_3132_ = v_a_2821_;
v___y_3133_ = v_a_2822_;
goto v___jp_3124_;
}
else
{
lean_object* v___x_3280_; 
lean_inc_ref(v_body_2898_);
lean_dec_ref_known(v_e_2813_, 3);
v___x_3280_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2817_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3291_; 
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3283_ = v___x_3280_;
v_isShared_3284_ = v_isSharedCheck_3291_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3280_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3291_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3289_; 
v___x_3285_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__18, &l_Lean_Meta_Grind_NormSym_simpForall___closed__18_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__18);
v___x_3286_ = l_Lean_Expr_app___override(v___x_3285_, v_body_2898_);
v___x_3287_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3287_, 0, v_a_3281_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
lean_ctor_set_uint8(v___x_3287_, sizeof(void*)*2, v___x_3139_);
lean_ctor_set_uint8(v___x_3287_, sizeof(void*)*2 + 1, v___x_3138_);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 0, v___x_3287_);
v___x_3289_ = v___x_3283_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3287_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
else
{
lean_object* v_a_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3299_; 
lean_dec_ref(v_body_2898_);
v_a_3292_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3294_ = v___x_3280_;
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_a_3292_);
lean_dec(v___x_3280_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3297_; 
if (v_isShared_3295_ == 0)
{
v___x_3297_ = v___x_3294_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_a_3292_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
}
}
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
lean_dec_ref_known(v_e_2813_, 3);
v_a_3300_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3277_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3277_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3300_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
}
else
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
lean_dec_ref_known(v_e_2813_, 3);
v_a_3308_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3310_ = v___x_3140_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3140_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3308_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
else
{
uint8_t v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = 0;
lean_inc_ref(v_binderType_2897_);
v___x_3317_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_2897_, v_a_2820_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v_a_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; uint8_t v___x_3321_; 
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
lean_inc(v_a_3318_);
lean_dec_ref_known(v___x_3317_, 1);
v___x_3319_ = l_Lean_Expr_cleanupAnnotations(v_a_3318_);
v___x_3320_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__6));
v___x_3321_ = l_Lean_Expr_isConstOf(v___x_3319_, v___x_3320_);
if (v___x_3321_ == 0)
{
lean_object* v___x_3322_; uint8_t v___x_3323_; 
v___x_3322_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_3323_ = l_Lean_Expr_isConstOf(v___x_3319_, v___x_3322_);
lean_dec_ref(v___x_3319_);
if (v___x_3323_ == 0)
{
v___y_3125_ = v_a_2814_;
v___y_3126_ = v_a_2815_;
v___y_3127_ = v_a_2816_;
v___y_3128_ = v_a_2817_;
v___y_3129_ = v_a_2818_;
v___y_3130_ = v_a_2819_;
v___y_3131_ = v_a_2820_;
v___y_3132_ = v_a_2821_;
v___y_3133_ = v_a_2822_;
goto v___jp_3124_;
}
else
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3324_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__20));
v___x_3325_ = lean_box(0);
v___x_3326_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v___x_3324_, v___x_3325_, v_a_2818_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref_known(v___x_3326_, 1);
v___x_3328_ = lean_unsigned_to_nat(1u);
v___x_3329_ = lean_mk_empty_array_with_capacity(v___x_3328_);
v___x_3330_ = lean_array_push(v___x_3329_, v_a_3327_);
lean_inc_ref(v_body_2898_);
v___x_3331_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_body_2898_, v___x_3330_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_object* v_a_3332_; lean_object* v___x_3333_; 
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
lean_inc_n(v_a_3332_, 2);
lean_dec_ref_known(v___x_3331_, 1);
v___x_3333_ = l_Lean_Meta_isProp(v_a_3332_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3346_; 
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3336_ = v___x_3333_;
v_isShared_3337_ = v_isSharedCheck_3346_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3333_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3346_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
uint8_t v___x_3338_; 
v___x_3338_ = lean_unbox(v_a_3334_);
lean_dec(v_a_3334_);
if (v___x_3338_ == 0)
{
lean_del_object(v___x_3336_);
lean_dec(v_a_3332_);
v___y_3125_ = v_a_2814_;
v___y_3126_ = v_a_2815_;
v___y_3127_ = v_a_2816_;
v___y_3128_ = v_a_2817_;
v___y_3129_ = v_a_2818_;
v___y_3130_ = v_a_2819_;
v___y_3131_ = v_a_2820_;
v___y_3132_ = v_a_2821_;
v___y_3133_ = v_a_2822_;
goto v___jp_3124_;
}
else
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3344_; 
lean_inc_ref(v_body_2898_);
lean_inc_ref(v_binderType_2897_);
lean_inc(v_binderName_2896_);
lean_dec_ref_known(v_e_2813_, 3);
v___x_3339_ = l_Lean_mkLambda(v_binderName_2896_, v_binderInfo_2899_, v_binderType_2897_, v_body_2898_);
v___x_3340_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__23, &l_Lean_Meta_Grind_NormSym_simpForall___closed__23_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__23);
v___x_3341_ = l_Lean_Expr_app___override(v___x_3340_, v___x_3339_);
v___x_3342_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3342_, 0, v_a_3332_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
lean_ctor_set_uint8(v___x_3342_, sizeof(void*)*2, v___x_3138_);
lean_ctor_set_uint8(v___x_3342_, sizeof(void*)*2 + 1, v___x_3316_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v___x_3342_);
v___x_3344_ = v___x_3336_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_dec(v_a_3332_);
lean_dec_ref_known(v_e_2813_, 3);
v_a_3347_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3333_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3333_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
else
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3362_; 
lean_dec_ref_known(v_e_2813_, 3);
v_a_3355_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3357_ = v___x_3331_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3331_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3360_; 
if (v_isShared_3358_ == 0)
{
v___x_3360_ = v___x_3357_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3355_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
else
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3370_; 
lean_dec_ref_known(v_e_2813_, 3);
v_a_3363_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3365_ = v___x_3326_;
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3326_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3368_; 
if (v_isShared_3366_ == 0)
{
v___x_3368_ = v___x_3365_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
}
else
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
lean_dec_ref(v___x_3319_);
lean_inc_ref(v_body_2898_);
lean_inc_ref(v_binderType_2897_);
lean_inc(v_binderName_2896_);
v___x_3371_ = l_Lean_mkLambda(v_binderName_2896_, v_binderInfo_2899_, v_binderType_2897_, v_body_2898_);
lean_inc(v_a_2822_);
lean_inc_ref(v_a_2821_);
lean_inc(v_a_2820_);
lean_inc_ref(v_a_2819_);
lean_inc_ref(v___x_3371_);
v___x_3372_ = lean_infer_type(v___x_3371_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc(v_a_3373_);
lean_dec_ref_known(v___x_3372_, 1);
v___x_3374_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__25, &l_Lean_Meta_Grind_NormSym_simpForall___closed__25_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__25);
lean_inc_ref(v_binderType_2897_);
lean_inc(v_binderName_2896_);
v___x_3375_ = l_Lean_mkForall(v_binderName_2896_, v_binderInfo_2899_, v_binderType_2897_, v___x_3374_);
v___x_3376_ = l_Lean_Meta_isExprDefEq(v_a_3373_, v___x_3375_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; uint8_t v___x_3378_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_a_3377_);
lean_dec_ref_known(v___x_3376_, 1);
v___x_3378_ = lean_unbox(v_a_3377_);
lean_dec(v_a_3377_);
if (v___x_3378_ == 0)
{
lean_dec_ref(v___x_3371_);
v___y_3125_ = v_a_2814_;
v___y_3126_ = v_a_2815_;
v___y_3127_ = v_a_2816_;
v___y_3128_ = v_a_2817_;
v___y_3129_ = v_a_2818_;
v___y_3130_ = v_a_2819_;
v___y_3131_ = v_a_2820_;
v___y_3132_ = v_a_2821_;
v___y_3133_ = v_a_2822_;
goto v___jp_3124_;
}
else
{
lean_object* v___x_3379_; 
lean_dec_ref_known(v_e_2813_, 3);
v___x_3379_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_2817_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3390_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3382_ = v___x_3379_;
v_isShared_3383_ = v_isSharedCheck_3390_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_3379_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3390_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3388_; 
v___x_3384_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__28, &l_Lean_Meta_Grind_NormSym_simpForall___closed__28_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__28);
v___x_3385_ = l_Lean_Expr_app___override(v___x_3384_, v___x_3371_);
v___x_3386_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3386_, 0, v_a_3380_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
lean_ctor_set_uint8(v___x_3386_, sizeof(void*)*2, v___x_3138_);
lean_ctor_set_uint8(v___x_3386_, sizeof(void*)*2 + 1, v___x_3316_);
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 0, v___x_3386_);
v___x_3388_ = v___x_3382_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3386_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
lean_dec_ref(v___x_3371_);
v_a_3391_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3379_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3379_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
}
else
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_dec_ref(v___x_3371_);
lean_dec_ref_known(v_e_2813_, 3);
v_a_3399_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3376_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3376_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_dec_ref(v___x_3371_);
lean_dec_ref_known(v_e_2813_, 3);
v_a_3407_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3372_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3372_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec_ref_known(v_e_2813_, 3);
v_a_3415_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3317_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3317_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
v___jp_2900_:
{
if (v___y_2910_ == 0)
{
v___y_2825_ = v___y_2909_;
v___y_2826_ = v___y_2906_;
v___y_2827_ = v___y_2908_;
v___y_2828_ = v___y_2904_;
v___y_2829_ = v___y_2901_;
v___y_2830_ = v___y_2907_;
v___y_2831_ = v___y_2903_;
v___y_2832_ = v___y_2902_;
v___y_2833_ = v___y_2905_;
goto v___jp_2824_;
}
else
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = l_Lean_Expr_appFn_x21(v_body_2898_);
v___x_2912_ = l_Lean_Expr_appFn_x21(v___x_2911_);
if (lean_obj_tag(v___x_2912_) == 4)
{
lean_object* v_declName_2913_; lean_object* v___x_2914_; uint8_t v___x_2915_; 
v_declName_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_declName_2913_);
lean_dec_ref_known(v___x_2912_, 2);
v___x_2914_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1));
v___x_2915_ = lean_name_eq(v_declName_2913_, v___x_2914_);
lean_dec(v_declName_2913_);
if (v___x_2915_ == 0)
{
lean_dec_ref(v___x_2911_);
v___y_2825_ = v___y_2909_;
v___y_2826_ = v___y_2906_;
v___y_2827_ = v___y_2908_;
v___y_2828_ = v___y_2904_;
v___y_2829_ = v___y_2901_;
v___y_2830_ = v___y_2907_;
v___y_2831_ = v___y_2903_;
v___y_2832_ = v___y_2902_;
v___y_2833_ = v___y_2905_;
goto v___jp_2824_;
}
else
{
lean_object* v_pRaw_2916_; lean_object* v_pRaw_2917_; lean_object* v___x_2918_; 
v_pRaw_2916_ = l_Lean_Expr_appArg_x21(v___x_2911_);
lean_dec_ref(v___x_2911_);
v_pRaw_2917_ = l_Lean_Expr_appArg_x21(v_body_2898_);
v___x_2918_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(v_pRaw_2916_);
if (lean_obj_tag(v___x_2918_) == 1)
{
lean_object* v_val_2919_; lean_object* v_snd_2920_; lean_object* v_fst_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_3019_; 
lean_inc_ref(v_binderType_2897_);
lean_inc(v_binderName_2896_);
lean_dec_ref(v_pRaw_2916_);
lean_dec_ref_known(v_e_2813_, 3);
v_val_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_val_2919_);
lean_dec_ref_known(v___x_2918_, 1);
v_snd_2920_ = lean_ctor_get(v_val_2919_, 1);
v_fst_2921_ = lean_ctor_get(v_val_2919_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v_val_2919_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_2923_ = v_val_2919_;
v_isShared_2924_ = v_isSharedCheck_3019_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_snd_2920_);
lean_inc(v_fst_2921_);
lean_dec(v_val_2919_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_3019_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v_fst_2925_; lean_object* v_snd_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_3018_; 
v_fst_2925_ = lean_ctor_get(v_snd_2920_, 0);
v_snd_2926_ = lean_ctor_get(v_snd_2920_, 1);
v_isSharedCheck_3018_ = !lean_is_exclusive(v_snd_2920_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_2928_ = v_snd_2920_;
v_isShared_2929_ = v_isSharedCheck_3018_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_snd_2926_);
lean_inc(v_fst_2925_);
lean_dec(v_snd_2920_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_3018_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___f_2930_; lean_object* v_p_2931_; uint8_t v___x_2932_; lean_object* v___x_2933_; lean_object* v_q_2934_; lean_object* v_00_u03b2_2935_; lean_object* v___x_2936_; 
lean_inc_n(v_fst_2925_, 3);
v___f_2930_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_NormSym_simpForall___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2930_, 0, v_fst_2925_);
lean_inc_ref(v_pRaw_2917_);
lean_inc_ref_n(v_binderType_2897_, 4);
lean_inc_n(v_binderName_2896_, 3);
v_p_2931_ = l_Lean_mkLambda(v_binderName_2896_, v_binderInfo_2899_, v_binderType_2897_, v_pRaw_2917_);
v___x_2932_ = 0;
lean_inc(v_snd_2926_);
lean_inc(v_fst_2921_);
v___x_2933_ = l_Lean_mkLambda(v_fst_2921_, v___x_2932_, v_fst_2925_, v_snd_2926_);
v_q_2934_ = l_Lean_mkLambda(v_binderName_2896_, v_binderInfo_2899_, v_binderType_2897_, v___x_2933_);
v_00_u03b2_2935_ = l_Lean_mkLambda(v_binderName_2896_, v_binderInfo_2899_, v_binderType_2897_, v_fst_2925_);
v___x_2936_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2897_, v___y_2901_, v___y_2907_, v___y_2903_, v___y_2902_, v___y_2905_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2938_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_a_2937_);
lean_dec_ref_known(v___x_2936_, 1);
lean_inc_ref(v_binderType_2897_);
lean_inc(v_binderName_2896_);
v___x_2938_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_binderName_2896_, v_binderType_2897_, v___f_2930_, v___y_2909_, v___y_2906_, v___y_2908_, v___y_2904_, v___y_2901_, v___y_2907_, v___y_2903_, v___y_2902_, v___y_2905_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref_known(v___x_2938_, 1);
v___x_2940_ = lean_unsigned_to_nat(0u);
v___x_2941_ = lean_unsigned_to_nat(1u);
v___x_2942_ = lean_expr_lift_loose_bvars(v_pRaw_2917_, v___x_2940_, v___x_2941_);
lean_dec_ref(v_pRaw_2917_);
v___x_2943_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2942_, v___y_2904_, v___y_2901_, v___y_2907_, v___y_2903_, v___y_2902_, v___y_2905_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v___x_2945_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref_known(v___x_2943_, 1);
v___x_2945_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_snd_2926_, v_a_2944_, v___y_2904_, v___y_2901_, v___y_2907_, v___y_2903_, v___y_2902_, v___y_2905_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2947_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref_known(v___x_2945_, 1);
v___x_2947_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_fst_2921_, v___x_2932_, v_fst_2925_, v_a_2946_, v___y_2904_, v___y_2901_, v___y_2907_, v___y_2903_, v___y_2902_, v___y_2905_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v___x_2949_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec_ref_known(v___x_2947_, 1);
lean_inc_ref(v_binderType_2897_);
v___x_2949_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_binderName_2896_, v_binderInfo_2899_, v_binderType_2897_, v_a_2948_, v___y_2904_, v___y_2901_, v___y_2907_, v___y_2903_, v___y_2902_, v___y_2905_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2969_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2952_ = v___x_2949_;
v_isShared_2953_ = v_isSharedCheck_2969_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2949_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2969_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2957_; 
v___x_2954_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__1));
v___x_2955_ = lean_box(0);
if (v_isShared_2929_ == 0)
{
lean_ctor_set_tag(v___x_2928_, 1);
lean_ctor_set(v___x_2928_, 1, v___x_2955_);
lean_ctor_set(v___x_2928_, 0, v_a_2939_);
v___x_2957_ = v___x_2928_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2939_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v___x_2955_);
v___x_2957_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
lean_object* v___x_2959_; 
if (v_isShared_2924_ == 0)
{
lean_ctor_set_tag(v___x_2923_, 1);
lean_ctor_set(v___x_2923_, 1, v___x_2957_);
lean_ctor_set(v___x_2923_, 0, v_a_2937_);
v___x_2959_ = v___x_2923_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2937_);
lean_ctor_set(v_reuseFailAlloc_2967_, 1, v___x_2957_);
v___x_2959_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2965_; 
v___x_2960_ = l_Lean_mkConst(v___x_2954_, v___x_2959_);
v___x_2961_ = l_Lean_mkApp4(v___x_2960_, v_binderType_2897_, v_00_u03b2_2935_, v_p_2931_, v_q_2934_);
v___x_2962_ = 0;
v___x_2963_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2963_, 0, v_a_2950_);
lean_ctor_set(v___x_2963_, 1, v___x_2961_);
lean_ctor_set_uint8(v___x_2963_, sizeof(void*)*2, v___x_2962_);
lean_ctor_set_uint8(v___x_2963_, sizeof(void*)*2 + 1, v___x_2962_);
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 0, v___x_2963_);
v___x_2965_ = v___x_2952_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2963_);
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
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_dec(v_a_2939_);
lean_dec(v_a_2937_);
lean_dec_ref(v_00_u03b2_2935_);
lean_dec_ref(v_q_2934_);
lean_dec_ref(v_p_2931_);
lean_del_object(v___x_2928_);
lean_del_object(v___x_2923_);
lean_dec_ref(v_binderType_2897_);
v_a_2970_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2949_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2949_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
lean_dec(v_a_2939_);
lean_dec(v_a_2937_);
lean_dec_ref(v_00_u03b2_2935_);
lean_dec_ref(v_q_2934_);
lean_dec_ref(v_p_2931_);
lean_del_object(v___x_2928_);
lean_del_object(v___x_2923_);
lean_dec_ref(v_binderType_2897_);
lean_dec(v_binderName_2896_);
v_a_2978_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2947_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2947_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
else
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
lean_dec(v_a_2939_);
lean_dec(v_a_2937_);
lean_dec_ref(v_00_u03b2_2935_);
lean_dec_ref(v_q_2934_);
lean_dec_ref(v_p_2931_);
lean_del_object(v___x_2928_);
lean_dec(v_fst_2925_);
lean_del_object(v___x_2923_);
lean_dec(v_fst_2921_);
lean_dec_ref(v_binderType_2897_);
lean_dec(v_binderName_2896_);
v_a_2986_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___x_2945_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2945_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2986_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
else
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
lean_dec(v_a_2939_);
lean_dec(v_a_2937_);
lean_dec_ref(v_00_u03b2_2935_);
lean_dec_ref(v_q_2934_);
lean_dec_ref(v_p_2931_);
lean_del_object(v___x_2928_);
lean_dec(v_snd_2926_);
lean_dec(v_fst_2925_);
lean_del_object(v___x_2923_);
lean_dec(v_fst_2921_);
lean_dec_ref(v_binderType_2897_);
lean_dec(v_binderName_2896_);
v_a_2994_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2943_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2943_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
lean_dec(v_a_2937_);
lean_dec_ref(v_00_u03b2_2935_);
lean_dec_ref(v_q_2934_);
lean_dec_ref(v_p_2931_);
lean_del_object(v___x_2928_);
lean_dec(v_snd_2926_);
lean_dec(v_fst_2925_);
lean_del_object(v___x_2923_);
lean_dec(v_fst_2921_);
lean_dec_ref(v_pRaw_2917_);
lean_dec_ref(v_binderType_2897_);
lean_dec(v_binderName_2896_);
v_a_3002_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_2938_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_2938_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
else
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3017_; 
lean_dec_ref(v_00_u03b2_2935_);
lean_dec_ref(v_q_2934_);
lean_dec_ref(v_p_2931_);
lean_dec_ref(v___f_2930_);
lean_del_object(v___x_2928_);
lean_dec(v_snd_2926_);
lean_dec(v_fst_2925_);
lean_del_object(v___x_2923_);
lean_dec(v_fst_2921_);
lean_dec_ref(v_pRaw_2917_);
lean_dec_ref(v_binderType_2897_);
lean_dec(v_binderName_2896_);
v_a_3010_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_3017_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3012_ = v___x_2936_;
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_2936_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3017_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
if (v_isShared_3013_ == 0)
{
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
}
}
else
{
lean_object* v___x_3020_; 
lean_dec(v___x_2918_);
v___x_3020_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(v_pRaw_2917_);
lean_dec_ref(v_pRaw_2917_);
if (lean_obj_tag(v___x_3020_) == 1)
{
lean_object* v_val_3021_; lean_object* v_snd_3022_; lean_object* v_fst_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3121_; 
lean_inc_ref(v_binderType_2897_);
lean_inc(v_binderName_2896_);
lean_dec_ref_known(v_e_2813_, 3);
v_val_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_val_3021_);
lean_dec_ref_known(v___x_3020_, 1);
v_snd_3022_ = lean_ctor_get(v_val_3021_, 1);
v_fst_3023_ = lean_ctor_get(v_val_3021_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v_val_3021_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3025_ = v_val_3021_;
v_isShared_3026_ = v_isSharedCheck_3121_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_snd_3022_);
lean_inc(v_fst_3023_);
lean_dec(v_val_3021_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3121_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v_fst_3027_; lean_object* v_snd_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3120_; 
v_fst_3027_ = lean_ctor_get(v_snd_3022_, 0);
v_snd_3028_ = lean_ctor_get(v_snd_3022_, 1);
v_isSharedCheck_3120_ = !lean_is_exclusive(v_snd_3022_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3030_ = v_snd_3022_;
v_isShared_3031_ = v_isSharedCheck_3120_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_snd_3028_);
lean_inc(v_fst_3027_);
lean_dec(v_snd_3022_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3120_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___f_3032_; lean_object* v_p_3033_; uint8_t v___x_3034_; lean_object* v___x_3035_; lean_object* v_q_3036_; lean_object* v_00_u03b2_3037_; lean_object* v___x_3038_; 
lean_inc_n(v_fst_3027_, 3);
v___f_3032_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_NormSym_simpForall___lam__0___boxed), 12, 1);
lean_closure_set(v___f_3032_, 0, v_fst_3027_);
lean_inc_ref(v_pRaw_2916_);
lean_inc_ref_n(v_binderType_2897_, 4);
lean_inc_n(v_binderName_2896_, 3);
v_p_3033_ = l_Lean_mkLambda(v_binderName_2896_, v_binderInfo_2899_, v_binderType_2897_, v_pRaw_2916_);
v___x_3034_ = 0;
lean_inc(v_snd_3028_);
lean_inc(v_fst_3023_);
v___x_3035_ = l_Lean_mkLambda(v_fst_3023_, v___x_3034_, v_fst_3027_, v_snd_3028_);
v_q_3036_ = l_Lean_mkLambda(v_binderName_2896_, v_binderInfo_2899_, v_binderType_2897_, v___x_3035_);
v_00_u03b2_3037_ = l_Lean_mkLambda(v_binderName_2896_, v_binderInfo_2899_, v_binderType_2897_, v_fst_3027_);
v___x_3038_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2897_, v___y_2901_, v___y_2907_, v___y_2903_, v___y_2902_, v___y_2905_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3040_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3039_);
lean_dec_ref_known(v___x_3038_, 1);
lean_inc_ref(v_binderType_2897_);
lean_inc(v_binderName_2896_);
v___x_3040_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_binderName_2896_, v_binderType_2897_, v___f_3032_, v___y_2909_, v___y_2906_, v___y_2908_, v___y_2904_, v___y_2901_, v___y_2907_, v___y_2903_, v___y_2902_, v___y_2905_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_a_3041_);
lean_dec_ref_known(v___x_3040_, 1);
v___x_3042_ = lean_unsigned_to_nat(0u);
v___x_3043_ = lean_unsigned_to_nat(1u);
v___x_3044_ = lean_expr_lift_loose_bvars(v_pRaw_2916_, v___x_3042_, v___x_3043_);
lean_dec_ref(v_pRaw_2916_);
v___x_3045_ = l_Lean_Meta_Sym_shareCommonInc(v___x_3044_, v___y_2904_, v___y_2901_, v___y_2907_, v___y_2903_, v___y_2902_, v___y_2905_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; lean_object* v___x_3047_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_a_3046_);
lean_dec_ref_known(v___x_3045_, 1);
v___x_3047_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_a_3046_, v_snd_3028_, v___y_2904_, v___y_2901_, v___y_2907_, v___y_2903_, v___y_2902_, v___y_2905_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3049_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref_known(v___x_3047_, 1);
v___x_3049_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_fst_3023_, v___x_3034_, v_fst_3027_, v_a_3048_, v___y_2904_, v___y_2901_, v___y_2907_, v___y_2903_, v___y_2902_, v___y_2905_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v___x_3051_; 
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
lean_inc(v_a_3050_);
lean_dec_ref_known(v___x_3049_, 1);
lean_inc_ref(v_binderType_2897_);
v___x_3051_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_binderName_2896_, v_binderInfo_2899_, v_binderType_2897_, v_a_3050_, v___y_2904_, v___y_2901_, v___y_2907_, v___y_2903_, v___y_2902_, v___y_2905_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3071_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3054_ = v___x_3051_;
v_isShared_3055_ = v_isSharedCheck_3071_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_3051_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3071_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3059_; 
v___x_3056_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__3));
v___x_3057_ = lean_box(0);
if (v_isShared_3031_ == 0)
{
lean_ctor_set_tag(v___x_3030_, 1);
lean_ctor_set(v___x_3030_, 1, v___x_3057_);
lean_ctor_set(v___x_3030_, 0, v_a_3041_);
v___x_3059_ = v___x_3030_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3041_);
lean_ctor_set(v_reuseFailAlloc_3070_, 1, v___x_3057_);
v___x_3059_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
lean_object* v___x_3061_; 
if (v_isShared_3026_ == 0)
{
lean_ctor_set_tag(v___x_3025_, 1);
lean_ctor_set(v___x_3025_, 1, v___x_3059_);
lean_ctor_set(v___x_3025_, 0, v_a_3039_);
v___x_3061_ = v___x_3025_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3039_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v___x_3059_);
v___x_3061_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; uint8_t v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3067_; 
v___x_3062_ = l_Lean_mkConst(v___x_3056_, v___x_3061_);
v___x_3063_ = l_Lean_mkApp4(v___x_3062_, v_binderType_2897_, v_00_u03b2_3037_, v_p_3033_, v_q_3036_);
v___x_3064_ = 0;
v___x_3065_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3065_, 0, v_a_3052_);
lean_ctor_set(v___x_3065_, 1, v___x_3063_);
lean_ctor_set_uint8(v___x_3065_, sizeof(void*)*2, v___x_3064_);
lean_ctor_set_uint8(v___x_3065_, sizeof(void*)*2 + 1, v___x_3064_);
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 0, v___x_3065_);
v___x_3067_ = v___x_3054_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3065_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
}
else
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
lean_dec(v_a_3041_);
lean_dec(v_a_3039_);
lean_dec_ref(v_00_u03b2_3037_);
lean_dec_ref(v_q_3036_);
lean_dec_ref(v_p_3033_);
lean_del_object(v___x_3030_);
lean_del_object(v___x_3025_);
lean_dec_ref(v_binderType_2897_);
v_a_3072_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_3051_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3051_);
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
lean_dec(v_a_3041_);
lean_dec(v_a_3039_);
lean_dec_ref(v_00_u03b2_3037_);
lean_dec_ref(v_q_3036_);
lean_dec_ref(v_p_3033_);
lean_del_object(v___x_3030_);
lean_del_object(v___x_3025_);
lean_dec_ref(v_binderType_2897_);
lean_dec(v_binderName_2896_);
v_a_3080_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3049_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3049_);
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
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
lean_dec(v_a_3041_);
lean_dec(v_a_3039_);
lean_dec_ref(v_00_u03b2_3037_);
lean_dec_ref(v_q_3036_);
lean_dec_ref(v_p_3033_);
lean_del_object(v___x_3030_);
lean_dec(v_fst_3027_);
lean_del_object(v___x_3025_);
lean_dec(v_fst_3023_);
lean_dec_ref(v_binderType_2897_);
lean_dec(v_binderName_2896_);
v_a_3088_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3047_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3047_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec(v_a_3041_);
lean_dec(v_a_3039_);
lean_dec_ref(v_00_u03b2_3037_);
lean_dec_ref(v_q_3036_);
lean_dec_ref(v_p_3033_);
lean_del_object(v___x_3030_);
lean_dec(v_snd_3028_);
lean_dec(v_fst_3027_);
lean_del_object(v___x_3025_);
lean_dec(v_fst_3023_);
lean_dec_ref(v_binderType_2897_);
lean_dec(v_binderName_2896_);
v_a_3096_ = lean_ctor_get(v___x_3045_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3045_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3045_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3045_);
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
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec(v_a_3039_);
lean_dec_ref(v_00_u03b2_3037_);
lean_dec_ref(v_q_3036_);
lean_dec_ref(v_p_3033_);
lean_del_object(v___x_3030_);
lean_dec(v_snd_3028_);
lean_dec(v_fst_3027_);
lean_del_object(v___x_3025_);
lean_dec(v_fst_3023_);
lean_dec_ref(v_pRaw_2916_);
lean_dec_ref(v_binderType_2897_);
lean_dec(v_binderName_2896_);
v_a_3104_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3040_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3040_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_dec_ref(v_00_u03b2_3037_);
lean_dec_ref(v_q_3036_);
lean_dec_ref(v_p_3033_);
lean_dec_ref(v___f_3032_);
lean_del_object(v___x_3030_);
lean_dec(v_snd_3028_);
lean_dec(v_fst_3027_);
lean_del_object(v___x_3025_);
lean_dec(v_fst_3023_);
lean_dec_ref(v_pRaw_2916_);
lean_dec_ref(v_binderType_2897_);
lean_dec(v_binderName_2896_);
v_a_3112_ = lean_ctor_get(v___x_3038_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3038_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3038_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3038_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
}
}
else
{
lean_dec(v___x_3020_);
lean_dec_ref(v_pRaw_2916_);
v___y_2825_ = v___y_2909_;
v___y_2826_ = v___y_2906_;
v___y_2827_ = v___y_2908_;
v___y_2828_ = v___y_2904_;
v___y_2829_ = v___y_2901_;
v___y_2830_ = v___y_2907_;
v___y_2831_ = v___y_2903_;
v___y_2832_ = v___y_2902_;
v___y_2833_ = v___y_2905_;
goto v___jp_2824_;
}
}
}
}
else
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
lean_dec_ref(v___x_2912_);
lean_dec_ref(v___x_2911_);
lean_dec_ref_known(v_e_2813_, 3);
v___x_3122_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3122_);
return v___x_3123_;
}
}
}
v___jp_3124_:
{
uint8_t v___x_3134_; 
v___x_3134_ = l_Lean_Expr_isApp(v_body_2898_);
if (v___x_3134_ == 0)
{
v___y_2901_ = v___y_3129_;
v___y_2902_ = v___y_3132_;
v___y_2903_ = v___y_3131_;
v___y_2904_ = v___y_3128_;
v___y_2905_ = v___y_3133_;
v___y_2906_ = v___y_3126_;
v___y_2907_ = v___y_3130_;
v___y_2908_ = v___y_3127_;
v___y_2909_ = v___y_3125_;
v___y_2910_ = v___x_3134_;
goto v___jp_2900_;
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; uint8_t v___x_3137_; 
v___x_3135_ = l_Lean_Expr_getAppNumArgs(v_body_2898_);
v___x_3136_ = lean_unsigned_to_nat(2u);
v___x_3137_ = lean_nat_dec_eq(v___x_3135_, v___x_3136_);
lean_dec(v___x_3135_);
v___y_2901_ = v___y_3129_;
v___y_2902_ = v___y_3132_;
v___y_2903_ = v___y_3131_;
v___y_2904_ = v___y_3128_;
v___y_2905_ = v___y_3133_;
v___y_2906_ = v___y_3126_;
v___y_2907_ = v___y_3130_;
v___y_2908_ = v___y_3127_;
v___y_2909_ = v___y_3125_;
v___y_2910_ = v___x_3137_;
goto v___jp_2900_;
}
}
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
lean_dec_ref(v_e_2813_);
v___x_3423_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_3424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3423_);
return v___x_3424_;
}
v___jp_2824_:
{
lean_object* v___x_2834_; 
v___x_2834_ = l_Lean_Meta_Grind_forallImpAnd_x3f(v_e_2813_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2887_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2837_ = v___x_2834_;
v_isShared_2838_ = v_isSharedCheck_2887_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2834_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2887_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
if (lean_obj_tag(v_a_2835_) == 1)
{
lean_object* v_val_2839_; lean_object* v_snd_2840_; lean_object* v_fst_2841_; lean_object* v_fst_2842_; lean_object* v_snd_2843_; lean_object* v___x_2844_; 
lean_del_object(v___x_2837_);
v_val_2839_ = lean_ctor_get(v_a_2835_, 0);
lean_inc(v_val_2839_);
lean_dec_ref_known(v_a_2835_, 1);
v_snd_2840_ = lean_ctor_get(v_val_2839_, 1);
lean_inc(v_snd_2840_);
v_fst_2841_ = lean_ctor_get(v_val_2839_, 0);
lean_inc(v_fst_2841_);
lean_dec(v_val_2839_);
v_fst_2842_ = lean_ctor_get(v_snd_2840_, 0);
lean_inc(v_fst_2842_);
v_snd_2843_ = lean_ctor_get(v_snd_2840_, 1);
lean_inc(v_snd_2843_);
lean_dec(v_snd_2840_);
v___x_2844_ = l_Lean_Meta_Sym_shareCommonInc(v_fst_2841_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2846_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2844_, 1);
v___x_2846_ = l_Lean_Meta_Sym_shareCommonInc(v_fst_2842_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2848_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v___x_2848_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v_a_2845_, v_a_2847_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2858_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2851_ = v___x_2848_;
v_isShared_2852_ = v_isSharedCheck_2858_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2848_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2858_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
uint8_t v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2856_; 
v___x_2853_ = 0;
v___x_2854_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2854_, 0, v_a_2849_);
lean_ctor_set(v___x_2854_, 1, v_snd_2843_);
lean_ctor_set_uint8(v___x_2854_, sizeof(void*)*2, v___x_2853_);
lean_ctor_set_uint8(v___x_2854_, sizeof(void*)*2 + 1, v___x_2853_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 0, v___x_2854_);
v___x_2856_ = v___x_2851_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2854_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
lean_dec(v_snd_2843_);
v_a_2859_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v___x_2848_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2848_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2859_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
lean_dec(v_a_2845_);
lean_dec(v_snd_2843_);
v_a_2867_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2846_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2846_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_dec(v_snd_2843_);
lean_dec(v_fst_2842_);
v_a_2875_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2844_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2844_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
else
{
lean_object* v___x_2883_; lean_object* v___x_2885_; 
lean_dec(v_a_2835_);
v___x_2883_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 0, v___x_2883_);
v___x_2885_ = v___x_2837_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2883_);
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
v_a_2888_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2834_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2834_);
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
}
LEAN_EXPORT void l_Lean_Meta_Grind_NormSym_simpForall_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2813_ = stack[0].m_obj;
lean_object* v_a_2814_ = stack[1].m_obj;
lean_object* v_a_2815_ = stack[2].m_obj;
lean_object* v_a_2816_ = stack[3].m_obj;
lean_object* v_a_2817_ = stack[4].m_obj;
lean_object* v_a_2818_ = stack[5].m_obj;
lean_object* v_a_2819_ = stack[6].m_obj;
lean_object* v_a_2820_ = stack[7].m_obj;
lean_object* v_a_2821_ = stack[8].m_obj;
lean_object* v_a_2822_ = stack[9].m_obj;
lean_object* v_res_3425_;
v_res_3425_ = l_Lean_Meta_Grind_NormSym_simpForall(v_e_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
stack->m_obj
 = v_res_3425_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpForall___boxed(lean_object* v_e_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_Meta_Grind_NormSym_simpForall(v_e_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_);
lean_dec(v_a_3435_);
lean_dec_ref(v_a_3434_);
lean_dec(v_a_3433_);
lean_dec_ref(v_a_3432_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec_ref(v_a_3428_);
lean_dec(v_a_3427_);
return v_res_3437_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpExists___closed__6(void){
_start:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3451_ = lean_box(0);
v___x_3452_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___closed__5));
v___x_3453_ = l_Lean_mkConst(v___x_3452_, v___x_3451_);
return v___x_3453_;
}
}
lean_object* l_Lean_Meta_Grind_NormSym_simpExists(lean_object* v_e_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_){
_start:
{
lean_object* v___x_3486_; uint8_t v___x_3487_; 
v___x_3486_ = l_Lean_Expr_cleanupAnnotations(v_e_3469_);
v___x_3487_ = l_Lean_Expr_isApp(v___x_3486_);
if (v___x_3487_ == 0)
{
lean_dec_ref(v___x_3486_);
goto v___jp_3483_;
}
else
{
lean_object* v_arg_3488_; lean_object* v___x_3489_; uint8_t v___x_3490_; 
v_arg_3488_ = lean_ctor_get(v___x_3486_, 1);
lean_inc_ref(v_arg_3488_);
v___x_3489_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3486_);
v___x_3490_ = l_Lean_Expr_isApp(v___x_3489_);
if (v___x_3490_ == 0)
{
lean_dec_ref(v___x_3489_);
lean_dec_ref(v_arg_3488_);
goto v___jp_3483_;
}
else
{
lean_object* v_arg_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; 
v_arg_3491_ = lean_ctor_get(v___x_3489_, 1);
lean_inc_ref(v_arg_3491_);
v___x_3492_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3489_);
v___x_3493_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkExistsS___redArg___closed__1));
v___x_3494_ = l_Lean_Expr_isConstOf(v___x_3492_, v___x_3493_);
if (v___x_3494_ == 0)
{
lean_dec_ref(v___x_3492_);
lean_dec_ref(v_arg_3491_);
lean_dec_ref(v_arg_3488_);
goto v___jp_3483_;
}
else
{
if (lean_obj_tag(v_arg_3488_) == 6)
{
lean_object* v_binderName_3495_; lean_object* v_body_3496_; lean_object* v_u_3497_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; uint8_t v___y_3586_; lean_object* v___y_3587_; uint8_t v___y_3588_; lean_object* v___y_3589_; uint8_t v___y_3590_; uint8_t v___y_3677_; uint8_t v___x_3755_; 
v_binderName_3495_ = lean_ctor_get(v_arg_3488_, 0);
lean_inc(v_binderName_3495_);
v_body_3496_ = lean_ctor_get(v_arg_3488_, 2);
lean_inc_ref(v_body_3496_);
lean_dec_ref_known(v_arg_3488_, 3);
v_u_3497_ = l_Lean_Expr_constLevels_x21(v___x_3492_);
v___x_3755_ = l_Lean_Expr_isApp(v_body_3496_);
if (v___x_3755_ == 0)
{
v___y_3677_ = v___x_3755_;
goto v___jp_3676_;
}
else
{
lean_object* v___x_3756_; lean_object* v___x_3757_; uint8_t v___x_3758_; 
v___x_3756_ = l_Lean_Expr_getAppNumArgs(v_body_3496_);
v___x_3757_ = lean_unsigned_to_nat(2u);
v___x_3758_ = lean_nat_dec_eq(v___x_3756_, v___x_3757_);
lean_dec(v___x_3756_);
v___y_3677_ = v___x_3758_;
goto v___jp_3676_;
}
v___jp_3498_:
{
uint8_t v___x_3508_; 
v___x_3508_ = l_Lean_Expr_hasLooseBVars(v_body_3496_);
if (v___x_3508_ == 0)
{
lean_object* v___x_3509_; 
lean_inc_ref(v_arg_3491_);
v___x_3509_ = l_Lean_Meta_isProp(v_arg_3491_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; uint8_t v___x_3511_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_a_3510_);
lean_dec_ref_known(v___x_3509_, 1);
v___x_3511_ = lean_unbox(v_a_3510_);
if (v___x_3511_ == 0)
{
lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3512_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___closed__1));
lean_inc(v_u_3497_);
v___x_3513_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__0___redArg(v___x_3512_, v_u_3497_, v___y_3503_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___x_3513_, 1);
lean_inc_ref(v_arg_3491_);
v___x_3515_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkNotS_spec__1___redArg(v_a_3514_, v_arg_3491_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3517_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3515_, 1);
v___x_3517_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_3516_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3532_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3520_ = v___x_3517_;
v_isShared_3521_ = v_isSharedCheck_3532_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3517_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3532_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
if (lean_obj_tag(v_a_3518_) == 1)
{
lean_object* v_val_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; uint8_t v___x_3527_; uint8_t v___x_3528_; lean_object* v___x_3530_; 
v_val_3522_ = lean_ctor_get(v_a_3518_, 0);
lean_inc(v_val_3522_);
lean_dec_ref_known(v_a_3518_, 1);
v___x_3523_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___closed__3));
v___x_3524_ = l_Lean_mkConst(v___x_3523_, v_u_3497_);
lean_inc_ref(v_body_3496_);
v___x_3525_ = l_Lean_mkApp3(v___x_3524_, v_arg_3491_, v_val_3522_, v_body_3496_);
v___x_3526_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3526_, 0, v_body_3496_);
lean_ctor_set(v___x_3526_, 1, v___x_3525_);
v___x_3527_ = lean_unbox(v_a_3510_);
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*2, v___x_3527_);
v___x_3528_ = lean_unbox(v_a_3510_);
lean_dec(v_a_3510_);
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*2 + 1, v___x_3528_);
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 0, v___x_3526_);
v___x_3530_ = v___x_3520_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3526_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
else
{
lean_del_object(v___x_3520_);
lean_dec(v_a_3518_);
lean_dec(v_a_3510_);
lean_dec(v_u_3497_);
lean_dec_ref(v_body_3496_);
lean_dec_ref(v_arg_3491_);
goto v___jp_3480_;
}
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_dec(v_a_3510_);
lean_dec(v_u_3497_);
lean_dec_ref(v_body_3496_);
lean_dec_ref(v_arg_3491_);
v_a_3533_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3517_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3517_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
lean_dec(v_a_3510_);
lean_dec(v_u_3497_);
lean_dec_ref(v_body_3496_);
lean_dec_ref(v_arg_3491_);
v_a_3541_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3515_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3515_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
lean_dec(v_a_3510_);
lean_dec(v_u_3497_);
lean_dec_ref(v_body_3496_);
lean_dec_ref(v_arg_3491_);
v_a_3549_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_3513_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3513_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
if (v_isShared_3552_ == 0)
{
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3549_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
else
{
lean_object* v___x_3557_; 
lean_dec(v_a_3510_);
lean_dec(v_u_3497_);
lean_inc_ref(v_body_3496_);
lean_inc_ref(v_arg_3491_);
v___x_3557_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v_arg_3491_, v_body_3496_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3568_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3560_ = v___x_3557_;
v_isShared_3561_ = v_isSharedCheck_3568_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3557_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3568_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3566_; 
v___x_3562_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpExists___closed__6, &l_Lean_Meta_Grind_NormSym_simpExists___closed__6_once, _init_l_Lean_Meta_Grind_NormSym_simpExists___closed__6);
v___x_3563_ = l_Lean_mkAppB(v___x_3562_, v_arg_3491_, v_body_3496_);
v___x_3564_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3564_, 0, v_a_3558_);
lean_ctor_set(v___x_3564_, 1, v___x_3563_);
lean_ctor_set_uint8(v___x_3564_, sizeof(void*)*2, v___x_3508_);
lean_ctor_set_uint8(v___x_3564_, sizeof(void*)*2 + 1, v___x_3508_);
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 0, v___x_3564_);
v___x_3566_ = v___x_3560_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3564_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec_ref(v_body_3496_);
lean_dec_ref(v_arg_3491_);
v_a_3569_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3557_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3557_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec(v_u_3497_);
lean_dec_ref(v_body_3496_);
lean_dec_ref(v_arg_3491_);
v_a_3577_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3509_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3509_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
else
{
lean_dec(v_u_3497_);
lean_dec_ref(v_body_3496_);
lean_dec_ref(v_arg_3491_);
goto v___jp_3480_;
}
}
v___jp_3585_:
{
if (v___y_3590_ == 0)
{
uint8_t v___x_3591_; 
v___x_3591_ = l_Lean_Expr_hasLooseBVars(v___y_3587_);
if (v___x_3591_ == 0)
{
if (v___y_3586_ == 0)
{
lean_dec_ref(v___y_3589_);
lean_dec_ref(v___y_3587_);
lean_dec(v_binderName_3495_);
lean_dec_ref(v___x_3492_);
v___y_3499_ = v_a_3470_;
v___y_3500_ = v_a_3471_;
v___y_3501_ = v_a_3472_;
v___y_3502_ = v_a_3473_;
v___y_3503_ = v_a_3474_;
v___y_3504_ = v_a_3475_;
v___y_3505_ = v_a_3476_;
v___y_3506_ = v_a_3477_;
v___y_3507_ = v_a_3478_;
goto v___jp_3498_;
}
else
{
uint8_t v___x_3592_; lean_object* v___x_3593_; 
lean_dec_ref(v_body_3496_);
v___x_3592_ = 0;
lean_inc_ref(v_arg_3491_);
v___x_3593_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_binderName_3495_, v___x_3592_, v_arg_3491_, v___y_3589_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_a_3594_; lean_object* v___x_3595_; 
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc_n(v_a_3594_, 2);
lean_dec_ref_known(v___x_3593_, 1);
lean_inc_ref(v_arg_3491_);
v___x_3595_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v___x_3492_, v_arg_3491_, v_a_3594_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_a_3596_; lean_object* v___x_3597_; 
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_a_3596_);
lean_dec_ref_known(v___x_3595_, 1);
lean_inc_ref(v___y_3587_);
v___x_3597_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v_a_3596_, v___y_3587_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3609_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3600_ = v___x_3597_;
v_isShared_3601_ = v_isSharedCheck_3609_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3597_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3609_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3607_; 
v___x_3602_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___closed__8));
v___x_3603_ = l_Lean_mkConst(v___x_3602_, v_u_3497_);
v___x_3604_ = l_Lean_mkApp3(v___x_3603_, v_arg_3491_, v_a_3594_, v___y_3587_);
v___x_3605_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3605_, 0, v_a_3598_);
lean_ctor_set(v___x_3605_, 1, v___x_3604_);
lean_ctor_set_uint8(v___x_3605_, sizeof(void*)*2, v___y_3590_);
lean_ctor_set_uint8(v___x_3605_, sizeof(void*)*2 + 1, v___y_3590_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v___x_3605_);
v___x_3607_ = v___x_3600_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___x_3605_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
lean_dec(v_a_3594_);
lean_dec_ref(v___y_3587_);
lean_dec(v_u_3497_);
lean_dec_ref(v_arg_3491_);
v_a_3610_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3597_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3597_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_dec(v_a_3594_);
lean_dec_ref(v___y_3587_);
lean_dec(v_u_3497_);
lean_dec_ref(v_arg_3491_);
v_a_3618_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3595_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3595_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
else
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3633_; 
lean_dec_ref(v___y_3587_);
lean_dec(v_u_3497_);
lean_dec_ref(v___x_3492_);
lean_dec_ref(v_arg_3491_);
v_a_3626_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3628_ = v___x_3593_;
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3593_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3631_; 
if (v_isShared_3629_ == 0)
{
v___x_3631_ = v___x_3628_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3626_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3589_);
lean_dec_ref(v___y_3587_);
lean_dec(v_binderName_3495_);
lean_dec_ref(v___x_3492_);
v___y_3499_ = v_a_3470_;
v___y_3500_ = v_a_3471_;
v___y_3501_ = v_a_3472_;
v___y_3502_ = v_a_3473_;
v___y_3503_ = v_a_3474_;
v___y_3504_ = v_a_3475_;
v___y_3505_ = v_a_3476_;
v___y_3506_ = v_a_3477_;
v___y_3507_ = v_a_3478_;
goto v___jp_3498_;
}
}
else
{
uint8_t v___x_3634_; lean_object* v___x_3635_; 
lean_dec_ref(v_body_3496_);
v___x_3634_ = 0;
lean_inc_ref(v_arg_3491_);
v___x_3635_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_binderName_3495_, v___x_3634_, v_arg_3491_, v___y_3587_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_object* v_a_3636_; lean_object* v___x_3637_; 
v_a_3636_ = lean_ctor_get(v___x_3635_, 0);
lean_inc_n(v_a_3636_, 2);
lean_dec_ref_known(v___x_3635_, 1);
lean_inc_ref(v_arg_3491_);
v___x_3637_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v___x_3492_, v_arg_3491_, v_a_3636_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; lean_object* v___x_3639_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
lean_dec_ref_known(v___x_3637_, 1);
lean_inc_ref(v___y_3589_);
v___x_3639_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS(v___y_3589_, v_a_3638_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3651_; 
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3642_ = v___x_3639_;
v_isShared_3643_ = v_isSharedCheck_3651_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3639_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3651_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3649_; 
v___x_3644_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___closed__10));
v___x_3645_ = l_Lean_mkConst(v___x_3644_, v_u_3497_);
v___x_3646_ = l_Lean_mkApp3(v___x_3645_, v_arg_3491_, v_a_3636_, v___y_3589_);
v___x_3647_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3647_, 0, v_a_3640_);
lean_ctor_set(v___x_3647_, 1, v___x_3646_);
lean_ctor_set_uint8(v___x_3647_, sizeof(void*)*2, v___y_3588_);
lean_ctor_set_uint8(v___x_3647_, sizeof(void*)*2 + 1, v___y_3588_);
if (v_isShared_3643_ == 0)
{
lean_ctor_set(v___x_3642_, 0, v___x_3647_);
v___x_3649_ = v___x_3642_;
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
lean_dec(v_a_3636_);
lean_dec_ref(v___y_3589_);
lean_dec(v_u_3497_);
lean_dec_ref(v_arg_3491_);
v_a_3652_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3654_ = v___x_3639_;
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v___x_3639_);
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
lean_dec(v_a_3636_);
lean_dec_ref(v___y_3589_);
lean_dec(v_u_3497_);
lean_dec_ref(v_arg_3491_);
v_a_3660_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3637_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3637_);
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
lean_dec_ref(v___y_3589_);
lean_dec(v_u_3497_);
lean_dec_ref(v___x_3492_);
lean_dec_ref(v_arg_3491_);
v_a_3668_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3635_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3635_);
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
}
v___jp_3676_:
{
if (v___y_3677_ == 0)
{
lean_dec(v_binderName_3495_);
lean_dec_ref(v___x_3492_);
v___y_3499_ = v_a_3470_;
v___y_3500_ = v_a_3471_;
v___y_3501_ = v_a_3472_;
v___y_3502_ = v_a_3473_;
v___y_3503_ = v_a_3474_;
v___y_3504_ = v_a_3475_;
v___y_3505_ = v_a_3476_;
v___y_3506_ = v_a_3477_;
v___y_3507_ = v_a_3478_;
goto v___jp_3498_;
}
else
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3678_ = l_Lean_Expr_appFn_x21(v_body_3496_);
v___x_3679_ = l_Lean_Expr_appFn_x21(v___x_3678_);
if (lean_obj_tag(v___x_3679_) == 4)
{
lean_object* v_declName_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; 
v_declName_3680_ = lean_ctor_get(v___x_3679_, 0);
lean_inc(v_declName_3680_);
lean_dec_ref_known(v___x_3679_, 2);
v___x_3681_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg___closed__1));
v___x_3682_ = lean_name_eq(v_declName_3680_, v___x_3681_);
if (v___x_3682_ == 0)
{
lean_object* v___x_3683_; uint8_t v___x_3684_; 
v___x_3683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS___closed__1));
v___x_3684_ = lean_name_eq(v_declName_3680_, v___x_3683_);
lean_dec(v_declName_3680_);
if (v___x_3684_ == 0)
{
lean_dec_ref(v___x_3678_);
lean_dec(v_binderName_3495_);
lean_dec_ref(v___x_3492_);
v___y_3499_ = v_a_3470_;
v___y_3500_ = v_a_3471_;
v___y_3501_ = v_a_3472_;
v___y_3502_ = v_a_3473_;
v___y_3503_ = v_a_3474_;
v___y_3504_ = v_a_3475_;
v___y_3505_ = v_a_3476_;
v___y_3506_ = v_a_3477_;
v___y_3507_ = v_a_3478_;
goto v___jp_3498_;
}
else
{
lean_object* v_b_3685_; lean_object* v_b_3686_; uint8_t v___x_3687_; 
v_b_3685_ = l_Lean_Expr_appArg_x21(v___x_3678_);
lean_dec_ref(v___x_3678_);
v_b_3686_ = l_Lean_Expr_appArg_x21(v_body_3496_);
v___x_3687_ = l_Lean_Expr_hasLooseBVars(v_b_3685_);
if (v___x_3687_ == 0)
{
v___y_3586_ = v___x_3684_;
v___y_3587_ = v_b_3686_;
v___y_3588_ = v___x_3682_;
v___y_3589_ = v_b_3685_;
v___y_3590_ = v___x_3684_;
goto v___jp_3585_;
}
else
{
v___y_3586_ = v___x_3684_;
v___y_3587_ = v_b_3686_;
v___y_3588_ = v___x_3682_;
v___y_3589_ = v_b_3685_;
v___y_3590_ = v___x_3682_;
goto v___jp_3585_;
}
}
}
else
{
lean_object* v_pRaw_3688_; lean_object* v_qRaw_3689_; uint8_t v___x_3690_; lean_object* v___x_3691_; 
lean_dec(v_declName_3680_);
v_pRaw_3688_ = l_Lean_Expr_appArg_x21(v___x_3678_);
lean_dec_ref(v___x_3678_);
v_qRaw_3689_ = l_Lean_Expr_appArg_x21(v_body_3496_);
lean_dec_ref(v_body_3496_);
v___x_3690_ = 0;
lean_inc_ref(v_arg_3491_);
lean_inc(v_binderName_3495_);
v___x_3691_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_binderName_3495_, v___x_3690_, v_arg_3491_, v_pRaw_3688_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v_a_3692_; lean_object* v___x_3693_; 
v_a_3692_ = lean_ctor_get(v___x_3691_, 0);
lean_inc(v_a_3692_);
lean_dec_ref_known(v___x_3691_, 1);
lean_inc_ref(v_arg_3491_);
v___x_3693_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_binderName_3495_, v___x_3690_, v_arg_3491_, v_qRaw_3689_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; lean_object* v___x_3695_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
lean_dec_ref_known(v___x_3693_, 1);
lean_inc(v_a_3692_);
lean_inc_ref(v_arg_3491_);
lean_inc_ref(v___x_3492_);
v___x_3695_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v___x_3492_, v_arg_3491_, v_a_3692_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v___x_3697_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3696_);
lean_dec_ref_known(v___x_3695_, 1);
lean_inc(v_a_3694_);
lean_inc_ref(v_arg_3491_);
v___x_3697_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkAndS_spec__0___redArg(v___x_3492_, v_arg_3491_, v_a_3694_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v_a_3698_; lean_object* v___x_3699_; 
v_a_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc(v_a_3698_);
lean_dec_ref_known(v___x_3697_, 1);
v___x_3699_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_mkOrS___redArg(v_a_3696_, v_a_3698_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3712_; 
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3702_ = v___x_3699_;
v_isShared_3703_ = v_isSharedCheck_3712_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3699_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3712_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; uint8_t v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3710_; 
v___x_3704_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___closed__12));
v___x_3705_ = l_Lean_mkConst(v___x_3704_, v_u_3497_);
v___x_3706_ = l_Lean_mkApp3(v___x_3705_, v_arg_3491_, v_a_3692_, v_a_3694_);
v___x_3707_ = 0;
v___x_3708_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3708_, 0, v_a_3700_);
lean_ctor_set(v___x_3708_, 1, v___x_3706_);
lean_ctor_set_uint8(v___x_3708_, sizeof(void*)*2, v___x_3707_);
lean_ctor_set_uint8(v___x_3708_, sizeof(void*)*2 + 1, v___x_3707_);
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 0, v___x_3708_);
v___x_3710_ = v___x_3702_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3708_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
else
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3720_; 
lean_dec(v_a_3694_);
lean_dec(v_a_3692_);
lean_dec(v_u_3497_);
lean_dec_ref(v_arg_3491_);
v_a_3713_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3715_ = v___x_3699_;
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3699_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3718_; 
if (v_isShared_3716_ == 0)
{
v___x_3718_ = v___x_3715_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_a_3713_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
lean_dec(v_a_3696_);
lean_dec(v_a_3694_);
lean_dec(v_a_3692_);
lean_dec(v_u_3497_);
lean_dec_ref(v_arg_3491_);
v_a_3721_ = lean_ctor_get(v___x_3697_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___x_3697_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3697_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3726_; 
if (v_isShared_3724_ == 0)
{
v___x_3726_ = v___x_3723_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
else
{
lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3736_; 
lean_dec(v_a_3694_);
lean_dec(v_a_3692_);
lean_dec(v_u_3497_);
lean_dec_ref(v___x_3492_);
lean_dec_ref(v_arg_3491_);
v_a_3729_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3731_ = v___x_3695_;
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v___x_3695_);
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
else
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
lean_dec(v_a_3692_);
lean_dec(v_u_3497_);
lean_dec_ref(v___x_3492_);
lean_dec_ref(v_arg_3491_);
v_a_3737_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v___x_3693_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3693_);
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
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
lean_dec_ref(v_qRaw_3689_);
lean_dec(v_u_3497_);
lean_dec(v_binderName_3495_);
lean_dec_ref(v___x_3492_);
lean_dec_ref(v_arg_3491_);
v_a_3745_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3691_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3691_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
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
}
else
{
lean_object* v___x_3753_; lean_object* v___x_3754_; 
lean_dec_ref(v___x_3679_);
lean_dec_ref(v___x_3678_);
lean_dec(v_u_3497_);
lean_dec_ref(v_body_3496_);
lean_dec(v_binderName_3495_);
lean_dec_ref(v___x_3492_);
lean_dec_ref(v_arg_3491_);
v___x_3753_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3753_);
return v___x_3754_;
}
}
}
}
else
{
lean_object* v___x_3759_; lean_object* v___x_3760_; 
lean_dec_ref(v___x_3492_);
lean_dec_ref(v_arg_3491_);
lean_dec_ref(v_arg_3488_);
v___x_3759_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
return v___x_3760_;
}
}
}
}
v___jp_3480_:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; 
v___x_3481_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3482_, 0, v___x_3481_);
return v___x_3482_;
}
v___jp_3483_:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3484_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
return v___x_3485_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_NormSym_simpExists_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3469_ = stack[0].m_obj;
lean_object* v_a_3470_ = stack[1].m_obj;
lean_object* v_a_3471_ = stack[2].m_obj;
lean_object* v_a_3472_ = stack[3].m_obj;
lean_object* v_a_3473_ = stack[4].m_obj;
lean_object* v_a_3474_ = stack[5].m_obj;
lean_object* v_a_3475_ = stack[6].m_obj;
lean_object* v_a_3476_ = stack[7].m_obj;
lean_object* v_a_3477_ = stack[8].m_obj;
lean_object* v_a_3478_ = stack[9].m_obj;
lean_object* v_res_3761_;
v_res_3761_ = l_Lean_Meta_Grind_NormSym_simpExists(v_e_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
stack->m_obj
 = v_res_3761_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists___boxed(lean_object* v_e_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_){
_start:
{
lean_object* v_res_3773_; 
v_res_3773_ = l_Lean_Meta_Grind_NormSym_simpExists(v_e_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_);
lean_dec(v_a_3771_);
lean_dec_ref(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_a_3764_);
lean_dec(v_a_3763_);
return v_res_3773_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Result(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
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
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_AlphaShareBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
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
res = initialize_Lean_Meta_Match_MatcherInfo(builtin);
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

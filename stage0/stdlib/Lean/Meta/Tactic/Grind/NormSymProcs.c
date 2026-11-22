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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkAndS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_mkOrS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevRangeS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getFalseExpr___redArg(lean_object*);
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
lean_object* l_Lean_Meta_Sym_mkNotS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_mkExistsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Meta_Sym_getBoolFalseExpr___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_getBoolTrueExpr___redArg(lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Sym_betaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_etaReduce(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_reduceArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_reduceArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_hasEtaReducibleArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_hasEtaReducibleArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_NormSym_etaReduce___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Exists"};
static const lean_object* l_Lean_Meta_Grind_NormSym_etaReduce___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_etaReduce___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_etaReduce___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_etaReduce___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 29, 48, 135, 199, 176, 149, 70)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_etaReduce___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_etaReduce___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_etaReduce___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Subtype"};
static const lean_object* l_Lean_Meta_Grind_NormSym_etaReduce___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_etaReduce___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_etaReduce___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_etaReduce___closed__2_value),LEAN_SCALAR_PTR_LITERAL(30, 108, 3, 75, 185, 102, 103, 84)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_etaReduce___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_etaReduce___closed__3_value;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "not_implies"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__4_value),LEAN_SCALAR_PTR_LITERAL(142, 189, 44, 77, 86, 197, 178, 67)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_pushNot___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__6;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__7_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__9_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Or"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__11_value),LEAN_SCALAR_PTR_LITERAL(34, 237, 162, 225, 217, 98, 205, 196)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__12_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__13_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__14_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "not_ite"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__16_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__15_value),LEAN_SCALAR_PTR_LITERAL(132, 165, 120, 219, 71, 87, 242, 138)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_pushNot___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__17;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "not_eq_true"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__18_value),LEAN_SCALAR_PTR_LITERAL(225, 244, 63, 40, 164, 6, 8, 162)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_pushNot___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__20;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "not_eq_false"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__21_value),LEAN_SCALAR_PTR_LITERAL(83, 226, 87, 91, 103, 177, 77, 30)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_pushNot___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__23;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "not_eq_prop"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__25_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__24_value),LEAN_SCALAR_PTR_LITERAL(93, 9, 240, 16, 38, 110, 5, 203)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__25_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_pushNot___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__26;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "not_and"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__27_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__28_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__28_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__27_value),LEAN_SCALAR_PTR_LITERAL(239, 225, 24, 71, 205, 142, 249, 26)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__28_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_pushNot___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__29;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "not_or"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__30 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__30_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__31_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__31_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__30_value),LEAN_SCALAR_PTR_LITERAL(235, 74, 178, 162, 31, 3, 143, 38)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__31 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__31_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_pushNot___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__32;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__33 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__33_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__33_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__34_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "not_exists"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__35_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__36_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__36_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__35_value),LEAN_SCALAR_PTR_LITERAL(122, 84, 103, 56, 9, 28, 88, 199)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__36 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__36_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "not_not"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__37 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__37_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__38_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__38_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__38_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__37_value),LEAN_SCALAR_PTR_LITERAL(37, 13, 167, 116, 75, 172, 227, 19)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__38 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__38_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_pushNot___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__39;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "not_true"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__40 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__40_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__41_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__41_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__40_value),LEAN_SCALAR_PTR_LITERAL(189, 233, 184, 33, 201, 88, 141, 182)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__41 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__41_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_pushNot___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__42;
static const lean_string_object l_Lean_Meta_Grind_NormSym_pushNot___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_false"};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__43 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__43_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__44_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_pushNot___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__44_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__43_value),LEAN_SCALAR_PTR_LITERAL(32, 161, 26, 17, 134, 82, 22, 22)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__44 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__44_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_pushNot___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_pushNot___closed__45;
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrNot_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrNot_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrNot_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrNot_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpForall___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_pushNot___closed__9_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
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
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Nonempty"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 191, 110, 220, 210, 100, 152, 183)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "exists_const"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 209, 190, 134, 241, 243, 173, 71)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "exists_prop"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(210, 14, 159, 153, 168, 50, 182, 0)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__6;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "exists_and_left"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(211, 136, 99, 9, 218, 202, 25, 69)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "exists_and_right"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(70, 93, 78, 251, 76, 254, 187, 237)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "exists_or"};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__12_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(161, 112, 226, 203, 229, 162, 152, 185)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___redArg(lean_object* v_e_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_){
_start:
{
if (lean_obj_tag(v_e_3_) == 10)
{
lean_object* v_expr_11_; lean_object* v___x_12_; 
v_expr_11_ = lean_ctor_get(v_e_3_, 1);
lean_inc_ref_n(v_expr_11_, 2);
lean_dec_ref_known(v_e_3_, 2);
v___x_12_ = l_Lean_Meta_Sym_mkEqRefl(v_expr_11_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v_a_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_22_; 
v_a_13_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_22_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_22_ == 0)
{
v___x_15_ = v___x_12_;
v_isShared_16_ = v_isSharedCheck_22_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_a_13_);
lean_dec(v___x_12_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_22_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
uint8_t v___x_17_; lean_object* v___x_18_; lean_object* v___x_20_; 
v___x_17_ = 0;
v___x_18_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_18_, 0, v_expr_11_);
lean_ctor_set(v___x_18_, 1, v_a_13_);
lean_ctor_set_uint8(v___x_18_, sizeof(void*)*2, v___x_17_);
lean_ctor_set_uint8(v___x_18_, sizeof(void*)*2 + 1, v___x_17_);
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
else
{
lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_30_; 
lean_dec_ref(v_expr_11_);
v_a_23_ = lean_ctor_get(v___x_12_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_30_ == 0)
{
v___x_25_ = v___x_12_;
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_dec(v___x_12_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_28_; 
if (v_isShared_26_ == 0)
{
v___x_28_ = v___x_25_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_a_23_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
}
else
{
lean_object* v___x_31_; lean_object* v___x_32_; 
lean_dec_ref(v_e_3_);
v___x_31_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___redArg___boxed(lean_object* v_e_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v_e_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_);
lean_dec(v_a_39_);
lean_dec_ref(v_a_38_);
lean_dec(v_a_37_);
lean_dec_ref(v_a_36_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData(lean_object* v_e_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_Meta_Grind_NormSym_eraseMData___redArg(v_e_42_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___boxed(lean_object* v_e_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Meta_Grind_NormSym_eraseMData(v_e_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_);
lean_dec(v_a_63_);
lean_dec_ref(v_a_62_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
lean_dec(v_a_59_);
lean_dec_ref(v_a_58_);
lean_dec(v_a_57_);
lean_dec_ref(v_a_56_);
lean_dec(v_a_55_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_reduceArg(lean_object* v_a_66_){
_start:
{
lean_object* v_a_x27_67_; uint8_t v___x_68_; 
v_a_x27_67_ = l_Lean_Meta_Sym_etaReduce(v_a_66_);
v___x_68_ = l_Lean_Expr_isConst(v_a_x27_67_);
if (v___x_68_ == 0)
{
uint8_t v___x_69_; 
v___x_69_ = l_Lean_Expr_isFVar(v_a_x27_67_);
if (v___x_69_ == 0)
{
lean_dec_ref(v_a_x27_67_);
lean_inc_ref(v_a_66_);
return v_a_66_;
}
else
{
return v_a_x27_67_;
}
}
else
{
return v_a_x27_67_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_reduceArg___boxed(lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_reduceArg(v_a_70_);
lean_dec_ref(v_a_70_);
return v_res_71_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_hasEtaReducibleArg(lean_object* v_a_72_){
_start:
{
if (lean_obj_tag(v_a_72_) == 5)
{
lean_object* v_fn_73_; lean_object* v_arg_74_; lean_object* v___x_75_; size_t v___x_76_; size_t v___x_77_; uint8_t v___x_78_; 
v_fn_73_ = lean_ctor_get(v_a_72_, 0);
v_arg_74_ = lean_ctor_get(v_a_72_, 1);
v___x_75_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_reduceArg(v_arg_74_);
v___x_76_ = lean_ptr_addr(v_arg_74_);
v___x_77_ = lean_ptr_addr(v___x_75_);
lean_dec_ref(v___x_75_);
v___x_78_ = lean_usize_dec_eq(v___x_76_, v___x_77_);
if (v___x_78_ == 0)
{
uint8_t v___x_79_; 
v___x_79_ = 1;
return v___x_79_;
}
else
{
v_a_72_ = v_fn_73_;
goto _start;
}
}
else
{
uint8_t v___x_81_; 
v___x_81_ = 0;
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_hasEtaReducibleArg___boxed(lean_object* v_a_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_hasEtaReducibleArg(v_a_82_);
lean_dec_ref(v_a_82_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(lean_object* v_f_85_, lean_object* v_a_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v___y_95_; lean_object* v___x_98_; uint8_t v_debug_99_; 
v___x_98_ = lean_st_ref_get(v___y_88_);
v_debug_99_ = lean_ctor_get_uint8(v___x_98_, sizeof(void*)*13);
lean_dec(v___x_98_);
if (v_debug_99_ == 0)
{
v___y_95_ = v___y_88_;
goto v___jp_94_;
}
else
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_85_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v___x_101_; 
lean_dec_ref_known(v___x_100_, 1);
v___x_101_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_dec_ref_known(v___x_101_, 1);
v___y_95_ = v___y_88_;
goto v___jp_94_;
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
lean_dec_ref(v_a_86_);
lean_dec_ref(v_f_85_);
v_a_102_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_101_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_101_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
lean_dec_ref(v_a_86_);
lean_dec_ref(v_f_85_);
v_a_110_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_100_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_100_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
v___jp_94_:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = l_Lean_Expr_app___override(v_f_85_, v_a_86_);
v___x_97_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_96_, v___y_95_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg___boxed(lean_object* v_f_118_, lean_object* v_a_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(v_f_118_, v_a_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0(lean_object* v_f_128_, lean_object* v_a_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(v_f_128_, v_a_129_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___boxed(lean_object* v_f_141_, lean_object* v_a_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0(v_f_141_, v_a_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go(lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
if (lean_obj_tag(v_a_154_) == 5)
{
lean_object* v_fn_165_; lean_object* v_arg_166_; lean_object* v___x_167_; 
v_fn_165_ = lean_ctor_get(v_a_154_, 0);
lean_inc_ref(v_fn_165_);
v_arg_166_ = lean_ctor_get(v_a_154_, 1);
lean_inc_ref(v_arg_166_);
lean_dec_ref_known(v_a_154_, 2);
v___x_167_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go(v_fn_165_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_a_168_);
lean_dec_ref_known(v___x_167_, 1);
v___x_169_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_reduceArg(v_arg_166_);
lean_dec_ref(v_arg_166_);
v___x_170_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(v_a_168_, v___x_169_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
return v___x_170_;
}
else
{
lean_dec_ref(v_arg_166_);
return v___x_167_;
}
}
else
{
lean_object* v___x_171_; 
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v_a_154_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go___boxed(lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go(v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec(v_a_173_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_etaReduce(lean_object* v_e_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___y_202_; lean_object* v___y_203_; lean_object* v___y_204_; lean_object* v___y_205_; lean_object* v___y_206_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_210_; uint8_t v___x_246_; 
v___x_246_ = l_Lean_Expr_isApp(v_e_190_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec_ref(v_e_190_);
v___x_247_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_247_, 0, v___x_246_);
lean_ctor_set_uint8(v___x_247_, 1, v___x_246_);
v___x_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
return v___x_248_;
}
else
{
lean_object* v___x_249_; 
v___x_249_ = l_Lean_Expr_getAppFn(v_e_190_);
if (lean_obj_tag(v___x_249_) == 4)
{
lean_object* v_declName_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v_declName_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_declName_250_);
lean_dec_ref_known(v___x_249_, 2);
v___x_251_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_etaReduce___closed__1));
v___x_252_ = lean_name_eq(v_declName_250_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_253_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_etaReduce___closed__3));
v___x_254_ = lean_name_eq(v_declName_250_, v___x_253_);
lean_dec(v_declName_250_);
if (v___x_254_ == 0)
{
v___y_202_ = v_a_191_;
v___y_203_ = v_a_192_;
v___y_204_ = v_a_193_;
v___y_205_ = v_a_194_;
v___y_206_ = v_a_195_;
v___y_207_ = v_a_196_;
v___y_208_ = v_a_197_;
v___y_209_ = v_a_198_;
v___y_210_ = v_a_199_;
goto v___jp_201_;
}
else
{
lean_dec_ref(v_e_190_);
goto v___jp_243_;
}
}
else
{
lean_dec(v_declName_250_);
lean_dec_ref(v_e_190_);
goto v___jp_243_;
}
}
else
{
lean_dec_ref(v___x_249_);
v___y_202_ = v_a_191_;
v___y_203_ = v_a_192_;
v___y_204_ = v_a_193_;
v___y_205_ = v_a_194_;
v___y_206_ = v_a_195_;
v___y_207_ = v_a_196_;
v___y_208_ = v_a_197_;
v___y_209_ = v_a_198_;
v___y_210_ = v_a_199_;
goto v___jp_201_;
}
}
v___jp_201_:
{
uint8_t v___x_211_; 
v___x_211_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_hasEtaReducibleArg(v_e_190_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec_ref(v_e_190_);
v___x_212_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_212_, 0, v___x_211_);
lean_ctor_set_uint8(v___x_212_, 1, v___x_211_);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
else
{
lean_object* v___x_214_; 
v___x_214_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go(v_e_190_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; lean_object* v___x_216_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc_n(v_a_215_, 2);
lean_dec_ref_known(v___x_214_, 1);
v___x_216_ = l_Lean_Meta_Sym_mkEqRefl(v_a_215_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_226_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_226_ == 0)
{
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_226_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_226_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
uint8_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_221_ = 0;
v___x_222_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_222_, 0, v_a_215_);
lean_ctor_set(v___x_222_, 1, v_a_217_);
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*2, v___x_221_);
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*2 + 1, v___x_221_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_222_);
v___x_224_ = v___x_219_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
lean_dec(v_a_215_);
v_a_227_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_216_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_216_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
else
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
v_a_235_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_214_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_214_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
v___jp_243_:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
return v___x_245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_etaReduce___boxed(lean_object* v_e_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Meta_Grind_NormSym_etaReduce(v_e_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(lean_object* v_e_274_){
_start:
{
lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_279_ = l_Lean_Expr_cleanupAnnotations(v_e_274_);
v___x_280_ = l_Lean_Expr_isApp(v___x_279_);
if (v___x_280_ == 0)
{
lean_dec_ref(v___x_279_);
goto v___jp_276_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_281_ = l_Lean_Expr_appFnCleanup___redArg(v___x_279_);
lean_dec_ref(v___x_279_);
v___x_282_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__3));
v___x_283_ = l_Lean_Expr_isConstOf(v___x_281_, v___x_282_);
lean_dec_ref(v___x_281_);
if (v___x_283_ == 0)
{
goto v___jp_276_;
}
else
{
uint8_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = 0;
v___x_285_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_283_, v___x_284_);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
return v___x_286_;
}
}
v___jp_276_:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___boxed(lean_object* v_e_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(v_e_287_);
lean_dec_ref(v_e_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond(lean_object* v_e_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(v_e_290_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___boxed(lean_object* v_e_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Meta_Grind_NormSym_preMatchCond(v_e_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_e_302_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(lean_object* v_declName_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; lean_object* v_env_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_317_ = lean_st_ref_get(v___y_315_);
v_env_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc_ref(v_env_318_);
lean_dec(v___x_317_);
v___x_319_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_318_, v_declName_314_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg___boxed(lean_object* v_declName_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(v_declName_321_, v___y_322_);
lean_dec(v___y_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0(lean_object* v_declName_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(v_declName_325_, v___y_334_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___boxed(lean_object* v_declName_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0(v_declName_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
lean_dec(v___y_346_);
lean_dec_ref(v___y_345_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(lean_object* v_e_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
if (lean_obj_tag(v_e_354_) == 5)
{
lean_object* v_fn_368_; lean_object* v_arg_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v_fn_368_ = lean_ctor_get(v_e_354_, 0);
lean_inc_ref(v_fn_368_);
v_arg_369_ = lean_ctor_get(v_e_354_, 1);
lean_inc_ref(v_arg_369_);
v___x_370_ = l_Lean_Expr_cleanupAnnotations(v_e_354_);
v___x_371_ = l_Lean_Expr_isApp(v___x_370_);
if (v___x_371_ == 0)
{
lean_dec_ref(v___x_370_);
lean_dec_ref(v_arg_369_);
lean_dec_ref_known(v_e_354_, 2);
lean_dec_ref(v_fn_368_);
goto v___jp_365_;
}
else
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = l_Lean_Expr_appFnCleanup___redArg(v___x_370_);
lean_dec_ref(v___x_370_);
v___x_373_ = l_Lean_Expr_isApp(v___x_372_);
if (v___x_373_ == 0)
{
lean_dec_ref(v___x_372_);
lean_dec_ref(v_arg_369_);
lean_dec_ref_known(v_e_354_, 2);
lean_dec_ref(v_fn_368_);
goto v___jp_365_;
}
else
{
lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_374_ = l_Lean_Expr_appFnCleanup___redArg(v___x_372_);
lean_dec_ref(v___x_372_);
v___x_375_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___closed__1));
v___x_376_ = l_Lean_Expr_isConstOf(v___x_374_, v___x_375_);
lean_dec_ref(v___x_374_);
if (v___x_376_ == 0)
{
lean_dec_ref(v_arg_369_);
lean_dec_ref_known(v_e_354_, 2);
lean_dec_ref(v_fn_368_);
goto v___jp_365_;
}
else
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_Expr_getAppFn(v_arg_369_);
if (lean_obj_tag(v___x_377_) == 4)
{
lean_object* v_declName_378_; lean_object* v___x_379_; lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_421_; 
v_declName_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_declName_378_);
lean_dec_ref_known(v___x_377_, 2);
v___x_379_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(v_declName_378_, v_a_363_);
v_a_380_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_421_ == 0)
{
v___x_382_ = v___x_379_;
v_isShared_383_ = v_isSharedCheck_421_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_421_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
if (lean_obj_tag(v_a_380_) == 1)
{
lean_object* v_val_384_; lean_object* v_numParams_385_; lean_object* v_numDiscrs_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
lean_del_object(v___x_382_);
v_val_384_ = lean_ctor_get(v_a_380_, 0);
lean_inc(v_val_384_);
lean_dec_ref_known(v_a_380_, 1);
v_numParams_385_ = lean_ctor_get(v_val_384_, 0);
lean_inc(v_numParams_385_);
v_numDiscrs_386_ = lean_ctor_get(v_val_384_, 1);
lean_inc(v_numDiscrs_386_);
lean_dec(v_val_384_);
v___x_387_ = lean_unsigned_to_nat(1u);
v___x_388_ = lean_nat_add(v_numParams_385_, v___x_387_);
lean_dec(v_numParams_385_);
v___x_389_ = lean_nat_add(v___x_388_, v_numDiscrs_386_);
lean_dec(v_numDiscrs_386_);
lean_inc_ref(v_arg_369_);
v___x_390_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_arg_369_, v___x_388_, v___x_389_, v_a_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
lean_dec(v___x_389_);
lean_dec(v___x_388_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v___x_392_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
lean_dec_ref_known(v___x_390_, 1);
v___x_392_ = l_Lean_Meta_Sym_Simp_mkCongrArg___redArg(v_e_354_, v_fn_368_, v_arg_369_, v_a_391_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_415_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_392_);
if (v_isSharedCheck_415_ == 0)
{
v___x_395_ = v___x_392_;
v_isShared_396_ = v_isSharedCheck_415_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_415_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
if (lean_obj_tag(v_a_393_) == 0)
{
uint8_t v_contextDependent_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v_contextDependent_397_ = lean_ctor_get_uint8(v_a_393_, 1);
lean_dec_ref_known(v_a_393_, 0);
v___x_398_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_376_, v_contextDependent_397_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_398_);
v___x_400_ = v___x_395_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
else
{
lean_object* v_e_x27_402_; lean_object* v_proof_403_; uint8_t v_contextDependent_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_414_; 
v_e_x27_402_ = lean_ctor_get(v_a_393_, 0);
v_proof_403_ = lean_ctor_get(v_a_393_, 1);
v_contextDependent_404_ = lean_ctor_get_uint8(v_a_393_, sizeof(void*)*2 + 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v_a_393_);
if (v_isSharedCheck_414_ == 0)
{
v___x_406_ = v_a_393_;
v_isShared_407_ = v_isSharedCheck_414_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_proof_403_);
lean_inc(v_e_x27_402_);
lean_dec(v_a_393_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_414_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_e_x27_402_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_proof_403_);
lean_ctor_set_uint8(v_reuseFailAlloc_413_, sizeof(void*)*2 + 1, v_contextDependent_404_);
v___x_409_ = v_reuseFailAlloc_413_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_411_; 
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*2, v___x_376_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_409_);
v___x_411_ = v___x_395_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
}
}
else
{
return v___x_392_;
}
}
else
{
lean_dec_ref(v_arg_369_);
lean_dec_ref_known(v_e_354_, 2);
lean_dec_ref(v_fn_368_);
return v___x_390_;
}
}
else
{
uint8_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_419_; 
lean_dec(v_a_380_);
lean_dec_ref(v_arg_369_);
lean_dec_ref_known(v_e_354_, 2);
lean_dec_ref(v_fn_368_);
v___x_416_ = 0;
v___x_417_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_376_, v___x_416_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_417_);
v___x_419_ = v___x_382_;
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
}
}
else
{
uint8_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec_ref(v___x_377_);
lean_dec_ref(v_arg_369_);
lean_dec_ref_known(v_e_354_, 2);
lean_dec_ref(v_fn_368_);
v___x_422_ = 0;
v___x_423_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_376_, v___x_422_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
}
}
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec_ref(v_e_354_);
v___x_425_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
v___jp_365_:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
return v___x_367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___boxed(lean_object* v_e_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(v_e_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
return v_res_438_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(lean_object* v_declName_462_){
_start:
{
lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_463_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__2));
v___x_464_ = lean_name_eq(v_declName_462_, v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; uint8_t v___x_466_; 
v___x_465_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__4));
v___x_466_ = lean_name_eq(v_declName_462_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_467_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__6));
v___x_468_ = lean_name_eq(v_declName_462_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_469_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__9));
v___x_470_ = lean_name_eq(v_declName_462_, v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_471_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__12));
v___x_472_ = lean_name_eq(v_declName_462_, v___x_471_);
return v___x_472_;
}
else
{
return v___x_470_;
}
}
else
{
return v___x_468_;
}
}
else
{
return v___x_466_;
}
}
else
{
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___boxed(lean_object* v_declName_473_){
_start:
{
uint8_t v_res_474_; lean_object* v_r_475_; 
v_res_474_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(v_declName_473_);
lean_dec(v_declName_473_);
v_r_475_ = lean_box(v_res_474_);
return v_r_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(lean_object* v_u_476_, lean_object* v___y_477_){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = l_Lean_Expr_sort___override(v_u_476_);
v___x_480_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_479_, v___y_477_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg___boxed(lean_object* v_u_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v_u_481_, v___y_482_);
lean_dec(v___y_482_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1(lean_object* v_u_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v_u_485_, v___y_490_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___boxed(lean_object* v_u_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1(v_u_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___y_498_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___redArg(lean_object* v_f_509_, lean_object* v_a_u2081_510_, lean_object* v_a_u2082_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(v_f_509_, v_a_u2081_510_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_521_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(v_a_520_, v_a_u2082_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
return v___x_521_;
}
else
{
lean_dec_ref(v_a_u2082_511_);
return v___x_519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___redArg___boxed(lean_object* v_f_522_, lean_object* v_a_u2081_523_, lean_object* v_a_u2082_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___redArg(v_f_522_, v_a_u2081_523_, v_a_u2082_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(lean_object* v_f_533_, lean_object* v_a_u2081_534_, lean_object* v_a_u2082_535_, lean_object* v_a_u2083_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___redArg(v_f_533_, v_a_u2081_534_, v_a_u2082_535_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_549_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v___x_547_, 1);
v___x_549_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(v_a_548_, v_a_u2083_536_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
return v___x_549_;
}
else
{
lean_dec_ref(v_a_u2083_536_);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___boxed(lean_object* v_f_550_, lean_object* v_a_u2081_551_, lean_object* v_a_u2082_552_, lean_object* v_a_u2083_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v_f_550_, v_a_u2081_551_, v_a_u2082_552_, v_a_u2083_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
return v_res_564_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__5(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = lean_box(0);
v___x_576_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__4));
v___x_577_ = l_Lean_mkConst(v___x_576_, v___x_575_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__8(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_583_ = lean_box(0);
v___x_584_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__7));
v___x_585_ = l_Lean_mkConst(v___x_584_, v___x_583_);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__17(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_602_ = lean_box(0);
v___x_603_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__16));
v___x_604_ = l_Lean_mkConst(v___x_603_, v___x_602_);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__20(void){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_610_ = lean_box(0);
v___x_611_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__19));
v___x_612_ = l_Lean_mkConst(v___x_611_, v___x_610_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpEq(lean_object* v_e_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = l_Lean_Expr_cleanupAnnotations(v_e_613_);
v___x_628_ = l_Lean_Expr_isApp(v___x_627_);
if (v___x_628_ == 0)
{
lean_dec_ref(v___x_627_);
goto v___jp_624_;
}
else
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = l_Lean_Expr_appFnCleanup___redArg(v___x_627_);
v___x_630_ = l_Lean_Expr_isApp(v___x_629_);
if (v___x_630_ == 0)
{
lean_dec_ref(v___x_629_);
lean_dec_ref(v___x_627_);
goto v___jp_624_;
}
else
{
lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_631_ = l_Lean_Expr_appFnCleanup___redArg(v___x_629_);
v___x_632_ = l_Lean_Expr_isApp(v___x_631_);
if (v___x_632_ == 0)
{
lean_dec_ref(v___x_631_);
lean_dec_ref(v___x_629_);
lean_dec_ref(v___x_627_);
goto v___jp_624_;
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_633_ = l_Lean_Expr_appFnCleanup___redArg(v___x_631_);
v___x_634_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__1));
v___x_635_ = l_Lean_Expr_isConstOf(v___x_633_, v___x_634_);
if (v___x_635_ == 0)
{
lean_dec_ref(v___x_633_);
lean_dec_ref(v___x_631_);
lean_dec_ref(v___x_629_);
lean_dec_ref(v___x_627_);
goto v___jp_624_;
}
else
{
lean_object* v_arg_636_; lean_object* v_arg_637_; lean_object* v_arg_638_; lean_object* v___x_639_; 
v_arg_636_ = lean_ctor_get(v___x_627_, 1);
lean_inc_ref(v_arg_636_);
lean_dec_ref(v___x_627_);
v_arg_637_ = lean_ctor_get(v___x_629_, 1);
lean_inc_ref(v_arg_637_);
lean_dec_ref(v___x_629_);
v_arg_638_ = lean_ctor_get(v___x_631_, 1);
lean_inc_ref_n(v_arg_638_, 2);
lean_dec_ref(v___x_631_);
v___x_639_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_638_, v_a_620_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_806_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_806_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_806_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_806_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_649_ = l_Lean_Expr_cleanupAnnotations(v_a_640_);
lean_dec(v_a_640_);
v___x_650_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__2));
v___x_651_ = l_Lean_Expr_isConstOf(v___x_649_, v___x_650_);
lean_dec_ref(v___x_649_);
if (v___x_651_ == 0)
{
size_t v___x_652_; size_t v___x_653_; uint8_t v___x_654_; 
lean_del_object(v___x_642_);
v___x_652_ = lean_ptr_addr(v_arg_637_);
v___x_653_ = lean_ptr_addr(v_arg_636_);
v___x_654_ = lean_usize_dec_eq(v___x_652_, v___x_653_);
if (v___x_654_ == 0)
{
uint8_t v___x_655_; 
lean_dec_ref(v_arg_638_);
lean_dec_ref(v___x_633_);
v___x_655_ = l_Lean_Expr_isTrue(v_arg_636_);
if (v___x_655_ == 0)
{
uint8_t v___x_656_; 
v___x_656_ = l_Lean_Expr_isFalse(v_arg_636_);
lean_dec_ref(v_arg_636_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_658_; 
lean_dec_ref(v_arg_637_);
v___x_657_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_657_, 0, v___x_656_);
lean_ctor_set_uint8(v___x_657_, 1, v___x_656_);
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
return v___x_658_;
}
else
{
lean_object* v___x_659_; 
lean_inc_ref(v_arg_637_);
v___x_659_ = l_Lean_Meta_Sym_mkNotS(v_arg_637_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_670_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_670_ == 0)
{
v___x_662_ = v___x_659_;
v_isShared_663_ = v_isSharedCheck_670_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_659_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_670_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_664_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpEq___closed__5, &l_Lean_Meta_Grind_NormSym_simpEq___closed__5_once, _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__5);
v___x_665_ = l_Lean_Expr_app___override(v___x_664_, v_arg_637_);
v___x_666_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_666_, 0, v_a_660_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
lean_ctor_set_uint8(v___x_666_, sizeof(void*)*2, v___x_655_);
lean_ctor_set_uint8(v___x_666_, sizeof(void*)*2 + 1, v___x_655_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_666_);
v___x_668_ = v___x_662_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec_ref(v_arg_637_);
v_a_671_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_659_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_659_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
else
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
lean_dec_ref(v_arg_636_);
v___x_679_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpEq___closed__8, &l_Lean_Meta_Grind_NormSym_simpEq___closed__8_once, _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__8);
lean_inc_ref(v_arg_637_);
v___x_680_ = l_Lean_Expr_app___override(v___x_679_, v_arg_637_);
v___x_681_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_681_, 0, v_arg_637_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
lean_ctor_set_uint8(v___x_681_, sizeof(void*)*2, v___x_635_);
lean_ctor_set_uint8(v___x_681_, sizeof(void*)*2 + 1, v___x_654_);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
}
else
{
lean_object* v___x_683_; 
lean_dec_ref(v_arg_636_);
v___x_683_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_617_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_696_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_696_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_696_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_696_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_688_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__10));
v___x_689_ = l_Lean_Expr_constLevels_x21(v___x_633_);
lean_dec_ref(v___x_633_);
v___x_690_ = l_Lean_mkConst(v___x_688_, v___x_689_);
v___x_691_ = l_Lean_mkAppB(v___x_690_, v_arg_638_, v_arg_637_);
v___x_692_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_692_, 0, v_a_684_);
lean_ctor_set(v___x_692_, 1, v___x_691_);
lean_ctor_set_uint8(v___x_692_, sizeof(void*)*2, v___x_635_);
lean_ctor_set_uint8(v___x_692_, sizeof(void*)*2 + 1, v___x_651_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_692_);
v___x_694_ = v___x_686_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec_ref(v_arg_638_);
lean_dec_ref(v_arg_637_);
lean_dec_ref(v___x_633_);
v_a_697_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_683_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_683_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
else
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_Expr_getAppFn(v_arg_636_);
if (lean_obj_tag(v___x_705_) == 4)
{
lean_object* v_declName_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v_declName_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_declName_706_);
lean_dec_ref_known(v___x_705_, 2);
v___x_707_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__12));
v___x_708_ = lean_name_eq(v_declName_706_, v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_709_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__14));
v___x_710_ = lean_name_eq(v_declName_706_, v___x_709_);
if (v___x_710_ == 0)
{
lean_object* v___x_732_; 
lean_del_object(v___x_642_);
v___x_732_ = l_Lean_Expr_getAppFn(v_arg_637_);
if (lean_obj_tag(v___x_732_) == 4)
{
lean_object* v_declName_733_; uint8_t v___x_734_; 
v_declName_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_declName_733_);
lean_dec_ref_known(v___x_732_, 2);
v___x_734_ = lean_name_eq(v_declName_733_, v___x_707_);
if (v___x_734_ == 0)
{
uint8_t v___x_735_; 
v___x_735_ = lean_name_eq(v_declName_733_, v___x_709_);
if (v___x_735_ == 0)
{
uint8_t v___x_798_; 
v___x_798_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(v_declName_733_);
lean_dec(v_declName_733_);
if (v___x_798_ == 0)
{
uint8_t v___x_799_; 
v___x_799_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(v_declName_706_);
lean_dec(v_declName_706_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec_ref(v_arg_638_);
lean_dec_ref(v_arg_637_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v___x_633_);
v___x_800_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_800_, 0, v___x_799_);
lean_ctor_set_uint8(v___x_800_, 1, v___x_799_);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
else
{
goto v___jp_736_;
}
}
else
{
lean_dec(v_declName_706_);
goto v___jp_736_;
}
}
else
{
lean_dec(v_declName_733_);
lean_dec(v_declName_706_);
goto v___jp_711_;
}
v___jp_736_:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_617_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_737_, 1);
v___x_739_ = lean_box(0);
v___x_740_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v___x_739_, v_a_618_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_742_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_740_, 1);
lean_inc(v_a_738_);
lean_inc_ref(v_arg_637_);
lean_inc_ref(v_arg_638_);
lean_inc_ref(v___x_633_);
v___x_742_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v___x_633_, v_arg_638_, v_arg_637_, v_a_738_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_744_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_742_, 1);
lean_inc_ref(v_arg_636_);
lean_inc_ref(v___x_633_);
v___x_744_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v___x_633_, v_arg_638_, v_arg_636_, v_a_738_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_746_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v___x_744_, 1);
v___x_746_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v___x_633_, v_a_741_, v_a_743_, v_a_745_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_757_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_757_ == 0)
{
v___x_749_ = v___x_746_;
v_isShared_750_ = v_isSharedCheck_757_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_746_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_757_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_751_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpEq___closed__20, &l_Lean_Meta_Grind_NormSym_simpEq___closed__20_once, _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__20);
v___x_752_ = l_Lean_mkAppB(v___x_751_, v_arg_637_, v_arg_636_);
v___x_753_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_753_, 0, v_a_747_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
lean_ctor_set_uint8(v___x_753_, sizeof(void*)*2, v___x_735_);
lean_ctor_set_uint8(v___x_753_, sizeof(void*)*2 + 1, v___x_735_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_753_);
v___x_755_ = v___x_749_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec_ref(v_arg_637_);
lean_dec_ref(v_arg_636_);
v_a_758_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_746_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_746_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v_a_743_);
lean_dec(v_a_741_);
lean_dec_ref(v_arg_637_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v___x_633_);
v_a_766_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_744_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_744_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
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
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec(v_a_741_);
lean_dec(v_a_738_);
lean_dec_ref(v_arg_638_);
lean_dec_ref(v_arg_637_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v___x_633_);
v_a_774_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_742_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_742_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_dec(v_a_738_);
lean_dec_ref(v_arg_638_);
lean_dec_ref(v_arg_637_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v___x_633_);
v_a_782_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_740_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_740_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec_ref(v_arg_638_);
lean_dec_ref(v_arg_637_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v___x_633_);
v_a_790_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_737_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_737_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
else
{
lean_dec(v_declName_733_);
lean_dec(v_declName_706_);
goto v___jp_711_;
}
}
else
{
lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec_ref(v___x_732_);
lean_dec(v_declName_706_);
lean_dec_ref(v_arg_638_);
lean_dec_ref(v_arg_637_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v___x_633_);
v___x_802_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_802_, 0, v___x_710_);
lean_ctor_set_uint8(v___x_802_, 1, v___x_710_);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
}
else
{
lean_dec(v_declName_706_);
lean_dec_ref(v_arg_638_);
lean_dec_ref(v_arg_637_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v___x_633_);
goto v___jp_644_;
}
v___jp_711_:
{
lean_object* v___x_712_; 
lean_inc_ref(v_arg_637_);
lean_inc_ref(v_arg_636_);
v___x_712_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v___x_633_, v_arg_638_, v_arg_636_, v_arg_637_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_723_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_723_ == 0)
{
v___x_715_ = v___x_712_;
v_isShared_716_ = v_isSharedCheck_723_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_712_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_723_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_717_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpEq___closed__17, &l_Lean_Meta_Grind_NormSym_simpEq___closed__17_once, _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__17);
v___x_718_ = l_Lean_mkAppB(v___x_717_, v_arg_637_, v_arg_636_);
v___x_719_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_719_, 0, v_a_713_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
lean_ctor_set_uint8(v___x_719_, sizeof(void*)*2, v___x_710_);
lean_ctor_set_uint8(v___x_719_, sizeof(void*)*2 + 1, v___x_710_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_719_);
v___x_721_ = v___x_715_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec_ref(v_arg_637_);
lean_dec_ref(v_arg_636_);
v_a_724_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_712_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_712_);
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
}
else
{
lean_dec(v_declName_706_);
lean_dec_ref(v_arg_638_);
lean_dec_ref(v_arg_637_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v___x_633_);
goto v___jp_644_;
}
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; 
lean_dec_ref(v___x_705_);
lean_del_object(v___x_642_);
lean_dec_ref(v_arg_638_);
lean_dec_ref(v_arg_637_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v___x_633_);
v___x_804_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
return v___x_805_;
}
}
v___jp_644_:
{
lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_645_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_645_);
v___x_647_ = v___x_642_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec_ref(v_arg_638_);
lean_dec_ref(v_arg_637_);
lean_dec_ref(v_arg_636_);
lean_dec_ref(v___x_633_);
v_a_807_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_639_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_639_);
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
}
}
}
v___jp_624_:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
return v___x_626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpEq___boxed(lean_object* v_e_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Lean_Meta_Grind_NormSym_simpEq(v_e_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_e_815_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0(lean_object* v_f_827_, lean_object* v_a_u2081_828_, lean_object* v_a_u2082_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___redArg(v_f_827_, v_a_u2081_828_, v_a_u2082_829_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___boxed(lean_object* v_f_841_, lean_object* v_a_u2081_842_, lean_object* v_a_u2082_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0(v_f_841_, v_a_u2081_842_, v_a_u2082_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___redArg(lean_object* v_declName_855_, lean_object* v_us_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = l_Lean_Expr_const___override(v_declName_855_, v_us_856_);
v___x_860_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_859_, v___y_857_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___redArg___boxed(lean_object* v_declName_861_, lean_object* v_us_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___redArg(v_declName_861_, v_us_862_, v___y_863_);
lean_dec(v___y_863_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0(lean_object* v_declName_866_, lean_object* v_us_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___redArg(v_declName_866_, v_us_867_, v___y_872_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___boxed(lean_object* v_declName_879_, lean_object* v_us_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0(v_declName_879_, v_us_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1_spec__1(lean_object* v_f_892_, lean_object* v_a_u2081_893_, lean_object* v_a_u2082_894_, lean_object* v_a_u2083_895_, lean_object* v_a_u2084_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v_f_892_, v_a_u2081_893_, v_a_u2082_894_, v_a_u2083_895_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_909_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v___x_907_, 1);
v___x_909_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(v_a_908_, v_a_u2084_896_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
return v___x_909_;
}
else
{
lean_dec_ref(v_a_u2084_896_);
return v___x_907_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1_spec__1___boxed(lean_object* v_f_910_, lean_object* v_a_u2081_911_, lean_object* v_a_u2082_912_, lean_object* v_a_u2083_913_, lean_object* v_a_u2084_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1_spec__1(v_f_910_, v_a_u2081_911_, v_a_u2082_912_, v_a_u2083_913_, v_a_u2084_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1(lean_object* v_f_926_, lean_object* v_a_u2081_927_, lean_object* v_a_u2082_928_, lean_object* v_a_u2083_929_, lean_object* v_a_u2084_930_, lean_object* v_a_u2085_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1_spec__1(v_f_926_, v_a_u2081_927_, v_a_u2082_928_, v_a_u2083_929_, v_a_u2084_930_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_944_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v___x_942_, 1);
v___x_944_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(v_a_943_, v_a_u2085_931_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
return v___x_944_;
}
else
{
lean_dec_ref(v_a_u2085_931_);
return v___x_942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1___boxed(lean_object* v_f_945_, lean_object* v_a_u2081_946_, lean_object* v_a_u2082_947_, lean_object* v_a_u2083_948_, lean_object* v_a_u2084_949_, lean_object* v_a_u2085_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1(v_f_945_, v_a_u2081_946_, v_a_u2082_947_, v_a_u2083_948_, v_a_u2084_949_, v_a_u2085_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpDIte(lean_object* v_e_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_985_ = l_Lean_Expr_cleanupAnnotations(v_e_971_);
v___x_986_ = l_Lean_Expr_isApp(v___x_985_);
if (v___x_986_ == 0)
{
lean_dec_ref(v___x_985_);
goto v___jp_982_;
}
else
{
lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_987_ = l_Lean_Expr_appFnCleanup___redArg(v___x_985_);
v___x_988_ = l_Lean_Expr_isApp(v___x_987_);
if (v___x_988_ == 0)
{
lean_dec_ref(v___x_987_);
lean_dec_ref(v___x_985_);
goto v___jp_982_;
}
else
{
lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_989_ = l_Lean_Expr_appFnCleanup___redArg(v___x_987_);
v___x_990_ = l_Lean_Expr_isApp(v___x_989_);
if (v___x_990_ == 0)
{
lean_dec_ref(v___x_989_);
lean_dec_ref(v___x_987_);
lean_dec_ref(v___x_985_);
goto v___jp_982_;
}
else
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = l_Lean_Expr_appFnCleanup___redArg(v___x_989_);
v___x_992_ = l_Lean_Expr_isApp(v___x_991_);
if (v___x_992_ == 0)
{
lean_dec_ref(v___x_991_);
lean_dec_ref(v___x_989_);
lean_dec_ref(v___x_987_);
lean_dec_ref(v___x_985_);
goto v___jp_982_;
}
else
{
lean_object* v___x_993_; uint8_t v___x_994_; 
v___x_993_ = l_Lean_Expr_appFnCleanup___redArg(v___x_991_);
v___x_994_ = l_Lean_Expr_isApp(v___x_993_);
if (v___x_994_ == 0)
{
lean_dec_ref(v___x_993_);
lean_dec_ref(v___x_991_);
lean_dec_ref(v___x_989_);
lean_dec_ref(v___x_987_);
lean_dec_ref(v___x_985_);
goto v___jp_982_;
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_995_ = l_Lean_Expr_appFnCleanup___redArg(v___x_993_);
v___x_996_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpDIte___closed__1));
v___x_997_ = l_Lean_Expr_isConstOf(v___x_995_, v___x_996_);
if (v___x_997_ == 0)
{
lean_dec_ref(v___x_995_);
lean_dec_ref(v___x_993_);
lean_dec_ref(v___x_991_);
lean_dec_ref(v___x_989_);
lean_dec_ref(v___x_987_);
lean_dec_ref(v___x_985_);
goto v___jp_982_;
}
else
{
lean_object* v_arg_998_; 
v_arg_998_ = lean_ctor_get(v___x_987_, 1);
lean_inc_ref(v_arg_998_);
lean_dec_ref(v___x_987_);
if (lean_obj_tag(v_arg_998_) == 6)
{
lean_object* v_body_999_; uint8_t v___x_1000_; 
v_body_999_ = lean_ctor_get(v_arg_998_, 2);
lean_inc_ref(v_body_999_);
lean_dec_ref_known(v_arg_998_, 3);
v___x_1000_ = l_Lean_Expr_hasLooseBVars(v_body_999_);
if (v___x_1000_ == 0)
{
lean_object* v_arg_1001_; 
v_arg_1001_ = lean_ctor_get(v___x_985_, 1);
lean_inc_ref(v_arg_1001_);
lean_dec_ref(v___x_985_);
if (lean_obj_tag(v_arg_1001_) == 6)
{
lean_object* v_body_1002_; uint8_t v___x_1003_; 
v_body_1002_ = lean_ctor_get(v_arg_1001_, 2);
lean_inc_ref(v_body_1002_);
lean_dec_ref_known(v_arg_1001_, 3);
v___x_1003_ = l_Lean_Expr_hasLooseBVars(v_body_1002_);
if (v___x_1003_ == 0)
{
lean_object* v_arg_1004_; lean_object* v_arg_1005_; lean_object* v_arg_1006_; lean_object* v_us_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v_arg_1004_ = lean_ctor_get(v___x_989_, 1);
lean_inc_ref(v_arg_1004_);
lean_dec_ref(v___x_989_);
v_arg_1005_ = lean_ctor_get(v___x_991_, 1);
lean_inc_ref(v_arg_1005_);
lean_dec_ref(v___x_991_);
v_arg_1006_ = lean_ctor_get(v___x_993_, 1);
lean_inc_ref(v_arg_1006_);
lean_dec_ref(v___x_993_);
v_us_1007_ = l_Lean_Expr_constLevels_x21(v___x_995_);
lean_dec_ref(v___x_995_);
v___x_1008_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpDIte___closed__3));
lean_inc(v_us_1007_);
v___x_1009_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___redArg(v___x_1008_, v_us_1007_, v_a_976_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1011_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_a_1010_);
lean_dec_ref_known(v___x_1009_, 1);
lean_inc_ref(v_body_1002_);
lean_inc_ref(v_body_999_);
lean_inc_ref(v_arg_1004_);
lean_inc_ref(v_arg_1005_);
lean_inc_ref(v_arg_1006_);
v___x_1011_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1(v_a_1010_, v_arg_1006_, v_arg_1005_, v_arg_1004_, v_body_999_, v_body_1002_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1023_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1014_ = v___x_1011_;
v_isShared_1015_ = v_isSharedCheck_1023_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1011_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1023_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1016_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpDIte___closed__5));
v___x_1017_ = l_Lean_mkConst(v___x_1016_, v_us_1007_);
v___x_1018_ = l_Lean_mkApp5(v___x_1017_, v_arg_1005_, v_arg_1006_, v_body_999_, v_body_1002_, v_arg_1004_);
v___x_1019_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1019_, 0, v_a_1012_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
lean_ctor_set_uint8(v___x_1019_, sizeof(void*)*2, v___x_1003_);
lean_ctor_set_uint8(v___x_1019_, sizeof(void*)*2 + 1, v___x_1003_);
if (v_isShared_1015_ == 0)
{
lean_ctor_set(v___x_1014_, 0, v___x_1019_);
v___x_1021_ = v___x_1014_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec(v_us_1007_);
lean_dec_ref(v_arg_1006_);
lean_dec_ref(v_arg_1005_);
lean_dec_ref(v_arg_1004_);
lean_dec_ref(v_body_1002_);
lean_dec_ref(v_body_999_);
v_a_1024_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1011_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1011_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec(v_us_1007_);
lean_dec_ref(v_arg_1006_);
lean_dec_ref(v_arg_1005_);
lean_dec_ref(v_arg_1004_);
lean_dec_ref(v_body_1002_);
lean_dec_ref(v_body_999_);
v_a_1032_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1009_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1009_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
else
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
lean_dec_ref(v_body_1002_);
lean_dec_ref(v_body_999_);
lean_dec_ref(v___x_995_);
lean_dec_ref(v___x_993_);
lean_dec_ref(v___x_991_);
lean_dec_ref(v___x_989_);
v___x_1040_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1040_, 0, v___x_1000_);
lean_ctor_set_uint8(v___x_1040_, 1, v___x_1000_);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
return v___x_1041_;
}
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_dec_ref(v_arg_1001_);
lean_dec_ref(v_body_999_);
lean_dec_ref(v___x_995_);
lean_dec_ref(v___x_993_);
lean_dec_ref(v___x_991_);
lean_dec_ref(v___x_989_);
v___x_1042_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1042_, 0, v___x_1000_);
lean_ctor_set_uint8(v___x_1042_, 1, v___x_1000_);
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_dec_ref(v_body_999_);
lean_dec_ref(v___x_995_);
lean_dec_ref(v___x_993_);
lean_dec_ref(v___x_991_);
lean_dec_ref(v___x_989_);
lean_dec_ref(v___x_985_);
v___x_1044_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
return v___x_1045_;
}
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec_ref(v_arg_998_);
lean_dec_ref(v___x_995_);
lean_dec_ref(v___x_993_);
lean_dec_ref(v___x_991_);
lean_dec_ref(v___x_989_);
lean_dec_ref(v___x_985_);
v___x_1046_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
}
}
}
}
}
}
v___jp_982_:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpDIte___boxed(lean_object* v_e_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_Meta_Grind_NormSym_simpDIte(v_e_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec_ref(v_e_1048_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(lean_object* v_x_1060_, uint8_t v_bi_1061_, lean_object* v_t_1062_, lean_object* v_b_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___y_1072_; lean_object* v___x_1075_; uint8_t v_debug_1076_; 
v___x_1075_ = lean_st_ref_get(v___y_1065_);
v_debug_1076_ = lean_ctor_get_uint8(v___x_1075_, sizeof(void*)*13);
lean_dec(v___x_1075_);
if (v_debug_1076_ == 0)
{
v___y_1072_ = v___y_1065_;
goto v___jp_1071_;
}
else
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1062_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v___x_1078_; 
lean_dec_ref_known(v___x_1077_, 1);
v___x_1078_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_dec_ref_known(v___x_1078_, 1);
v___y_1072_ = v___y_1065_;
goto v___jp_1071_;
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec_ref(v_b_1063_);
lean_dec_ref(v_t_1062_);
lean_dec(v_x_1060_);
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
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
else
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
lean_dec_ref(v_b_1063_);
lean_dec_ref(v_t_1062_);
lean_dec(v_x_1060_);
v_a_1087_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1089_ = v___x_1077_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1077_);
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
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
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
}
v___jp_1071_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = l_Lean_Expr_lam___override(v_x_1060_, v_t_1062_, v_b_1063_, v_bi_1061_);
v___x_1074_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1073_, v___y_1072_);
return v___x_1074_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg___boxed(lean_object* v_x_1095_, lean_object* v_bi_1096_, lean_object* v_t_1097_, lean_object* v_b_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
uint8_t v_bi_boxed_1106_; lean_object* v_res_1107_; 
v_bi_boxed_1106_ = lean_unbox(v_bi_1096_);
v_res_1107_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_x_1095_, v_bi_boxed_1106_, v_t_1097_, v_b_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0(lean_object* v_x_1108_, uint8_t v_bi_1109_, lean_object* v_t_1110_, lean_object* v_b_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_x_1108_, v_bi_1109_, v_t_1110_, v_b_1111_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___boxed(lean_object* v_x_1123_, lean_object* v_bi_1124_, lean_object* v_t_1125_, lean_object* v_b_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
uint8_t v_bi_boxed_1137_; lean_object* v_res_1138_; 
v_bi_boxed_1137_ = lean_unbox(v_bi_1124_);
v_res_1138_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0(v_x_1123_, v_bi_boxed_1137_, v_t_1125_, v_b_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(lean_object* v_idx_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = l_Lean_Expr_bvar___override(v_idx_1139_);
v___x_1143_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1142_, v___y_1140_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg___boxed(lean_object* v_idx_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(v_idx_1144_, v___y_1145_);
lean_dec(v___y_1145_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1(lean_object* v_idx_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(v_idx_1148_, v___y_1153_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___boxed(lean_object* v_idx_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1(v_idx_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(lean_object* v_x_1172_, uint8_t v_bi_1173_, lean_object* v_t_1174_, lean_object* v_b_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___y_1184_; lean_object* v___x_1187_; uint8_t v_debug_1188_; 
v___x_1187_ = lean_st_ref_get(v___y_1177_);
v_debug_1188_ = lean_ctor_get_uint8(v___x_1187_, sizeof(void*)*13);
lean_dec(v___x_1187_);
if (v_debug_1188_ == 0)
{
v___y_1184_ = v___y_1177_;
goto v___jp_1183_;
}
else
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1174_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v___x_1190_; 
lean_dec_ref_known(v___x_1189_, 1);
v___x_1190_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_dec_ref_known(v___x_1190_, 1);
v___y_1184_ = v___y_1177_;
goto v___jp_1183_;
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec_ref(v_b_1175_);
lean_dec_ref(v_t_1174_);
lean_dec(v_x_1172_);
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1190_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1190_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec_ref(v_b_1175_);
lean_dec_ref(v_t_1174_);
lean_dec(v_x_1172_);
v_a_1199_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1189_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1189_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
v___jp_1183_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = l_Lean_Expr_forallE___override(v_x_1172_, v_t_1174_, v_b_1175_, v_bi_1173_);
v___x_1186_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1185_, v___y_1184_);
return v___x_1186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg___boxed(lean_object* v_x_1207_, lean_object* v_bi_1208_, lean_object* v_t_1209_, lean_object* v_b_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
uint8_t v_bi_boxed_1218_; lean_object* v_res_1219_; 
v_bi_boxed_1218_ = lean_unbox(v_bi_1208_);
v_res_1219_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_x_1207_, v_bi_boxed_1218_, v_t_1209_, v_b_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2(lean_object* v_x_1220_, uint8_t v_bi_1221_, lean_object* v_t_1222_, lean_object* v_b_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_x_1220_, v_bi_1221_, v_t_1222_, v_b_1223_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___boxed(lean_object* v_x_1235_, lean_object* v_bi_1236_, lean_object* v_t_1237_, lean_object* v_b_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
uint8_t v_bi_boxed_1249_; lean_object* v_res_1250_; 
v_bi_boxed_1249_ = lean_unbox(v_bi_1236_);
v_res_1250_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2(v_x_1235_, v_bi_boxed_1249_, v_t_1237_, v_b_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
return v_res_1250_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__6(void){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = lean_box(0);
v___x_1265_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__5));
v___x_1266_ = l_Lean_mkConst(v___x_1265_, v___x_1264_);
return v___x_1266_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__17(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1284_ = lean_box(0);
v___x_1285_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__16));
v___x_1286_ = l_Lean_mkConst(v___x_1285_, v___x_1284_);
return v___x_1286_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__20(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1291_ = lean_box(0);
v___x_1292_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__19));
v___x_1293_ = l_Lean_mkConst(v___x_1292_, v___x_1291_);
return v___x_1293_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__23(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = lean_box(0);
v___x_1299_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__22));
v___x_1300_ = l_Lean_mkConst(v___x_1299_, v___x_1298_);
return v___x_1300_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__26(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_box(0);
v___x_1307_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__25));
v___x_1308_ = l_Lean_mkConst(v___x_1307_, v___x_1306_);
return v___x_1308_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__29(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1314_ = lean_box(0);
v___x_1315_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__28));
v___x_1316_ = l_Lean_mkConst(v___x_1315_, v___x_1314_);
return v___x_1316_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__32(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = lean_box(0);
v___x_1323_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__31));
v___x_1324_ = l_Lean_mkConst(v___x_1323_, v___x_1322_);
return v___x_1324_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__39(void){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1338_ = lean_box(0);
v___x_1339_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__38));
v___x_1340_ = l_Lean_mkConst(v___x_1339_, v___x_1338_);
return v___x_1340_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__42(void){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1346_ = lean_box(0);
v___x_1347_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__41));
v___x_1348_ = l_Lean_mkConst(v___x_1347_, v___x_1346_);
return v___x_1348_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__45(void){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1354_ = lean_box(0);
v___x_1355_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__44));
v___x_1356_ = l_Lean_mkConst(v___x_1355_, v___x_1354_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_pushNot(lean_object* v_e_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; uint8_t v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; uint8_t v___y_1382_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1440_ = l_Lean_Expr_cleanupAnnotations(v_e_1357_);
v___x_1441_ = l_Lean_Expr_isApp(v___x_1440_);
if (v___x_1441_ == 0)
{
lean_dec_ref(v___x_1440_);
goto v___jp_1437_;
}
else
{
lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v___x_1442_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1440_);
v___x_1443_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__3));
v___x_1444_ = l_Lean_Expr_isConstOf(v___x_1442_, v___x_1443_);
lean_dec_ref(v___x_1442_);
if (v___x_1444_ == 0)
{
lean_dec_ref(v___x_1440_);
goto v___jp_1437_;
}
else
{
lean_object* v_arg_1445_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___x_1506_; 
v_arg_1445_ = lean_ctor_get(v___x_1440_, 1);
lean_inc_ref_n(v_arg_1445_, 2);
lean_dec_ref(v___x_1440_);
v___x_1506_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1445_, v_a_1364_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1890_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1509_ = v___x_1506_;
v_isShared_1510_ = v_isSharedCheck_1890_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1506_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1890_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; uint8_t v___x_1513_; 
v___x_1511_ = l_Lean_Expr_cleanupAnnotations(v_a_1507_);
lean_dec(v_a_1507_);
v___x_1512_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_1513_ = l_Lean_Expr_isConstOf(v___x_1511_, v___x_1512_);
if (v___x_1513_ == 0)
{
lean_object* v___x_1514_; uint8_t v___x_1515_; 
v___x_1514_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__10));
v___x_1515_ = l_Lean_Expr_isConstOf(v___x_1511_, v___x_1514_);
if (v___x_1515_ == 0)
{
uint8_t v___x_1516_; 
v___x_1516_ = l_Lean_Expr_isApp(v___x_1511_);
if (v___x_1516_ == 0)
{
lean_dec_ref(v___x_1511_);
lean_del_object(v___x_1509_);
v___y_1447_ = v_a_1358_;
v___y_1448_ = v_a_1359_;
v___y_1449_ = v_a_1360_;
v___y_1450_ = v_a_1361_;
v___y_1451_ = v_a_1362_;
v___y_1452_ = v_a_1363_;
v___y_1453_ = v_a_1364_;
v___y_1454_ = v_a_1365_;
v___y_1455_ = v_a_1366_;
goto v___jp_1446_;
}
else
{
lean_object* v_arg_1517_; lean_object* v___x_1518_; uint8_t v___x_1519_; 
v_arg_1517_ = lean_ctor_get(v___x_1511_, 1);
lean_inc_ref(v_arg_1517_);
v___x_1518_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1511_);
lean_dec_ref(v___x_1511_);
v___x_1519_ = l_Lean_Expr_isConstOf(v___x_1518_, v___x_1443_);
if (v___x_1519_ == 0)
{
uint8_t v___x_1520_; 
lean_del_object(v___x_1509_);
v___x_1520_ = l_Lean_Expr_isApp(v___x_1518_);
if (v___x_1520_ == 0)
{
lean_dec_ref(v___x_1518_);
lean_dec_ref(v_arg_1517_);
v___y_1447_ = v_a_1358_;
v___y_1448_ = v_a_1359_;
v___y_1449_ = v_a_1360_;
v___y_1450_ = v_a_1361_;
v___y_1451_ = v_a_1362_;
v___y_1452_ = v_a_1363_;
v___y_1453_ = v_a_1364_;
v___y_1454_ = v_a_1365_;
v___y_1455_ = v_a_1366_;
goto v___jp_1446_;
}
else
{
lean_object* v_arg_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; uint8_t v___x_1524_; 
v_arg_1521_ = lean_ctor_get(v___x_1518_, 1);
lean_inc_ref(v_arg_1521_);
v___x_1522_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1518_);
lean_dec_ref(v___x_1518_);
v___x_1523_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_etaReduce___closed__1));
v___x_1524_ = l_Lean_Expr_isConstOf(v___x_1522_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1525_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__12));
v___x_1526_ = l_Lean_Expr_isConstOf(v___x_1522_, v___x_1525_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1527_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__14));
v___x_1528_ = l_Lean_Expr_isConstOf(v___x_1522_, v___x_1527_);
if (v___x_1528_ == 0)
{
uint8_t v___x_1529_; 
v___x_1529_ = l_Lean_Expr_isApp(v___x_1522_);
if (v___x_1529_ == 0)
{
lean_dec_ref(v___x_1522_);
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_arg_1517_);
v___y_1447_ = v_a_1358_;
v___y_1448_ = v_a_1359_;
v___y_1449_ = v_a_1360_;
v___y_1450_ = v_a_1361_;
v___y_1451_ = v_a_1362_;
v___y_1452_ = v_a_1363_;
v___y_1453_ = v_a_1364_;
v___y_1454_ = v_a_1365_;
v___y_1455_ = v_a_1366_;
goto v___jp_1446_;
}
else
{
lean_object* v_arg_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; uint8_t v___x_1533_; 
v_arg_1530_ = lean_ctor_get(v___x_1522_, 1);
lean_inc_ref(v_arg_1530_);
v___x_1531_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1522_);
lean_dec_ref(v___x_1522_);
v___x_1532_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__1));
v___x_1533_ = l_Lean_Expr_isConstOf(v___x_1531_, v___x_1532_);
if (v___x_1533_ == 0)
{
uint8_t v___x_1534_; 
v___x_1534_ = l_Lean_Expr_isApp(v___x_1531_);
if (v___x_1534_ == 0)
{
lean_dec_ref(v___x_1531_);
lean_dec_ref(v_arg_1530_);
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_arg_1517_);
v___y_1447_ = v_a_1358_;
v___y_1448_ = v_a_1359_;
v___y_1449_ = v_a_1360_;
v___y_1450_ = v_a_1361_;
v___y_1451_ = v_a_1362_;
v___y_1452_ = v_a_1363_;
v___y_1453_ = v_a_1364_;
v___y_1454_ = v_a_1365_;
v___y_1455_ = v_a_1366_;
goto v___jp_1446_;
}
else
{
lean_object* v___x_1535_; uint8_t v___x_1536_; 
v___x_1535_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1531_);
v___x_1536_ = l_Lean_Expr_isApp(v___x_1535_);
if (v___x_1536_ == 0)
{
lean_dec_ref(v___x_1535_);
lean_dec_ref(v___x_1531_);
lean_dec_ref(v_arg_1530_);
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_arg_1517_);
v___y_1447_ = v_a_1358_;
v___y_1448_ = v_a_1359_;
v___y_1449_ = v_a_1360_;
v___y_1450_ = v_a_1361_;
v___y_1451_ = v_a_1362_;
v___y_1452_ = v_a_1363_;
v___y_1453_ = v_a_1364_;
v___y_1454_ = v_a_1365_;
v___y_1455_ = v_a_1366_;
goto v___jp_1446_;
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; 
v___x_1537_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1535_);
v___x_1538_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpDIte___closed__3));
v___x_1539_ = l_Lean_Expr_isConstOf(v___x_1537_, v___x_1538_);
if (v___x_1539_ == 0)
{
lean_dec_ref(v___x_1537_);
lean_dec_ref(v___x_1535_);
lean_dec_ref(v___x_1531_);
lean_dec_ref(v_arg_1530_);
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_arg_1517_);
v___y_1447_ = v_a_1358_;
v___y_1448_ = v_a_1359_;
v___y_1449_ = v_a_1360_;
v___y_1450_ = v_a_1361_;
v___y_1451_ = v_a_1362_;
v___y_1452_ = v_a_1363_;
v___y_1453_ = v_a_1364_;
v___y_1454_ = v_a_1365_;
v___y_1455_ = v_a_1366_;
goto v___jp_1446_;
}
else
{
lean_object* v_arg_1540_; lean_object* v_arg_1541_; lean_object* v___x_1542_; 
lean_dec_ref(v_arg_1445_);
v_arg_1540_ = lean_ctor_get(v___x_1531_, 1);
lean_inc_ref(v_arg_1540_);
lean_dec_ref(v___x_1531_);
v_arg_1541_ = lean_ctor_get(v___x_1535_, 1);
lean_inc_ref(v_arg_1541_);
lean_dec_ref(v___x_1535_);
lean_inc_ref(v_arg_1521_);
v___x_1542_ = l_Lean_Meta_Sym_mkNotS(v_arg_1521_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1544_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
lean_inc_ref(v_arg_1517_);
v___x_1544_ = l_Lean_Meta_Sym_mkNotS(v_arg_1517_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1546_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1544_, 1);
lean_inc_ref(v_arg_1530_);
lean_inc_ref(v_arg_1540_);
v___x_1546_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1(v___x_1537_, v_arg_1541_, v_arg_1540_, v_arg_1530_, v_a_1543_, v_a_1545_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1557_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1549_ = v___x_1546_;
v_isShared_1550_ = v_isSharedCheck_1557_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1557_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; 
v___x_1551_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__17, &l_Lean_Meta_Grind_NormSym_pushNot___closed__17_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__17);
v___x_1552_ = l_Lean_mkApp4(v___x_1551_, v_arg_1540_, v_arg_1530_, v_arg_1521_, v_arg_1517_);
v___x_1553_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1553_, 0, v_a_1547_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
lean_ctor_set_uint8(v___x_1553_, sizeof(void*)*2, v___x_1533_);
lean_ctor_set_uint8(v___x_1553_, sizeof(void*)*2 + 1, v___x_1533_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1553_);
v___x_1555_ = v___x_1549_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec_ref(v_arg_1540_);
lean_dec_ref(v_arg_1530_);
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_arg_1517_);
v_a_1558_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1546_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1546_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec(v_a_1543_);
lean_dec_ref(v_arg_1541_);
lean_dec_ref(v_arg_1540_);
lean_dec_ref(v___x_1537_);
lean_dec_ref(v_arg_1530_);
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_arg_1517_);
v_a_1566_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1544_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1544_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec_ref(v_arg_1541_);
lean_dec_ref(v_arg_1540_);
lean_dec_ref(v___x_1537_);
lean_dec_ref(v_arg_1530_);
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_arg_1517_);
v_a_1574_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1542_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1542_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
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
}
}
else
{
uint8_t v___x_1582_; 
lean_dec_ref(v_arg_1445_);
v___x_1582_ = l_Lean_Expr_isProp(v_arg_1530_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1517_, v_a_1364_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1657_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1657_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1657_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
v___x_1588_ = l_Lean_Expr_cleanupAnnotations(v_a_1584_);
lean_dec(v_a_1584_);
v___x_1589_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__14));
v___x_1590_ = l_Lean_Expr_isConstOf(v___x_1588_, v___x_1589_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__12));
v___x_1592_ = l_Lean_Expr_isConstOf(v___x_1588_, v___x_1591_);
lean_dec_ref(v___x_1588_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1595_; 
lean_dec_ref(v___x_1531_);
lean_dec_ref(v_arg_1530_);
lean_dec_ref(v_arg_1521_);
v___x_1593_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1593_, 0, v___x_1582_);
lean_ctor_set_uint8(v___x_1593_, 1, v___x_1582_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1593_);
v___x_1595_ = v___x_1586_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
else
{
lean_object* v___x_1597_; 
lean_del_object(v___x_1586_);
v___x_1597_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_1361_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1599_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
lean_dec_ref_known(v___x_1597_, 1);
lean_inc_ref(v_arg_1521_);
v___x_1599_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v___x_1531_, v_arg_1530_, v_arg_1521_, v_a_1598_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1610_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1602_ = v___x_1599_;
v_isShared_1603_ = v_isSharedCheck_1610_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1599_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1610_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1604_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__20, &l_Lean_Meta_Grind_NormSym_pushNot___closed__20_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__20);
v___x_1605_ = l_Lean_Expr_app___override(v___x_1604_, v_arg_1521_);
v___x_1606_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1606_, 0, v_a_1600_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
lean_ctor_set_uint8(v___x_1606_, sizeof(void*)*2, v___x_1582_);
lean_ctor_set_uint8(v___x_1606_, sizeof(void*)*2 + 1, v___x_1582_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v___x_1606_);
v___x_1608_ = v___x_1602_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec_ref(v_arg_1521_);
v_a_1611_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1599_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1599_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec_ref(v___x_1531_);
lean_dec_ref(v_arg_1530_);
lean_dec_ref(v_arg_1521_);
v_a_1619_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1597_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1597_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
else
{
lean_object* v___x_1627_; 
lean_dec_ref(v___x_1588_);
lean_del_object(v___x_1586_);
v___x_1627_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_1361_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; lean_object* v___x_1629_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1628_);
lean_dec_ref_known(v___x_1627_, 1);
lean_inc_ref(v_arg_1521_);
v___x_1629_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v___x_1531_, v_arg_1530_, v_arg_1521_, v_a_1628_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1640_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1632_ = v___x_1629_;
v_isShared_1633_ = v_isSharedCheck_1640_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1629_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1640_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1638_; 
v___x_1634_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__23, &l_Lean_Meta_Grind_NormSym_pushNot___closed__23_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__23);
v___x_1635_ = l_Lean_Expr_app___override(v___x_1634_, v_arg_1521_);
v___x_1636_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1636_, 0, v_a_1630_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
lean_ctor_set_uint8(v___x_1636_, sizeof(void*)*2, v___x_1582_);
lean_ctor_set_uint8(v___x_1636_, sizeof(void*)*2 + 1, v___x_1582_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v___x_1636_);
v___x_1638_ = v___x_1632_;
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
lean_dec_ref(v_arg_1521_);
v_a_1641_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1629_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1629_);
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
lean_dec_ref(v___x_1531_);
lean_dec_ref(v_arg_1530_);
lean_dec_ref(v_arg_1521_);
v_a_1649_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v___x_1627_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v___x_1627_);
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
}
}
else
{
lean_object* v_a_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1665_; 
lean_dec_ref(v___x_1531_);
lean_dec_ref(v_arg_1530_);
lean_dec_ref(v_arg_1521_);
v_a_1658_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1660_ = v___x_1583_;
v_isShared_1661_ = v_isSharedCheck_1665_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_a_1658_);
lean_dec(v___x_1583_);
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
else
{
lean_object* v___x_1666_; 
lean_inc_ref(v_arg_1517_);
v___x_1666_ = l_Lean_Meta_Sym_mkNotS(v_arg_1517_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1668_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref_known(v___x_1666_, 1);
lean_inc_ref(v_arg_1521_);
v___x_1668_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v___x_1531_, v_arg_1530_, v_arg_1521_, v_a_1667_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1679_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1679_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1679_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1673_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__26, &l_Lean_Meta_Grind_NormSym_pushNot___closed__26_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__26);
v___x_1674_ = l_Lean_mkAppB(v___x_1673_, v_arg_1521_, v_arg_1517_);
v___x_1675_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1675_, 0, v_a_1669_);
lean_ctor_set(v___x_1675_, 1, v___x_1674_);
lean_ctor_set_uint8(v___x_1675_, sizeof(void*)*2, v___x_1528_);
lean_ctor_set_uint8(v___x_1675_, sizeof(void*)*2 + 1, v___x_1528_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1675_);
v___x_1677_ = v___x_1671_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_arg_1517_);
v_a_1680_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1668_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1668_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_dec_ref(v___x_1531_);
lean_dec_ref(v_arg_1530_);
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_arg_1517_);
v_a_1688_ = lean_ctor_get(v___x_1666_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1666_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1666_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1696_; 
lean_dec_ref(v___x_1522_);
lean_dec_ref(v_arg_1445_);
lean_inc_ref(v_arg_1521_);
v___x_1696_ = l_Lean_Meta_Sym_mkNotS(v_arg_1521_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v___x_1698_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1696_, 1);
lean_inc_ref(v_arg_1517_);
v___x_1698_ = l_Lean_Meta_Sym_mkNotS(v_arg_1517_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v_a_1699_; lean_object* v___x_1700_; 
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc(v_a_1699_);
lean_dec_ref_known(v___x_1698_, 1);
v___x_1700_ = l_Lean_Meta_Sym_mkOrS(v_a_1697_, v_a_1699_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
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
v___x_1705_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__29, &l_Lean_Meta_Grind_NormSym_pushNot___closed__29_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__29);
v___x_1706_ = l_Lean_mkAppB(v___x_1705_, v_arg_1521_, v_arg_1517_);
v___x_1707_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1707_, 0, v_a_1701_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
lean_ctor_set_uint8(v___x_1707_, sizeof(void*)*2, v___x_1526_);
lean_ctor_set_uint8(v___x_1707_, sizeof(void*)*2 + 1, v___x_1526_);
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
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_arg_1517_);
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
lean_dec(v_a_1697_);
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_arg_1517_);
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
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_arg_1517_);
v_a_1728_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1696_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1696_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
}
else
{
lean_object* v___x_1736_; 
lean_dec_ref(v___x_1522_);
lean_dec_ref(v_arg_1445_);
lean_inc_ref(v_arg_1521_);
v___x_1736_ = l_Lean_Meta_Sym_mkNotS(v_arg_1521_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v___x_1738_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref_known(v___x_1736_, 1);
lean_inc_ref(v_arg_1517_);
v___x_1738_ = l_Lean_Meta_Sym_mkNotS(v_arg_1517_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v___x_1740_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___x_1738_, 1);
v___x_1740_ = l_Lean_Meta_Sym_mkAndS(v_a_1737_, v_a_1739_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1751_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1743_ = v___x_1740_;
v_isShared_1744_ = v_isSharedCheck_1751_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1740_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1751_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1745_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__32, &l_Lean_Meta_Grind_NormSym_pushNot___closed__32_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__32);
v___x_1746_ = l_Lean_mkAppB(v___x_1745_, v_arg_1521_, v_arg_1517_);
v___x_1747_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1747_, 0, v_a_1741_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
lean_ctor_set_uint8(v___x_1747_, sizeof(void*)*2, v___x_1524_);
lean_ctor_set_uint8(v___x_1747_, sizeof(void*)*2 + 1, v___x_1524_);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1747_);
v___x_1749_ = v___x_1743_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_arg_1517_);
v_a_1752_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1740_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1740_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec(v_a_1737_);
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_arg_1517_);
v_a_1760_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___x_1738_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1738_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_arg_1517_);
v_a_1768_ = lean_ctor_get(v___x_1736_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1736_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1736_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
else
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_dec_ref(v___x_1522_);
lean_dec_ref(v_arg_1445_);
v___x_1776_ = lean_unsigned_to_nat(0u);
v___x_1777_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(v___x_1776_, v_a_1362_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref_known(v___x_1777_, 1);
v___x_1779_ = lean_unsigned_to_nat(1u);
v___x_1780_ = lean_mk_empty_array_with_capacity(v___x_1779_);
v___x_1781_ = lean_array_push(v___x_1780_, v_a_1778_);
lean_inc_ref(v_arg_1517_);
v___x_1782_ = l_Lean_Meta_Sym_betaS(v_arg_1517_, v___x_1781_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1784_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1782_, 1);
v___x_1784_ = l_Lean_Meta_Sym_mkNotS(v_a_1783_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; lean_object* v___x_1788_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref_known(v___x_1784_, 1);
v___x_1786_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__34));
v___x_1787_ = 0;
lean_inc_ref(v_arg_1521_);
v___x_1788_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v___x_1786_, v___x_1787_, v_arg_1521_, v_a_1785_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1790_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
lean_inc_ref(v_arg_1521_);
v___x_1790_ = l_Lean_Meta_Sym_getLevel___redArg(v_arg_1521_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1804_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1804_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1804_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
v___x_1795_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__36));
v___x_1796_ = lean_box(0);
v___x_1797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1797_, 0, v_a_1791_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
v___x_1798_ = l_Lean_mkConst(v___x_1795_, v___x_1797_);
v___x_1799_ = l_Lean_mkAppB(v___x_1798_, v_arg_1521_, v_arg_1517_);
v___x_1800_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1800_, 0, v_a_1789_);
lean_ctor_set(v___x_1800_, 1, v___x_1799_);
lean_ctor_set_uint8(v___x_1800_, sizeof(void*)*2, v___x_1519_);
lean_ctor_set_uint8(v___x_1800_, sizeof(void*)*2 + 1, v___x_1519_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 0, v___x_1800_);
v___x_1802_ = v___x_1793_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
else
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1812_; 
lean_dec(v_a_1789_);
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_arg_1517_);
v_a_1805_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1812_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1807_ = v___x_1790_;
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1790_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1812_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1810_; 
if (v_isShared_1808_ == 0)
{
v___x_1810_ = v___x_1807_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
}
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_arg_1517_);
v_a_1813_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1788_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1788_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_arg_1517_);
v_a_1821_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1784_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1784_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_arg_1517_);
v_a_1829_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1782_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1782_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
lean_dec_ref(v_arg_1521_);
lean_dec_ref(v_arg_1517_);
v_a_1837_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1777_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1777_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
}
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1849_; 
lean_dec_ref(v___x_1518_);
lean_dec_ref(v_arg_1445_);
v___x_1845_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__39, &l_Lean_Meta_Grind_NormSym_pushNot___closed__39_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__39);
lean_inc_ref(v_arg_1517_);
v___x_1846_ = l_Lean_Expr_app___override(v___x_1845_, v_arg_1517_);
v___x_1847_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1847_, 0, v_arg_1517_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*2, v___x_1515_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*2 + 1, v___x_1515_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v___x_1847_);
v___x_1849_ = v___x_1509_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
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
lean_object* v___x_1851_; 
lean_dec_ref(v___x_1511_);
lean_del_object(v___x_1509_);
lean_dec_ref(v_arg_1445_);
v___x_1851_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_1361_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1861_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1854_ = v___x_1851_;
v_isShared_1855_ = v_isSharedCheck_1861_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1851_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1861_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1859_; 
v___x_1856_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__42, &l_Lean_Meta_Grind_NormSym_pushNot___closed__42_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__42);
v___x_1857_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1857_, 0, v_a_1852_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
lean_ctor_set_uint8(v___x_1857_, sizeof(void*)*2, v___x_1513_);
lean_ctor_set_uint8(v___x_1857_, sizeof(void*)*2 + 1, v___x_1513_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v___x_1857_);
v___x_1859_ = v___x_1854_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
v_a_1862_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1864_ = v___x_1851_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1851_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_a_1862_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
else
{
lean_object* v___x_1870_; 
lean_dec_ref(v___x_1511_);
lean_del_object(v___x_1509_);
lean_dec_ref(v_arg_1445_);
v___x_1870_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_1361_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1881_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1881_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1881_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; uint8_t v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1875_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__45, &l_Lean_Meta_Grind_NormSym_pushNot___closed__45_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__45);
v___x_1876_ = 0;
v___x_1877_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1877_, 0, v_a_1871_);
lean_ctor_set(v___x_1877_, 1, v___x_1875_);
lean_ctor_set_uint8(v___x_1877_, sizeof(void*)*2, v___x_1876_);
lean_ctor_set_uint8(v___x_1877_, sizeof(void*)*2 + 1, v___x_1876_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1877_);
v___x_1879_ = v___x_1873_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
else
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1889_; 
v_a_1882_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1884_ = v___x_1870_;
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1870_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1889_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1887_; 
if (v_isShared_1885_ == 0)
{
v___x_1887_ = v___x_1884_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_a_1882_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_dec_ref(v_arg_1445_);
v_a_1891_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1506_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1506_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
v___jp_1446_:
{
if (lean_obj_tag(v_arg_1445_) == 7)
{
lean_object* v_binderName_1456_; lean_object* v_binderType_1457_; lean_object* v_body_1458_; uint8_t v_binderInfo_1459_; lean_object* v___x_1460_; 
v_binderName_1456_ = lean_ctor_get(v_arg_1445_, 0);
lean_inc(v_binderName_1456_);
v_binderType_1457_ = lean_ctor_get(v_arg_1445_, 1);
lean_inc_ref_n(v_binderType_1457_, 2);
v_body_1458_ = lean_ctor_get(v_arg_1445_, 2);
lean_inc_ref(v_body_1458_);
v_binderInfo_1459_ = lean_ctor_get_uint8(v_arg_1445_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_arg_1445_, 3);
v___x_1460_ = l_Lean_Meta_isProp(v_binderType_1457_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; uint8_t v___x_1462_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1460_, 1);
v___x_1462_ = l_Lean_Expr_hasLooseBVars(v_body_1458_);
if (v___x_1462_ == 0)
{
uint8_t v___x_1463_; 
v___x_1463_ = lean_unbox(v_a_1461_);
if (v___x_1463_ == 0)
{
uint8_t v___x_1464_; 
v___x_1464_ = lean_unbox(v_a_1461_);
lean_dec(v_a_1461_);
v___y_1369_ = v___y_1453_;
v___y_1370_ = v_binderName_1456_;
v___y_1371_ = v___y_1455_;
v___y_1372_ = v___y_1448_;
v___y_1373_ = v___y_1449_;
v___y_1374_ = v___y_1454_;
v___y_1375_ = v_binderType_1457_;
v___y_1376_ = v___y_1452_;
v___y_1377_ = v_binderInfo_1459_;
v___y_1378_ = v___y_1450_;
v___y_1379_ = v___y_1451_;
v___y_1380_ = v_body_1458_;
v___y_1381_ = v___y_1447_;
v___y_1382_ = v___x_1464_;
goto v___jp_1368_;
}
else
{
lean_object* v___x_1465_; 
lean_dec(v_a_1461_);
lean_dec(v_binderName_1456_);
lean_inc_ref(v_body_1458_);
v___x_1465_ = l_Lean_Meta_Sym_mkNotS(v_body_1458_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v_a_1466_; lean_object* v___x_1467_; 
v_a_1466_ = lean_ctor_get(v___x_1465_, 0);
lean_inc(v_a_1466_);
lean_dec_ref_known(v___x_1465_, 1);
lean_inc_ref(v_binderType_1457_);
v___x_1467_ = l_Lean_Meta_Sym_mkAndS(v_binderType_1457_, v_a_1466_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1478_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1470_ = v___x_1467_;
v_isShared_1471_ = v_isSharedCheck_1478_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1467_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1478_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1472_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__6, &l_Lean_Meta_Grind_NormSym_pushNot___closed__6_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__6);
v___x_1473_ = l_Lean_mkAppB(v___x_1472_, v_binderType_1457_, v_body_1458_);
v___x_1474_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1474_, 0, v_a_1468_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
lean_ctor_set_uint8(v___x_1474_, sizeof(void*)*2, v___x_1462_);
lean_ctor_set_uint8(v___x_1474_, sizeof(void*)*2 + 1, v___x_1462_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 0, v___x_1474_);
v___x_1476_ = v___x_1470_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec_ref(v_body_1458_);
lean_dec_ref(v_binderType_1457_);
v_a_1479_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1467_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1467_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec_ref(v_body_1458_);
lean_dec_ref(v_binderType_1457_);
v_a_1487_ = lean_ctor_get(v___x_1465_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1465_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1465_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
}
}
else
{
uint8_t v___x_1495_; 
lean_dec(v_a_1461_);
v___x_1495_ = 0;
v___y_1369_ = v___y_1453_;
v___y_1370_ = v_binderName_1456_;
v___y_1371_ = v___y_1455_;
v___y_1372_ = v___y_1448_;
v___y_1373_ = v___y_1449_;
v___y_1374_ = v___y_1454_;
v___y_1375_ = v_binderType_1457_;
v___y_1376_ = v___y_1452_;
v___y_1377_ = v_binderInfo_1459_;
v___y_1378_ = v___y_1450_;
v___y_1379_ = v___y_1451_;
v___y_1380_ = v_body_1458_;
v___y_1381_ = v___y_1447_;
v___y_1382_ = v___x_1495_;
goto v___jp_1368_;
}
}
else
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
lean_dec_ref(v_body_1458_);
lean_dec_ref(v_binderType_1457_);
lean_dec(v_binderName_1456_);
v_a_1496_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1498_ = v___x_1460_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1460_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
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
lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec_ref(v_arg_1445_);
v___x_1504_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
return v___x_1505_;
}
}
}
}
v___jp_1368_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
lean_inc_ref(v___y_1380_);
lean_inc_ref(v___y_1375_);
lean_inc(v___y_1370_);
v___x_1383_ = l_Lean_mkLambda(v___y_1370_, v___y_1377_, v___y_1375_, v___y_1380_);
v___x_1384_ = l_Lean_Meta_Sym_mkNotS(v___y_1380_, v___y_1378_, v___y_1379_, v___y_1376_, v___y_1369_, v___y_1374_, v___y_1371_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1386_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
lean_inc_ref(v___y_1375_);
v___x_1386_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v___y_1370_, v___y_1377_, v___y_1375_, v_a_1385_, v___y_1378_, v___y_1379_, v___y_1376_, v___y_1369_, v___y_1374_, v___y_1371_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1388_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_a_1387_);
lean_dec_ref_known(v___x_1386_, 1);
lean_inc_ref(v___y_1375_);
v___x_1388_ = l_Lean_Meta_Sym_getLevel___redArg(v___y_1375_, v___y_1379_, v___y_1376_, v___y_1369_, v___y_1374_, v___y_1371_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1390_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc_n(v_a_1389_, 2);
lean_dec_ref_known(v___x_1388_, 1);
lean_inc_ref(v___y_1375_);
v___x_1390_ = l_Lean_Meta_Sym_mkExistsS(v_a_1389_, v___y_1375_, v_a_1387_, v___y_1378_, v___y_1379_, v___y_1376_, v___y_1369_, v___y_1374_, v___y_1371_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1404_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1393_ = v___x_1390_;
v_isShared_1394_ = v_isSharedCheck_1404_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1404_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1395_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__1));
v___x_1396_ = lean_box(0);
v___x_1397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1397_, 0, v_a_1389_);
lean_ctor_set(v___x_1397_, 1, v___x_1396_);
v___x_1398_ = l_Lean_mkConst(v___x_1395_, v___x_1397_);
v___x_1399_ = l_Lean_mkAppB(v___x_1398_, v___y_1375_, v___x_1383_);
v___x_1400_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1400_, 0, v_a_1391_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*2, v___y_1382_);
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*2 + 1, v___y_1382_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1400_);
v___x_1402_ = v___x_1393_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec(v_a_1389_);
lean_dec_ref(v___x_1383_);
lean_dec_ref(v___y_1375_);
v_a_1405_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1390_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1390_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec(v_a_1387_);
lean_dec_ref(v___x_1383_);
lean_dec_ref(v___y_1375_);
v_a_1413_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___x_1388_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___x_1388_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
else
{
lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1428_; 
lean_dec_ref(v___x_1383_);
lean_dec_ref(v___y_1375_);
v_a_1421_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1423_ = v___x_1386_;
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1386_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1428_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1426_; 
if (v_isShared_1424_ == 0)
{
v___x_1426_ = v___x_1423_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec_ref(v___x_1383_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1370_);
v_a_1429_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1384_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1384_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
v___jp_1437_:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
return v___x_1439_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_pushNot___boxed(lean_object* v_e_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_Meta_Grind_NormSym_pushNot(v_e_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_);
lean_dec(v_a_1908_);
lean_dec_ref(v_a_1907_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
lean_dec(v_a_1900_);
lean_dec_ref(v_e_1899_);
return v_res_1910_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1916_ = lean_box(0);
v___x_1917_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__1));
v___x_1918_ = l_Lean_mkConst(v___x_1917_, v___x_1916_);
return v___x_1918_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = lean_box(0);
v___x_1925_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__4));
v___x_1926_ = l_Lean_mkConst(v___x_1925_, v___x_1924_);
return v___x_1926_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = lean_box(0);
v___x_1931_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__7));
v___x_1932_ = l_Lean_mkConst(v___x_1931_, v___x_1930_);
return v___x_1932_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1936_ = lean_box(0);
v___x_1937_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__10));
v___x_1938_ = l_Lean_mkConst(v___x_1937_, v___x_1936_);
return v___x_1938_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14(void){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1944_ = lean_box(0);
v___x_1945_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__13));
v___x_1946_ = l_Lean_mkConst(v___x_1945_, v___x_1944_);
return v___x_1946_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1950_ = lean_box(0);
v___x_1951_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__16));
v___x_1952_ = l_Lean_mkConst(v___x_1951_, v___x_1950_);
return v___x_1952_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20(void){
_start:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1956_ = lean_box(0);
v___x_1957_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__19));
v___x_1958_ = l_Lean_mkConst(v___x_1957_, v___x_1956_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg(lean_object* v_e_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1973_ = l_Lean_Expr_cleanupAnnotations(v_e_1959_);
v___x_1974_ = l_Lean_Expr_isApp(v___x_1973_);
if (v___x_1974_ == 0)
{
lean_dec_ref(v___x_1973_);
goto v___jp_1970_;
}
else
{
lean_object* v___x_1975_; uint8_t v___x_1976_; 
v___x_1975_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1973_);
v___x_1976_ = l_Lean_Expr_isApp(v___x_1975_);
if (v___x_1976_ == 0)
{
lean_dec_ref(v___x_1975_);
lean_dec_ref(v___x_1973_);
goto v___jp_1970_;
}
else
{
lean_object* v___x_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v___x_1977_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1975_);
v___x_1978_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__12));
v___x_1979_ = l_Lean_Expr_isConstOf(v___x_1977_, v___x_1978_);
lean_dec_ref(v___x_1977_);
if (v___x_1979_ == 0)
{
lean_dec_ref(v___x_1975_);
lean_dec_ref(v___x_1973_);
goto v___jp_1970_;
}
else
{
lean_object* v_arg_1980_; lean_object* v_arg_1981_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___x_2099_; 
v_arg_1980_ = lean_ctor_get(v___x_1973_, 1);
lean_inc_ref(v_arg_1980_);
lean_dec_ref(v___x_1973_);
v_arg_1981_ = lean_ctor_get(v___x_1975_, 1);
lean_inc_ref_n(v_arg_1981_, 2);
lean_dec_ref(v___x_1975_);
v___x_2099_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1981_, v_a_1963_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2159_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2102_ = v___x_2099_;
v_isShared_2103_ = v_isSharedCheck_2159_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2099_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2159_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2104_ = l_Lean_Expr_cleanupAnnotations(v_a_2100_);
lean_dec(v_a_2100_);
v___x_2105_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_2106_ = l_Lean_Expr_isConstOf(v___x_2104_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; uint8_t v___x_2108_; 
v___x_2107_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__10));
v___x_2108_ = l_Lean_Expr_isConstOf(v___x_2104_, v___x_2107_);
if (v___x_2108_ == 0)
{
uint8_t v___x_2109_; 
lean_del_object(v___x_2102_);
v___x_2109_ = l_Lean_Expr_isApp(v___x_2104_);
if (v___x_2109_ == 0)
{
lean_dec_ref(v___x_2104_);
v___y_1983_ = v_a_1960_;
v___y_1984_ = v_a_1961_;
v___y_1985_ = v_a_1962_;
v___y_1986_ = v_a_1963_;
v___y_1987_ = v_a_1964_;
v___y_1988_ = v_a_1965_;
goto v___jp_1982_;
}
else
{
lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2110_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2104_);
v___x_2111_ = l_Lean_Expr_isApp(v___x_2110_);
if (v___x_2111_ == 0)
{
lean_dec_ref(v___x_2110_);
lean_dec_ref(v___x_2104_);
v___y_1983_ = v_a_1960_;
v___y_1984_ = v_a_1961_;
v___y_1985_ = v_a_1962_;
v___y_1986_ = v_a_1963_;
v___y_1987_ = v_a_1964_;
v___y_1988_ = v_a_1965_;
goto v___jp_1982_;
}
else
{
lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2112_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2110_);
v___x_2113_ = l_Lean_Expr_isConstOf(v___x_2112_, v___x_1978_);
lean_dec_ref(v___x_2112_);
if (v___x_2113_ == 0)
{
lean_dec_ref(v___x_2110_);
lean_dec_ref(v___x_2104_);
v___y_1983_ = v_a_1960_;
v___y_1984_ = v_a_1961_;
v___y_1985_ = v_a_1962_;
v___y_1986_ = v_a_1963_;
v___y_1987_ = v_a_1964_;
v___y_1988_ = v_a_1965_;
goto v___jp_1982_;
}
else
{
lean_object* v_arg_2114_; lean_object* v_arg_2115_; lean_object* v___x_2116_; 
lean_dec_ref(v_arg_1981_);
v_arg_2114_ = lean_ctor_get(v___x_2104_, 1);
lean_inc_ref_n(v_arg_2114_, 2);
lean_dec_ref(v___x_2104_);
v_arg_2115_ = lean_ctor_get(v___x_2110_, 1);
lean_inc_ref(v_arg_2115_);
lean_dec_ref(v___x_2110_);
lean_inc_ref(v_arg_1980_);
v___x_2116_ = l_Lean_Meta_Sym_mkOrS(v_arg_2114_, v_arg_1980_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2118_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
lean_inc_ref(v_arg_2115_);
v___x_2118_ = l_Lean_Meta_Sym_mkOrS(v_arg_2115_, v_a_2117_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2129_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2129_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2129_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2127_; 
v___x_2123_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14);
v___x_2124_ = l_Lean_mkApp3(v___x_2123_, v_arg_2115_, v_arg_2114_, v_arg_1980_);
v___x_2125_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2125_, 0, v_a_2119_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
lean_ctor_set_uint8(v___x_2125_, sizeof(void*)*2, v___x_2108_);
lean_ctor_set_uint8(v___x_2125_, sizeof(void*)*2 + 1, v___x_2108_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2125_);
v___x_2127_ = v___x_2121_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec_ref(v_arg_2115_);
lean_dec_ref(v_arg_2114_);
lean_dec_ref(v_arg_1980_);
v_a_2130_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2118_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2118_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec_ref(v_arg_2115_);
lean_dec_ref(v_arg_2114_);
lean_dec_ref(v_arg_1980_);
v_a_2138_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2116_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2116_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2150_; 
lean_dec_ref(v___x_2104_);
v___x_2146_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17);
v___x_2147_ = l_Lean_Expr_app___override(v___x_2146_, v_arg_1980_);
v___x_2148_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2148_, 0, v_arg_1981_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
lean_ctor_set_uint8(v___x_2148_, sizeof(void*)*2, v___x_2106_);
lean_ctor_set_uint8(v___x_2148_, sizeof(void*)*2 + 1, v___x_2106_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2148_);
v___x_2150_ = v___x_2102_;
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
lean_object* v___x_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2157_; 
lean_dec_ref(v___x_2104_);
lean_dec_ref(v_arg_1981_);
v___x_2152_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20);
lean_inc_ref(v_arg_1980_);
v___x_2153_ = l_Lean_Expr_app___override(v___x_2152_, v_arg_1980_);
v___x_2154_ = 0;
v___x_2155_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2155_, 0, v_arg_1980_);
lean_ctor_set(v___x_2155_, 1, v___x_2153_);
lean_ctor_set_uint8(v___x_2155_, sizeof(void*)*2, v___x_2154_);
lean_ctor_set_uint8(v___x_2155_, sizeof(void*)*2 + 1, v___x_2154_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2155_);
v___x_2157_ = v___x_2102_;
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
else
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2167_; 
lean_dec_ref(v_arg_1981_);
lean_dec_ref(v_arg_1980_);
v_a_2160_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2167_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2162_ = v___x_2099_;
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2099_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2167_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2165_; 
if (v_isShared_2163_ == 0)
{
v___x_2165_ = v___x_2162_;
goto v_reusejp_2164_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v_a_2160_);
v___x_2165_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2164_;
}
v_reusejp_2164_:
{
return v___x_2165_;
}
}
}
v___jp_1982_:
{
lean_object* v___x_1989_; 
lean_inc_ref(v_arg_1980_);
v___x_1989_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1980_, v___y_1986_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2090_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_1992_ = v___x_1989_;
v_isShared_1993_ = v_isSharedCheck_2090_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_a_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2090_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1994_ = l_Lean_Expr_cleanupAnnotations(v_a_1990_);
lean_dec(v_a_1990_);
v___x_1995_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_1996_ = l_Lean_Expr_isConstOf(v___x_1994_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; uint8_t v___x_1998_; 
v___x_1997_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__10));
v___x_1998_ = l_Lean_Expr_isConstOf(v___x_1994_, v___x_1997_);
if (v___x_1998_ == 0)
{
uint8_t v___x_1999_; 
lean_dec_ref(v_arg_1980_);
v___x_1999_ = l_Lean_Expr_isApp(v___x_1994_);
if (v___x_1999_ == 0)
{
lean_dec_ref(v___x_1994_);
lean_del_object(v___x_1992_);
lean_dec_ref(v_arg_1981_);
goto v___jp_1967_;
}
else
{
lean_object* v___x_2000_; uint8_t v___x_2001_; 
v___x_2000_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1994_);
v___x_2001_ = l_Lean_Expr_isApp(v___x_2000_);
if (v___x_2001_ == 0)
{
lean_dec_ref(v___x_2000_);
lean_dec_ref(v___x_1994_);
lean_del_object(v___x_1992_);
lean_dec_ref(v_arg_1981_);
goto v___jp_1967_;
}
else
{
lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_2002_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2000_);
v___x_2003_ = l_Lean_Expr_isConstOf(v___x_2002_, v___x_1978_);
lean_dec_ref(v___x_2002_);
if (v___x_2003_ == 0)
{
lean_dec_ref(v___x_2000_);
lean_dec_ref(v___x_1994_);
lean_del_object(v___x_1992_);
lean_dec_ref(v_arg_1981_);
goto v___jp_1967_;
}
else
{
uint8_t v___x_2004_; 
v___x_2004_ = l_Lean_Expr_isForall(v_arg_1981_);
if (v___x_2004_ == 0)
{
lean_object* v_arg_2005_; lean_object* v_arg_2006_; uint8_t v___x_2007_; 
v_arg_2005_ = lean_ctor_get(v___x_1994_, 1);
lean_inc_ref(v_arg_2005_);
lean_dec_ref(v___x_1994_);
v_arg_2006_ = lean_ctor_get(v___x_2000_, 1);
lean_inc_ref(v_arg_2006_);
lean_dec_ref(v___x_2000_);
v___x_2007_ = l_Lean_Expr_isForall(v_arg_2006_);
if (v___x_2007_ == 0)
{
uint8_t v___x_2008_; 
v___x_2008_ = l_Lean_Expr_isForall(v_arg_2005_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2011_; 
lean_dec_ref(v_arg_2006_);
lean_dec_ref(v_arg_2005_);
lean_dec_ref(v_arg_1981_);
v___x_2009_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2009_, 0, v___x_2008_);
lean_ctor_set_uint8(v___x_2009_, 1, v___x_2008_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_2009_);
v___x_2011_ = v___x_1992_;
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
else
{
lean_object* v___x_2013_; 
lean_del_object(v___x_1992_);
lean_inc_ref(v_arg_1981_);
lean_inc_ref(v_arg_2006_);
v___x_2013_ = l_Lean_Meta_Sym_mkOrS(v_arg_2006_, v_arg_1981_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2015_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
lean_inc_ref(v_arg_2005_);
v___x_2015_ = l_Lean_Meta_Sym_mkOrS(v_arg_2005_, v_a_2014_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2026_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2026_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2026_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2020_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2);
v___x_2021_ = l_Lean_mkApp3(v___x_2020_, v_arg_1981_, v_arg_2006_, v_arg_2005_);
v___x_2022_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2022_, 0, v_a_2016_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*2, v___x_2007_);
lean_ctor_set_uint8(v___x_2022_, sizeof(void*)*2 + 1, v___x_2007_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2022_);
v___x_2024_ = v___x_2018_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_dec_ref(v_arg_2006_);
lean_dec_ref(v_arg_2005_);
lean_dec_ref(v_arg_1981_);
v_a_2027_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2015_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2015_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec_ref(v_arg_2006_);
lean_dec_ref(v_arg_2005_);
lean_dec_ref(v_arg_1981_);
v_a_2035_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2013_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2013_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
else
{
lean_object* v___x_2043_; 
lean_del_object(v___x_1992_);
lean_inc_ref(v_arg_2005_);
lean_inc_ref(v_arg_1981_);
v___x_2043_ = l_Lean_Meta_Sym_mkOrS(v_arg_1981_, v_arg_2005_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2045_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref_known(v___x_2043_, 1);
lean_inc_ref(v_arg_2006_);
v___x_2045_ = l_Lean_Meta_Sym_mkOrS(v_arg_2006_, v_a_2044_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2056_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2048_ = v___x_2045_;
v_isShared_2049_ = v_isSharedCheck_2056_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2045_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2056_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2050_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5);
v___x_2051_ = l_Lean_mkApp3(v___x_2050_, v_arg_1981_, v_arg_2006_, v_arg_2005_);
v___x_2052_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2052_, 0, v_a_2046_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
lean_ctor_set_uint8(v___x_2052_, sizeof(void*)*2, v___x_2004_);
lean_ctor_set_uint8(v___x_2052_, sizeof(void*)*2 + 1, v___x_2004_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v___x_2052_);
v___x_2054_ = v___x_2048_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec_ref(v_arg_2006_);
lean_dec_ref(v_arg_2005_);
lean_dec_ref(v_arg_1981_);
v_a_2057_ = lean_ctor_get(v___x_2045_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2045_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2045_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2045_);
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
lean_dec_ref(v_arg_2006_);
lean_dec_ref(v_arg_2005_);
lean_dec_ref(v_arg_1981_);
v_a_2065_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2043_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2043_);
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
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2075_; 
lean_dec_ref(v___x_2000_);
lean_dec_ref(v___x_1994_);
lean_dec_ref(v_arg_1981_);
v___x_2073_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2073_, 0, v___x_1998_);
lean_ctor_set_uint8(v___x_2073_, 1, v___x_1998_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_2073_);
v___x_2075_ = v___x_1992_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2073_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
}
}
else
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2081_; 
lean_dec_ref(v___x_1994_);
v___x_2077_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8);
v___x_2078_ = l_Lean_Expr_app___override(v___x_2077_, v_arg_1981_);
v___x_2079_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2079_, 0, v_arg_1980_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*2, v___x_1996_);
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*2 + 1, v___x_1996_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_2079_);
v___x_2081_ = v___x_1992_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2088_; 
lean_dec_ref(v___x_1994_);
lean_dec_ref(v_arg_1980_);
v___x_2083_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11);
lean_inc_ref(v_arg_1981_);
v___x_2084_ = l_Lean_Expr_app___override(v___x_2083_, v_arg_1981_);
v___x_2085_ = 0;
v___x_2086_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2086_, 0, v_arg_1981_);
lean_ctor_set(v___x_2086_, 1, v___x_2084_);
lean_ctor_set_uint8(v___x_2086_, sizeof(void*)*2, v___x_2085_);
lean_ctor_set_uint8(v___x_2086_, sizeof(void*)*2 + 1, v___x_2085_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 0, v___x_2086_);
v___x_2088_ = v___x_1992_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec_ref(v_arg_1981_);
lean_dec_ref(v_arg_1980_);
v_a_2091_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_1989_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_1989_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
}
}
v___jp_1967_:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
return v___x_1969_;
}
v___jp_1970_:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1971_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1971_);
return v___x_1972_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___boxed(lean_object* v_e_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Lean_Meta_Grind_NormSym_simpOr___redArg(v_e_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
lean_dec(v_a_2174_);
lean_dec_ref(v_a_2173_);
lean_dec(v_a_2172_);
lean_dec_ref(v_a_2171_);
lean_dec(v_a_2170_);
lean_dec_ref(v_a_2169_);
lean_dec_ref(v_e_2168_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr(lean_object* v_e_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_Meta_Grind_NormSym_simpOr___redArg(v_e_2177_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr___boxed(lean_object* v_e_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_Meta_Grind_NormSym_simpOr(v_e_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
lean_dec(v_a_2190_);
lean_dec_ref(v_e_2189_);
return v_res_2200_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2201_ = lean_box(0);
v___x_2202_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_2203_ = l_Lean_mkConst(v___x_2202_, v___x_2201_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0(uint8_t v___x_2204_, uint8_t v___x_2205_, lean_object* v_h_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v___y_2218_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0, &l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0);
lean_inc_ref(v_h_2206_);
v___x_2228_ = l_Lean_Meta_mkNoConfusion(v___x_2227_, v_h_2206_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; uint8_t v___x_2233_; lean_object* v___x_2234_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2229_);
lean_dec_ref_known(v___x_2228_, 1);
v___x_2230_ = lean_unsigned_to_nat(1u);
v___x_2231_ = lean_mk_empty_array_with_capacity(v___x_2230_);
v___x_2232_ = lean_array_push(v___x_2231_, v_h_2206_);
v___x_2233_ = 1;
v___x_2234_ = l_Lean_Meta_mkLambdaFVars(v___x_2232_, v_a_2229_, v___x_2204_, v___x_2205_, v___x_2204_, v___x_2205_, v___x_2233_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
lean_dec_ref(v___x_2232_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v___x_2236_; uint8_t v_transparency_2237_; uint8_t v___x_2238_; uint8_t v___x_2239_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2234_, 1);
v___x_2236_ = l_Lean_Meta_Context_config(v___y_2212_);
v_transparency_2237_ = lean_ctor_get_uint8(v___x_2236_, 9);
lean_dec_ref(v___x_2236_);
v___x_2238_ = 1;
v___x_2239_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2237_, v___x_2238_);
if (v___x_2239_ == 0)
{
lean_object* v_keyedConfig_2240_; uint8_t v_trackZetaDelta_2241_; lean_object* v_zetaDeltaSet_2242_; lean_object* v_lctx_2243_; lean_object* v_localInstances_2244_; lean_object* v_defEqCtx_x3f_2245_; lean_object* v_synthPendingDepth_2246_; lean_object* v_customCanUnfoldPredicate_x3f_2247_; uint8_t v_univApprox_2248_; uint8_t v_inTypeClassResolution_2249_; uint8_t v_cacheInferType_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v_keyedConfig_2240_ = lean_ctor_get(v___y_2212_, 0);
v_trackZetaDelta_2241_ = lean_ctor_get_uint8(v___y_2212_, sizeof(void*)*7);
v_zetaDeltaSet_2242_ = lean_ctor_get(v___y_2212_, 1);
v_lctx_2243_ = lean_ctor_get(v___y_2212_, 2);
v_localInstances_2244_ = lean_ctor_get(v___y_2212_, 3);
v_defEqCtx_x3f_2245_ = lean_ctor_get(v___y_2212_, 4);
v_synthPendingDepth_2246_ = lean_ctor_get(v___y_2212_, 5);
v_customCanUnfoldPredicate_x3f_2247_ = lean_ctor_get(v___y_2212_, 6);
v_univApprox_2248_ = lean_ctor_get_uint8(v___y_2212_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2249_ = lean_ctor_get_uint8(v___y_2212_, sizeof(void*)*7 + 2);
v_cacheInferType_2250_ = lean_ctor_get_uint8(v___y_2212_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2240_);
v___x_2251_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2238_, v_keyedConfig_2240_);
lean_inc(v_customCanUnfoldPredicate_x3f_2247_);
lean_inc(v_synthPendingDepth_2246_);
lean_inc(v_defEqCtx_x3f_2245_);
lean_inc_ref(v_localInstances_2244_);
lean_inc_ref(v_lctx_2243_);
lean_inc(v_zetaDeltaSet_2242_);
v___x_2252_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
lean_ctor_set(v___x_2252_, 1, v_zetaDeltaSet_2242_);
lean_ctor_set(v___x_2252_, 2, v_lctx_2243_);
lean_ctor_set(v___x_2252_, 3, v_localInstances_2244_);
lean_ctor_set(v___x_2252_, 4, v_defEqCtx_x3f_2245_);
lean_ctor_set(v___x_2252_, 5, v_synthPendingDepth_2246_);
lean_ctor_set(v___x_2252_, 6, v_customCanUnfoldPredicate_x3f_2247_);
lean_ctor_set_uint8(v___x_2252_, sizeof(void*)*7, v_trackZetaDelta_2241_);
lean_ctor_set_uint8(v___x_2252_, sizeof(void*)*7 + 1, v_univApprox_2248_);
lean_ctor_set_uint8(v___x_2252_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2249_);
lean_ctor_set_uint8(v___x_2252_, sizeof(void*)*7 + 3, v_cacheInferType_2250_);
v___x_2253_ = l_Lean_Meta_mkEqFalse_x27(v_a_2235_, v___x_2252_, v___y_2213_, v___y_2214_, v___y_2215_);
lean_dec_ref_known(v___x_2252_, 7);
v___y_2218_ = v___x_2253_;
goto v___jp_2217_;
}
else
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Lean_Meta_mkEqFalse_x27(v_a_2235_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
v___y_2218_ = v___x_2254_;
goto v___jp_2217_;
}
}
else
{
return v___x_2234_;
}
}
else
{
lean_dec_ref(v_h_2206_);
return v___x_2228_;
}
v___jp_2217_:
{
if (lean_obj_tag(v___y_2218_) == 0)
{
return v___y_2218_;
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
v_a_2219_ = lean_ctor_get(v___y_2218_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___y_2218_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___y_2218_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___y_2218_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___boxed(lean_object* v___x_2255_, lean_object* v___x_2256_, lean_object* v_h_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
uint8_t v___x_16165__boxed_2268_; uint8_t v___x_16166__boxed_2269_; lean_object* v_res_2270_; 
v___x_16165__boxed_2268_ = lean_unbox(v___x_2255_);
v___x_16166__boxed_2269_ = lean_unbox(v___x_2256_);
v_res_2270_ = l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0(v___x_16165__boxed_2268_, v___x_16166__boxed_2269_, v_h_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0(lean_object* v_k_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v_b_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v___x_2283_; 
lean_inc(v___y_2281_);
lean_inc_ref(v___y_2280_);
lean_inc(v___y_2279_);
lean_inc_ref(v___y_2278_);
lean_inc(v___y_2276_);
lean_inc_ref(v___y_2275_);
lean_inc(v___y_2274_);
lean_inc_ref(v___y_2273_);
lean_inc(v___y_2272_);
v___x_2283_ = lean_apply_11(v_k_2271_, v_b_2277_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, lean_box(0));
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v_b_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0(v_k_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v_b_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(lean_object* v_name_2297_, uint8_t v_bi_2298_, lean_object* v_type_2299_, lean_object* v_k_2300_, uint8_t v_kind_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v___f_2312_; lean_object* v___x_2313_; 
lean_inc(v___y_2306_);
lean_inc_ref(v___y_2305_);
lean_inc(v___y_2304_);
lean_inc_ref(v___y_2303_);
lean_inc(v___y_2302_);
v___f_2312_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_2312_, 0, v_k_2300_);
lean_closure_set(v___f_2312_, 1, v___y_2302_);
lean_closure_set(v___f_2312_, 2, v___y_2303_);
lean_closure_set(v___f_2312_, 3, v___y_2304_);
lean_closure_set(v___f_2312_, 4, v___y_2305_);
lean_closure_set(v___f_2312_, 5, v___y_2306_);
v___x_2313_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2297_, v_bi_2298_, v_type_2299_, v___f_2312_, v_kind_2301_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
if (lean_obj_tag(v___x_2313_) == 0)
{
return v___x_2313_;
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2313_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___boxed(lean_object* v_name_2322_, lean_object* v_bi_2323_, lean_object* v_type_2324_, lean_object* v_k_2325_, lean_object* v_kind_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
uint8_t v_bi_boxed_2337_; uint8_t v_kind_boxed_2338_; lean_object* v_res_2339_; 
v_bi_boxed_2337_ = lean_unbox(v_bi_2323_);
v_kind_boxed_2338_ = lean_unbox(v_kind_2326_);
v_res_2339_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(v_name_2322_, v_bi_boxed_2337_, v_type_2324_, v_k_2325_, v_kind_boxed_2338_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(lean_object* v_name_2340_, lean_object* v_type_2341_, lean_object* v_k_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
uint8_t v___x_2353_; uint8_t v___x_2354_; lean_object* v___x_2355_; 
v___x_2353_ = 0;
v___x_2354_ = 0;
v___x_2355_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(v_name_2340_, v___x_2353_, v_type_2341_, v_k_2342_, v___x_2354_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg___boxed(lean_object* v_name_2356_, lean_object* v_type_2357_, lean_object* v_k_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_name_2356_, v_type_2357_, v_k_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq(lean_object* v_e_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2387_ = l_Lean_Expr_cleanupAnnotations(v_e_2373_);
v___x_2388_ = l_Lean_Expr_isApp(v___x_2387_);
if (v___x_2388_ == 0)
{
lean_dec_ref(v___x_2387_);
lean_dec_ref(v_e_2373_);
goto v___jp_2384_;
}
else
{
lean_object* v___x_2389_; uint8_t v___x_2390_; 
v___x_2389_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2387_);
v___x_2390_ = l_Lean_Expr_isApp(v___x_2389_);
if (v___x_2390_ == 0)
{
lean_dec_ref(v___x_2389_);
lean_dec_ref(v___x_2387_);
lean_dec_ref(v_e_2373_);
goto v___jp_2384_;
}
else
{
lean_object* v___x_2391_; uint8_t v___x_2392_; 
v___x_2391_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2389_);
v___x_2392_ = l_Lean_Expr_isApp(v___x_2391_);
if (v___x_2392_ == 0)
{
lean_dec_ref(v___x_2391_);
lean_dec_ref(v___x_2389_);
lean_dec_ref(v___x_2387_);
lean_dec_ref(v_e_2373_);
goto v___jp_2384_;
}
else
{
lean_object* v___x_2393_; lean_object* v___x_2394_; uint8_t v___x_2395_; 
v___x_2393_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2391_);
lean_dec_ref(v___x_2391_);
v___x_2394_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__1));
v___x_2395_ = l_Lean_Expr_isConstOf(v___x_2393_, v___x_2394_);
lean_dec_ref(v___x_2393_);
if (v___x_2395_ == 0)
{
lean_dec_ref(v___x_2389_);
lean_dec_ref(v___x_2387_);
lean_dec_ref(v_e_2373_);
goto v___jp_2384_;
}
else
{
lean_object* v_arg_2396_; lean_object* v_arg_2397_; lean_object* v___x_2398_; 
v_arg_2396_ = lean_ctor_get(v___x_2387_, 1);
lean_inc_ref(v_arg_2396_);
lean_dec_ref(v___x_2387_);
v_arg_2397_ = lean_ctor_get(v___x_2389_, 1);
lean_inc_ref(v_arg_2397_);
lean_dec_ref(v___x_2389_);
v___x_2398_ = l_Lean_Meta_isConstructorApp_x3f(v_arg_2397_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2468_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2401_ = v___x_2398_;
v_isShared_2402_ = v_isSharedCheck_2468_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2398_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2468_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
if (lean_obj_tag(v_a_2399_) == 1)
{
lean_object* v_val_2403_; lean_object* v___x_2404_; 
lean_del_object(v___x_2401_);
v_val_2403_ = lean_ctor_get(v_a_2399_, 0);
lean_inc(v_val_2403_);
lean_dec_ref_known(v_a_2399_, 1);
v___x_2404_ = l_Lean_Meta_isConstructorApp_x3f(v_arg_2396_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2455_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2407_ = v___x_2404_;
v_isShared_2408_ = v_isSharedCheck_2455_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2404_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2455_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
if (lean_obj_tag(v_a_2405_) == 1)
{
lean_object* v_toConstantVal_2409_; lean_object* v_val_2410_; lean_object* v_toConstantVal_2411_; lean_object* v_name_2412_; lean_object* v_name_2413_; uint8_t v___x_2414_; 
v_toConstantVal_2409_ = lean_ctor_get(v_val_2403_, 0);
lean_inc_ref(v_toConstantVal_2409_);
lean_dec(v_val_2403_);
v_val_2410_ = lean_ctor_get(v_a_2405_, 0);
lean_inc(v_val_2410_);
lean_dec_ref_known(v_a_2405_, 1);
v_toConstantVal_2411_ = lean_ctor_get(v_val_2410_, 0);
lean_inc_ref(v_toConstantVal_2411_);
lean_dec(v_val_2410_);
v_name_2412_ = lean_ctor_get(v_toConstantVal_2409_, 0);
lean_inc(v_name_2412_);
lean_dec_ref(v_toConstantVal_2409_);
v_name_2413_ = lean_ctor_get(v_toConstantVal_2411_, 0);
lean_inc(v_name_2413_);
lean_dec_ref(v_toConstantVal_2411_);
v___x_2414_ = lean_name_eq(v_name_2412_, v_name_2413_);
lean_dec(v_name_2413_);
lean_dec(v_name_2412_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___f_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
lean_del_object(v___x_2407_);
v___x_2415_ = lean_box(v___x_2414_);
v___x_2416_ = lean_box(v___x_2395_);
v___f_2417_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2417_, 0, v___x_2415_);
lean_closure_set(v___f_2417_, 1, v___x_2416_);
v___x_2418_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_reduceCtorEq___closed__1));
v___x_2419_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v___x_2418_, v_e_2373_, v___f_2417_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2421_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2420_);
lean_dec_ref_known(v___x_2419_, 1);
v___x_2421_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2377_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2430_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2424_ = v___x_2421_;
v_isShared_2425_ = v_isSharedCheck_2430_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2421_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2430_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2426_; lean_object* v___x_2428_; 
v___x_2426_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2426_, 0, v_a_2422_);
lean_ctor_set(v___x_2426_, 1, v_a_2420_);
lean_ctor_set_uint8(v___x_2426_, sizeof(void*)*2, v___x_2395_);
lean_ctor_set_uint8(v___x_2426_, sizeof(void*)*2 + 1, v___x_2414_);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 0, v___x_2426_);
v___x_2428_ = v___x_2424_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2426_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_dec(v_a_2420_);
v_a_2431_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2421_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2421_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2446_; 
v_a_2439_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2446_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2446_ == 0)
{
v___x_2441_ = v___x_2419_;
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2419_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2446_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2439_);
v___x_2444_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
return v___x_2444_;
}
}
}
}
else
{
lean_object* v___x_2447_; lean_object* v___x_2449_; 
lean_dec_ref(v_e_2373_);
v___x_2447_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 0, v___x_2447_);
v___x_2449_ = v___x_2407_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
else
{
lean_object* v___x_2451_; lean_object* v___x_2453_; 
lean_dec(v_a_2405_);
lean_dec(v_val_2403_);
lean_dec_ref(v_e_2373_);
v___x_2451_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 0, v___x_2451_);
v___x_2453_ = v___x_2407_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2451_);
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
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec(v_val_2403_);
lean_dec_ref(v_e_2373_);
v_a_2456_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2404_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2404_);
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
else
{
lean_object* v___x_2464_; lean_object* v___x_2466_; 
lean_dec(v_a_2399_);
lean_dec_ref(v_arg_2396_);
lean_dec_ref(v_e_2373_);
v___x_2464_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 0, v___x_2464_);
v___x_2466_ = v___x_2401_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec_ref(v_arg_2396_);
lean_dec_ref(v_e_2373_);
v_a_2469_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2398_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2398_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
}
}
v___jp_2384_:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
return v___x_2386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___boxed(lean_object* v_e_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_Meta_Grind_NormSym_reduceCtorEq(v_e_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_);
lean_dec(v_a_2486_);
lean_dec_ref(v_a_2485_);
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
lean_dec(v_a_2480_);
lean_dec_ref(v_a_2479_);
lean_dec(v_a_2478_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0(lean_object* v_00_u03b1_2489_, lean_object* v_name_2490_, uint8_t v_bi_2491_, lean_object* v_type_2492_, lean_object* v_k_2493_, uint8_t v_kind_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v___x_2505_; 
v___x_2505_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(v_name_2490_, v_bi_2491_, v_type_2492_, v_k_2493_, v_kind_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2506_, lean_object* v_name_2507_, lean_object* v_bi_2508_, lean_object* v_type_2509_, lean_object* v_k_2510_, lean_object* v_kind_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
uint8_t v_bi_boxed_2522_; uint8_t v_kind_boxed_2523_; lean_object* v_res_2524_; 
v_bi_boxed_2522_ = lean_unbox(v_bi_2508_);
v_kind_boxed_2523_ = lean_unbox(v_kind_2511_);
v_res_2524_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0(v_00_u03b1_2506_, v_name_2507_, v_bi_boxed_2522_, v_type_2509_, v_k_2510_, v_kind_boxed_2523_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0(lean_object* v_00_u03b1_2525_, lean_object* v_name_2526_, lean_object* v_type_2527_, lean_object* v_k_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v___x_2539_; 
v___x_2539_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_name_2526_, v_type_2527_, v_k_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___boxed(lean_object* v_00_u03b1_2540_, lean_object* v_name_2541_, lean_object* v_type_2542_, lean_object* v_k_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0(v_00_u03b1_2540_, v_name_2541_, v_type_2542_, v_k_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
return v_res_2554_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot(lean_object* v_e_2555_){
_start:
{
uint8_t v___x_2556_; 
v___x_2556_ = l_Lean_Expr_isForall(v_e_2555_);
if (v___x_2556_ == 0)
{
lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; 
v___x_2557_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__3));
v___x_2558_ = lean_unsigned_to_nat(1u);
v___x_2559_ = l_Lean_Expr_isAppOfArity(v_e_2555_, v___x_2557_, v___x_2558_);
return v___x_2559_;
}
else
{
return v___x_2556_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot___boxed(lean_object* v_e_2560_){
_start:
{
uint8_t v_res_2561_; lean_object* v_r_2562_; 
v_res_2561_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot(v_e_2560_);
lean_dec_ref(v_e_2560_);
v_r_2562_ = lean_box(v_res_2561_);
return v_r_2562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrNot_x3f___redArg(lean_object* v_e_2563_, lean_object* v_a_2564_){
_start:
{
if (lean_obj_tag(v_e_2563_) == 7)
{
lean_object* v_binderName_2566_; lean_object* v_binderType_2567_; lean_object* v_body_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v_binderName_2566_ = lean_ctor_get(v_e_2563_, 0);
v_binderType_2567_ = lean_ctor_get(v_e_2563_, 1);
v_body_2568_ = lean_ctor_get(v_e_2563_, 2);
lean_inc_ref(v_body_2568_);
lean_inc_ref(v_binderType_2567_);
v___x_2569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2569_, 0, v_binderType_2567_);
lean_ctor_set(v___x_2569_, 1, v_body_2568_);
lean_inc(v_binderName_2566_);
v___x_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2570_, 0, v_binderName_2566_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
v___x_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
v___x_2572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
return v___x_2572_;
}
else
{
lean_object* v___x_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v___x_2573_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__3));
v___x_2574_ = lean_unsigned_to_nat(1u);
v___x_2575_ = l_Lean_Expr_isAppOfArity(v_e_2563_, v___x_2573_, v___x_2574_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = lean_box(0);
v___x_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
return v___x_2577_;
}
else
{
lean_object* v___x_2578_; 
v___x_2578_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2564_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2591_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2581_ = v___x_2578_;
v_isShared_2582_ = v_isSharedCheck_2591_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2591_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2589_; 
v___x_2583_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__34));
v___x_2584_ = l_Lean_Expr_appArg_x21(v_e_2563_);
v___x_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2584_);
lean_ctor_set(v___x_2585_, 1, v_a_2579_);
v___x_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2583_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
v___x_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v___x_2587_);
v___x_2589_ = v___x_2581_;
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
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
v_a_2592_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2578_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2578_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrNot_x3f___redArg___boxed(lean_object* v_e_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrNot_x3f___redArg(v_e_2600_, v_a_2601_);
lean_dec_ref(v_a_2601_);
lean_dec_ref(v_e_2600_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrNot_x3f(lean_object* v_e_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrNot_x3f___redArg(v_e_2604_, v_a_2605_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrNot_x3f___boxed(lean_object* v_e_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrNot_x3f(v_e_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_, v_a_2619_);
lean_dec(v_a_2619_);
lean_dec_ref(v_a_2618_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
lean_dec_ref(v_e_2613_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0(lean_object* v_fst_2622_, lean_object* v_a_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = lean_expr_instantiate1(v_fst_2622_, v_a_2623_);
v___x_2635_ = l_Lean_Meta_getLevel(v___x_2634_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0___boxed(lean_object* v_fst_2636_, lean_object* v_a_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0(v_fst_2636_, v_a_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v_a_2637_);
lean_dec_ref(v_fst_2636_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f(lean_object* v_e_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_){
_start:
{
if (lean_obj_tag(v_e_2659_) == 7)
{
lean_object* v_binderName_2673_; lean_object* v_binderType_2674_; lean_object* v_body_2675_; uint8_t v_binderInfo_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v_binderName_2673_ = lean_ctor_get(v_e_2659_, 0);
lean_inc(v_binderName_2673_);
v_binderType_2674_ = lean_ctor_get(v_e_2659_, 1);
lean_inc_ref(v_binderType_2674_);
v_body_2675_ = lean_ctor_get(v_e_2659_, 2);
lean_inc_ref(v_body_2675_);
v_binderInfo_2676_ = lean_ctor_get_uint8(v_e_2659_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2659_, 3);
v___x_2677_ = l_Lean_Expr_cleanupAnnotations(v_body_2675_);
lean_dec_ref(v_body_2675_);
v___x_2678_ = l_Lean_Expr_isApp(v___x_2677_);
if (v___x_2678_ == 0)
{
lean_dec_ref(v___x_2677_);
lean_dec_ref(v_binderType_2674_);
lean_dec(v_binderName_2673_);
goto v___jp_2670_;
}
else
{
lean_object* v___x_2679_; uint8_t v___x_2680_; 
v___x_2679_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2677_);
v___x_2680_ = l_Lean_Expr_isApp(v___x_2679_);
if (v___x_2680_ == 0)
{
lean_dec_ref(v___x_2679_);
lean_dec_ref(v___x_2677_);
lean_dec_ref(v_binderType_2674_);
lean_dec(v_binderName_2673_);
goto v___jp_2670_;
}
else
{
lean_object* v___x_2681_; lean_object* v___x_2682_; uint8_t v___x_2683_; 
v___x_2681_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2679_);
v___x_2682_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__12));
v___x_2683_ = l_Lean_Expr_isConstOf(v___x_2681_, v___x_2682_);
lean_dec_ref(v___x_2681_);
if (v___x_2683_ == 0)
{
lean_dec_ref(v___x_2679_);
lean_dec_ref(v___x_2677_);
lean_dec_ref(v_binderType_2674_);
lean_dec(v_binderName_2673_);
goto v___jp_2670_;
}
else
{
lean_object* v_arg_2684_; lean_object* v_arg_2685_; lean_object* v___x_2686_; 
v_arg_2684_ = lean_ctor_get(v___x_2677_, 1);
lean_inc_ref(v_arg_2684_);
lean_dec_ref(v___x_2677_);
v_arg_2685_ = lean_ctor_get(v___x_2679_, 1);
lean_inc_ref(v_arg_2685_);
lean_dec_ref(v___x_2679_);
v___x_2686_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrNot_x3f___redArg(v_arg_2685_, v_a_2663_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v_a_2687_; 
v_a_2687_ = lean_ctor_get(v___x_2686_, 0);
lean_inc(v_a_2687_);
lean_dec_ref_known(v___x_2686_, 1);
if (lean_obj_tag(v_a_2687_) == 1)
{
lean_object* v_val_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2794_; 
lean_dec_ref(v_arg_2685_);
v_val_2688_ = lean_ctor_get(v_a_2687_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v_a_2687_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2690_ = v_a_2687_;
v_isShared_2691_ = v_isSharedCheck_2794_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_val_2688_);
lean_dec(v_a_2687_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2794_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v_snd_2692_; lean_object* v_fst_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2793_; 
v_snd_2692_ = lean_ctor_get(v_val_2688_, 1);
v_fst_2693_ = lean_ctor_get(v_val_2688_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_val_2688_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2695_ = v_val_2688_;
v_isShared_2696_ = v_isSharedCheck_2793_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_snd_2692_);
lean_inc(v_fst_2693_);
lean_dec(v_val_2688_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2793_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v_fst_2697_; lean_object* v_snd_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2792_; 
v_fst_2697_ = lean_ctor_get(v_snd_2692_, 0);
v_snd_2698_ = lean_ctor_get(v_snd_2692_, 1);
v_isSharedCheck_2792_ = !lean_is_exclusive(v_snd_2692_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2700_ = v_snd_2692_;
v_isShared_2701_ = v_isSharedCheck_2792_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_snd_2698_);
lean_inc(v_fst_2697_);
lean_dec(v_snd_2692_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2792_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___f_2702_; lean_object* v___x_2703_; uint8_t v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
lean_inc_n(v_fst_2697_, 3);
v___f_2702_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2702_, 0, v_fst_2697_);
lean_inc_ref(v_arg_2684_);
lean_inc_ref_n(v_binderType_2674_, 4);
lean_inc_n(v_binderName_2673_, 3);
v___x_2703_ = l_Lean_mkLambda(v_binderName_2673_, v_binderInfo_2676_, v_binderType_2674_, v_arg_2684_);
v___x_2704_ = 0;
lean_inc(v_snd_2698_);
lean_inc(v_fst_2693_);
v___x_2705_ = l_Lean_mkLambda(v_fst_2693_, v___x_2704_, v_fst_2697_, v_snd_2698_);
v___x_2706_ = l_Lean_mkLambda(v_binderName_2673_, v_binderInfo_2676_, v_binderType_2674_, v___x_2705_);
v___x_2707_ = l_Lean_mkLambda(v_binderName_2673_, v_binderInfo_2676_, v_binderType_2674_, v_fst_2697_);
v___x_2708_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2674_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_a_2709_; lean_object* v___x_2710_; 
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
lean_inc(v_a_2709_);
lean_dec_ref_known(v___x_2708_, 1);
lean_inc_ref(v_binderType_2674_);
lean_inc(v_binderName_2673_);
v___x_2710_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_binderName_2673_, v_binderType_2674_, v___f_2702_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2710_, 1);
v___x_2712_ = lean_unsigned_to_nat(0u);
v___x_2713_ = lean_unsigned_to_nat(1u);
v___x_2714_ = lean_expr_lift_loose_bvars(v_arg_2684_, v___x_2712_, v___x_2713_);
lean_dec_ref(v_arg_2684_);
v___x_2715_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2714_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2717_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_a_2716_);
lean_dec_ref_known(v___x_2715_, 1);
v___x_2717_ = l_Lean_Meta_Sym_mkOrS(v_snd_2698_, v_a_2716_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; lean_object* v___x_2719_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2718_);
lean_dec_ref_known(v___x_2717_, 1);
v___x_2719_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_fst_2693_, v___x_2704_, v_fst_2697_, v_a_2718_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; lean_object* v___x_2721_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref_known(v___x_2719_, 1);
lean_inc_ref(v_binderType_2674_);
v___x_2721_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_binderName_2673_, v_binderInfo_2676_, v_binderType_2674_, v_a_2720_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2743_; 
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2724_ = v___x_2721_;
v_isShared_2725_ = v_isSharedCheck_2743_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2721_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2743_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2729_; 
v___x_2726_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__1));
v___x_2727_ = lean_box(0);
if (v_isShared_2696_ == 0)
{
lean_ctor_set_tag(v___x_2695_, 1);
lean_ctor_set(v___x_2695_, 1, v___x_2727_);
lean_ctor_set(v___x_2695_, 0, v_a_2711_);
v___x_2729_ = v___x_2695_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2711_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v___x_2727_);
v___x_2729_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2734_; 
v___x_2730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2730_, 0, v_a_2709_);
lean_ctor_set(v___x_2730_, 1, v___x_2729_);
v___x_2731_ = l_Lean_mkConst(v___x_2726_, v___x_2730_);
v___x_2732_ = l_Lean_mkApp4(v___x_2731_, v_binderType_2674_, v___x_2707_, v___x_2703_, v___x_2706_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 1, v___x_2732_);
lean_ctor_set(v___x_2700_, 0, v_a_2722_);
v___x_2734_ = v___x_2700_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2722_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v___x_2732_);
v___x_2734_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
lean_object* v___x_2736_; 
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v___x_2734_);
v___x_2736_ = v___x_2690_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2734_);
v___x_2736_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2738_; 
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 0, v___x_2736_);
v___x_2738_ = v___x_2724_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2736_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2751_; 
lean_dec(v_a_2711_);
lean_dec(v_a_2709_);
lean_dec_ref(v___x_2707_);
lean_dec_ref(v___x_2706_);
lean_dec_ref(v___x_2703_);
lean_del_object(v___x_2700_);
lean_del_object(v___x_2695_);
lean_del_object(v___x_2690_);
lean_dec_ref(v_binderType_2674_);
v_a_2744_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2746_ = v___x_2721_;
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2721_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2751_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2749_; 
if (v_isShared_2747_ == 0)
{
v___x_2749_ = v___x_2746_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec(v_a_2711_);
lean_dec(v_a_2709_);
lean_dec_ref(v___x_2707_);
lean_dec_ref(v___x_2706_);
lean_dec_ref(v___x_2703_);
lean_del_object(v___x_2700_);
lean_del_object(v___x_2695_);
lean_del_object(v___x_2690_);
lean_dec_ref(v_binderType_2674_);
lean_dec(v_binderName_2673_);
v_a_2752_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___x_2719_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___x_2719_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_dec(v_a_2711_);
lean_dec(v_a_2709_);
lean_dec_ref(v___x_2707_);
lean_dec_ref(v___x_2706_);
lean_dec_ref(v___x_2703_);
lean_del_object(v___x_2700_);
lean_dec(v_fst_2697_);
lean_del_object(v___x_2695_);
lean_dec(v_fst_2693_);
lean_del_object(v___x_2690_);
lean_dec_ref(v_binderType_2674_);
lean_dec(v_binderName_2673_);
v_a_2760_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2717_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2717_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_dec(v_a_2711_);
lean_dec(v_a_2709_);
lean_dec_ref(v___x_2707_);
lean_dec_ref(v___x_2706_);
lean_dec_ref(v___x_2703_);
lean_del_object(v___x_2700_);
lean_dec(v_snd_2698_);
lean_dec(v_fst_2697_);
lean_del_object(v___x_2695_);
lean_dec(v_fst_2693_);
lean_del_object(v___x_2690_);
lean_dec_ref(v_binderType_2674_);
lean_dec(v_binderName_2673_);
v_a_2768_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2715_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2715_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_dec(v_a_2709_);
lean_dec_ref(v___x_2707_);
lean_dec_ref(v___x_2706_);
lean_dec_ref(v___x_2703_);
lean_del_object(v___x_2700_);
lean_dec(v_snd_2698_);
lean_dec(v_fst_2697_);
lean_del_object(v___x_2695_);
lean_dec(v_fst_2693_);
lean_del_object(v___x_2690_);
lean_dec_ref(v_arg_2684_);
lean_dec_ref(v_binderType_2674_);
lean_dec(v_binderName_2673_);
v_a_2776_ = lean_ctor_get(v___x_2710_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2710_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2710_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2710_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec_ref(v___x_2707_);
lean_dec_ref(v___x_2706_);
lean_dec_ref(v___x_2703_);
lean_dec_ref(v___f_2702_);
lean_del_object(v___x_2700_);
lean_dec(v_snd_2698_);
lean_dec(v_fst_2697_);
lean_del_object(v___x_2695_);
lean_dec(v_fst_2693_);
lean_del_object(v___x_2690_);
lean_dec_ref(v_arg_2684_);
lean_dec_ref(v_binderType_2674_);
lean_dec(v_binderName_2673_);
v_a_2784_ = lean_ctor_get(v___x_2708_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2708_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2708_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2708_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2795_; 
lean_dec(v_a_2687_);
v___x_2795_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrNot_x3f___redArg(v_arg_2684_, v_a_2663_);
lean_dec_ref(v_arg_2684_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2911_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2798_ = v___x_2795_;
v_isShared_2799_ = v_isSharedCheck_2911_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2795_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2911_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
if (lean_obj_tag(v_a_2796_) == 1)
{
lean_object* v_val_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2906_; 
lean_del_object(v___x_2798_);
v_val_2800_ = lean_ctor_get(v_a_2796_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v_a_2796_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2802_ = v_a_2796_;
v_isShared_2803_ = v_isSharedCheck_2906_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_val_2800_);
lean_dec(v_a_2796_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2906_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v_snd_2804_; lean_object* v_fst_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2905_; 
v_snd_2804_ = lean_ctor_get(v_val_2800_, 1);
v_fst_2805_ = lean_ctor_get(v_val_2800_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v_val_2800_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2807_ = v_val_2800_;
v_isShared_2808_ = v_isSharedCheck_2905_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_snd_2804_);
lean_inc(v_fst_2805_);
lean_dec(v_val_2800_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2905_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v_fst_2809_; lean_object* v_snd_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2904_; 
v_fst_2809_ = lean_ctor_get(v_snd_2804_, 0);
v_snd_2810_ = lean_ctor_get(v_snd_2804_, 1);
v_isSharedCheck_2904_ = !lean_is_exclusive(v_snd_2804_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2812_ = v_snd_2804_;
v_isShared_2813_ = v_isSharedCheck_2904_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_snd_2810_);
lean_inc(v_fst_2809_);
lean_dec(v_snd_2804_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2904_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___f_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
lean_inc_n(v_fst_2809_, 3);
v___f_2814_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2814_, 0, v_fst_2809_);
lean_inc_ref(v_arg_2685_);
lean_inc_ref_n(v_binderType_2674_, 4);
lean_inc_n(v_binderName_2673_, 3);
v___x_2815_ = l_Lean_mkLambda(v_binderName_2673_, v_binderInfo_2676_, v_binderType_2674_, v_arg_2685_);
v___x_2816_ = 0;
lean_inc(v_snd_2810_);
lean_inc(v_fst_2805_);
v___x_2817_ = l_Lean_mkLambda(v_fst_2805_, v___x_2816_, v_fst_2809_, v_snd_2810_);
v___x_2818_ = l_Lean_mkLambda(v_binderName_2673_, v_binderInfo_2676_, v_binderType_2674_, v___x_2817_);
v___x_2819_ = l_Lean_mkLambda(v_binderName_2673_, v_binderInfo_2676_, v_binderType_2674_, v_fst_2809_);
v___x_2820_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2674_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2822_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
lean_inc_ref(v_binderType_2674_);
lean_inc(v_binderName_2673_);
v___x_2822_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_binderName_2673_, v_binderType_2674_, v___f_2814_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
lean_dec_ref_known(v___x_2822_, 1);
v___x_2824_ = lean_unsigned_to_nat(0u);
v___x_2825_ = lean_unsigned_to_nat(1u);
v___x_2826_ = lean_expr_lift_loose_bvars(v_arg_2685_, v___x_2824_, v___x_2825_);
lean_dec_ref(v_arg_2685_);
v___x_2827_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2826_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2829_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2827_, 1);
v___x_2829_ = l_Lean_Meta_Sym_mkOrS(v_a_2828_, v_snd_2810_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2831_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2829_, 1);
v___x_2831_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_fst_2805_, v___x_2816_, v_fst_2809_, v_a_2830_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2833_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2831_, 1);
lean_inc_ref(v_binderType_2674_);
v___x_2833_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_binderName_2673_, v_binderInfo_2676_, v_binderType_2674_, v_a_2832_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2855_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2836_ = v___x_2833_;
v_isShared_2837_ = v_isSharedCheck_2855_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2833_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2855_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2841_; 
v___x_2838_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__3));
v___x_2839_ = lean_box(0);
if (v_isShared_2808_ == 0)
{
lean_ctor_set_tag(v___x_2807_, 1);
lean_ctor_set(v___x_2807_, 1, v___x_2839_);
lean_ctor_set(v___x_2807_, 0, v_a_2823_);
v___x_2841_ = v___x_2807_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2823_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v___x_2839_);
v___x_2841_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2846_; 
v___x_2842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2842_, 0, v_a_2821_);
lean_ctor_set(v___x_2842_, 1, v___x_2841_);
v___x_2843_ = l_Lean_mkConst(v___x_2838_, v___x_2842_);
v___x_2844_ = l_Lean_mkApp4(v___x_2843_, v_binderType_2674_, v___x_2819_, v___x_2815_, v___x_2818_);
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 1, v___x_2844_);
lean_ctor_set(v___x_2812_, 0, v_a_2834_);
v___x_2846_ = v___x_2812_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2834_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v___x_2844_);
v___x_2846_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
lean_object* v___x_2848_; 
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v___x_2846_);
v___x_2848_ = v___x_2802_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2846_);
v___x_2848_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
lean_object* v___x_2850_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 0, v___x_2848_);
v___x_2850_ = v___x_2836_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2848_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
}
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_dec(v_a_2823_);
lean_dec(v_a_2821_);
lean_dec_ref(v___x_2819_);
lean_dec_ref(v___x_2818_);
lean_dec_ref(v___x_2815_);
lean_del_object(v___x_2812_);
lean_del_object(v___x_2807_);
lean_del_object(v___x_2802_);
lean_dec_ref(v_binderType_2674_);
v_a_2856_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2833_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2833_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec(v_a_2823_);
lean_dec(v_a_2821_);
lean_dec_ref(v___x_2819_);
lean_dec_ref(v___x_2818_);
lean_dec_ref(v___x_2815_);
lean_del_object(v___x_2812_);
lean_del_object(v___x_2807_);
lean_del_object(v___x_2802_);
lean_dec_ref(v_binderType_2674_);
lean_dec(v_binderName_2673_);
v_a_2864_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2831_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2831_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
lean_dec(v_a_2823_);
lean_dec(v_a_2821_);
lean_dec_ref(v___x_2819_);
lean_dec_ref(v___x_2818_);
lean_dec_ref(v___x_2815_);
lean_del_object(v___x_2812_);
lean_dec(v_fst_2809_);
lean_del_object(v___x_2807_);
lean_dec(v_fst_2805_);
lean_del_object(v___x_2802_);
lean_dec_ref(v_binderType_2674_);
lean_dec(v_binderName_2673_);
v_a_2872_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2829_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2829_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec(v_a_2823_);
lean_dec(v_a_2821_);
lean_dec_ref(v___x_2819_);
lean_dec_ref(v___x_2818_);
lean_dec_ref(v___x_2815_);
lean_del_object(v___x_2812_);
lean_dec(v_snd_2810_);
lean_dec(v_fst_2809_);
lean_del_object(v___x_2807_);
lean_dec(v_fst_2805_);
lean_del_object(v___x_2802_);
lean_dec_ref(v_binderType_2674_);
lean_dec(v_binderName_2673_);
v_a_2880_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2827_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2827_);
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
lean_dec(v_a_2821_);
lean_dec_ref(v___x_2819_);
lean_dec_ref(v___x_2818_);
lean_dec_ref(v___x_2815_);
lean_del_object(v___x_2812_);
lean_dec(v_snd_2810_);
lean_dec(v_fst_2809_);
lean_del_object(v___x_2807_);
lean_dec(v_fst_2805_);
lean_del_object(v___x_2802_);
lean_dec_ref(v_arg_2685_);
lean_dec_ref(v_binderType_2674_);
lean_dec(v_binderName_2673_);
v_a_2888_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2822_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2822_);
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
lean_dec_ref(v___x_2819_);
lean_dec_ref(v___x_2818_);
lean_dec_ref(v___x_2815_);
lean_dec_ref(v___f_2814_);
lean_del_object(v___x_2812_);
lean_dec(v_snd_2810_);
lean_dec(v_fst_2809_);
lean_del_object(v___x_2807_);
lean_dec(v_fst_2805_);
lean_del_object(v___x_2802_);
lean_dec_ref(v_arg_2685_);
lean_dec_ref(v_binderType_2674_);
lean_dec(v_binderName_2673_);
v_a_2896_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2820_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2820_);
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
}
}
}
else
{
lean_object* v___x_2907_; lean_object* v___x_2909_; 
lean_dec(v_a_2796_);
lean_dec_ref(v_arg_2685_);
lean_dec_ref(v_binderType_2674_);
lean_dec(v_binderName_2673_);
v___x_2907_ = lean_box(0);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2907_);
v___x_2909_ = v___x_2798_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v___x_2907_);
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
lean_dec_ref(v_arg_2685_);
lean_dec_ref(v_binderType_2674_);
lean_dec(v_binderName_2673_);
v_a_2912_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2795_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2795_);
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
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec_ref(v_arg_2685_);
lean_dec_ref(v_arg_2684_);
lean_dec_ref(v_binderType_2674_);
lean_dec(v_binderName_2673_);
v_a_2920_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2686_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2686_);
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
}
}
}
else
{
lean_object* v___x_2928_; lean_object* v___x_2929_; 
lean_dec_ref(v_e_2659_);
v___x_2928_ = lean_box(0);
v___x_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2928_);
return v___x_2929_;
}
v___jp_2670_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = lean_box(0);
v___x_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2671_);
return v___x_2672_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___boxed(lean_object* v_e_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f(v_e_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
lean_dec(v_a_2937_);
lean_dec_ref(v_a_2936_);
lean_dec(v_a_2935_);
lean_dec_ref(v_a_2934_);
lean_dec(v_a_2933_);
lean_dec_ref(v_a_2932_);
lean_dec(v_a_2931_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg(lean_object* v_fvarId_2942_, lean_object* v___y_2943_){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2945_ = l_Lean_Expr_fvar___override(v_fvarId_2942_);
v___x_2946_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2945_, v___y_2943_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg___boxed(lean_object* v_fvarId_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg(v_fvarId_2947_, v___y_2948_);
lean_dec(v___y_2948_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___lam__0(lean_object* v___y_2951_, lean_object* v_k_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v_b_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = l_Lean_Expr_fvarId_x21(v_b_2957_);
v___x_2964_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg(v___x_2963_, v___y_2951_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2966_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2965_);
lean_dec_ref_known(v___x_2964_, 1);
lean_inc(v___y_2961_);
lean_inc_ref(v___y_2960_);
lean_inc(v___y_2959_);
lean_inc_ref(v___y_2958_);
lean_inc(v___y_2951_);
lean_inc_ref(v___y_2956_);
lean_inc(v___y_2955_);
lean_inc_ref(v___y_2954_);
lean_inc(v___y_2953_);
v___x_2966_ = lean_apply_11(v_k_2952_, v_a_2965_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2951_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, lean_box(0));
return v___x_2966_;
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_dec_ref(v_k_2952_);
v_a_2967_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2964_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2964_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v___y_2975_, lean_object* v_k_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v_b_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___lam__0(v___y_2975_, v_k_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v_b_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec_ref(v_b_2981_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec(v___y_2975_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg(lean_object* v_k_2988_, lean_object* v_name_2989_, uint8_t v_bi_2990_, lean_object* v_type_2991_, uint8_t v_kind_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
lean_object* v___f_3003_; lean_object* v___x_3004_; 
lean_inc_ref(v___y_2996_);
lean_inc(v___y_2995_);
lean_inc_ref(v___y_2994_);
lean_inc(v___y_2993_);
lean_inc(v___y_2997_);
v___f_3003_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_3003_, 0, v___y_2997_);
lean_closure_set(v___f_3003_, 1, v_k_2988_);
lean_closure_set(v___f_3003_, 2, v___y_2993_);
lean_closure_set(v___f_3003_, 3, v___y_2994_);
lean_closure_set(v___f_3003_, 4, v___y_2995_);
lean_closure_set(v___f_3003_, 5, v___y_2996_);
v___x_3004_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2989_, v_bi_2990_, v_type_2991_, v___f_3003_, v_kind_2992_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
if (lean_obj_tag(v___x_3004_) == 0)
{
return v___x_3004_;
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_3004_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_3004_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___boxed(lean_object* v_k_3013_, lean_object* v_name_3014_, lean_object* v_bi_3015_, lean_object* v_type_3016_, lean_object* v_kind_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
uint8_t v_bi_boxed_3028_; uint8_t v_kind_boxed_3029_; lean_object* v_res_3030_; 
v_bi_boxed_3028_ = lean_unbox(v_bi_3015_);
v_kind_boxed_3029_ = lean_unbox(v_kind_3017_);
v_res_3030_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg(v_k_3013_, v_name_3014_, v_bi_boxed_3028_, v_type_3016_, v_kind_boxed_3029_, v___y_3018_, v___y_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg(lean_object* v_name_3031_, uint8_t v_bi_3032_, lean_object* v_type_3033_, lean_object* v_k_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
uint8_t v___x_3045_; lean_object* v___x_3046_; 
v___x_3045_ = 0;
v___x_3046_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg(v_k_3034_, v_name_3031_, v_bi_3032_, v_type_3033_, v___x_3045_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg___boxed(lean_object* v_name_3047_, lean_object* v_bi_3048_, lean_object* v_type_3049_, lean_object* v_k_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_){
_start:
{
uint8_t v_bi_boxed_3061_; lean_object* v_res_3062_; 
v_bi_boxed_3061_ = lean_unbox(v_bi_3048_);
v_res_3062_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg(v_name_3047_, v_bi_boxed_3061_, v_type_3049_, v_k_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v___y_3057_);
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec(v___y_3053_);
lean_dec_ref(v___y_3052_);
lean_dec(v___y_3051_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___lam__0___boxed(lean_object* v_xs_3063_, lean_object* v_body_3064_, lean_object* v_x_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___lam__0(v_xs_3063_, v_body_3064_, v_x_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go(lean_object* v_xs_3077_, lean_object* v_e_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_){
_start:
{
if (lean_obj_tag(v_e_3078_) == 7)
{
lean_object* v_binderName_3089_; lean_object* v_binderType_3090_; lean_object* v_body_3091_; uint8_t v_binderInfo_3092_; uint8_t v___x_3093_; 
v_binderName_3089_ = lean_ctor_get(v_e_3078_, 0);
v_binderType_3090_ = lean_ctor_get(v_e_3078_, 1);
v_body_3091_ = lean_ctor_get(v_e_3078_, 2);
v_binderInfo_3092_ = lean_ctor_get_uint8(v_e_3078_, sizeof(void*)*3 + 8);
v___x_3093_ = l_Lean_Expr_isForall(v_body_3091_);
if (v___x_3093_ == 0)
{
lean_object* v___x_3094_; lean_object* v___x_3095_; uint8_t v___x_3096_; 
v___x_3094_ = lean_array_get_size(v_xs_3077_);
v___x_3095_ = lean_unsigned_to_nat(0u);
v___x_3096_ = lean_nat_dec_eq(v___x_3094_, v___x_3095_);
if (v___x_3096_ == 0)
{
uint8_t v___x_3097_; lean_object* v___x_3098_; 
v___x_3097_ = 1;
lean_inc_ref(v_xs_3077_);
v___x_3098_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_3078_, v___x_3095_, v___x_3094_, v_xs_3077_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_object* v_a_3099_; lean_object* v___x_3100_; 
v_a_3099_ = lean_ctor_get(v___x_3098_, 0);
lean_inc_n(v_a_3099_, 2);
lean_dec_ref_known(v___x_3098_, 1);
v___x_3100_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f(v_a_3099_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3185_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3103_ = v___x_3100_;
v_isShared_3104_ = v_isSharedCheck_3185_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3100_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3185_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
if (lean_obj_tag(v_a_3101_) == 1)
{
lean_object* v_val_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3180_; 
lean_del_object(v___x_3103_);
v_val_3105_ = lean_ctor_get(v_a_3101_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v_a_3101_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3107_ = v_a_3101_;
v_isShared_3108_ = v_isSharedCheck_3180_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_val_3105_);
lean_dec(v_a_3101_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3180_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v_fst_3109_; lean_object* v_snd_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3179_; 
v_fst_3109_ = lean_ctor_get(v_val_3105_, 0);
v_snd_3110_ = lean_ctor_get(v_val_3105_, 1);
v_isSharedCheck_3179_ = !lean_is_exclusive(v_val_3105_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3112_ = v_val_3105_;
v_isShared_3113_ = v_isSharedCheck_3179_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_snd_3110_);
lean_inc(v_fst_3109_);
lean_dec(v_val_3105_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3179_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3114_; 
lean_inc_ref(v_xs_3077_);
v___x_3114_ = l_Lean_Meta_Sym_Simp_mkForallCongrFor(v_xs_3077_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; uint8_t v___x_3116_; lean_object* v___x_3117_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3115_);
lean_dec_ref_known(v___x_3114_, 1);
v___x_3116_ = 1;
v___x_3117_ = l_Lean_Meta_mkLambdaFVars(v_xs_3077_, v_a_3099_, v___x_3096_, v___x_3097_, v___x_3096_, v___x_3097_, v___x_3116_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v___x_3119_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3118_);
lean_dec_ref_known(v___x_3117_, 1);
lean_inc(v_fst_3109_);
v___x_3119_ = l_Lean_Meta_mkLambdaFVars(v_xs_3077_, v_fst_3109_, v___x_3096_, v___x_3097_, v___x_3096_, v___x_3097_, v___x_3116_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v___x_3121_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3120_);
lean_dec_ref_known(v___x_3119_, 1);
v___x_3121_ = l_Lean_Meta_mkLambdaFVars(v_xs_3077_, v_snd_3110_, v___x_3096_, v___x_3097_, v___x_3096_, v___x_3097_, v___x_3116_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
lean_inc(v_a_3122_);
lean_dec_ref_known(v___x_3121_, 1);
v___x_3123_ = l_Lean_mkApp3(v_a_3115_, v_a_3118_, v_a_3120_, v_a_3122_);
v___x_3124_ = l_Lean_Meta_Sym_mkForallFVarsS(v_xs_3077_, v_fst_3109_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3138_; 
v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3127_ = v___x_3124_;
v_isShared_3128_ = v_isSharedCheck_3138_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3124_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3138_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 1, v___x_3123_);
lean_ctor_set(v___x_3112_, 0, v_a_3125_);
v___x_3130_ = v___x_3112_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3125_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v___x_3123_);
v___x_3130_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
lean_object* v___x_3132_; 
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 0, v___x_3130_);
v___x_3132_ = v___x_3107_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3130_);
v___x_3132_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
lean_object* v___x_3134_; 
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 0, v___x_3132_);
v___x_3134_ = v___x_3127_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3132_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec_ref(v___x_3123_);
lean_del_object(v___x_3112_);
lean_del_object(v___x_3107_);
v_a_3139_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3124_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3124_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec(v_a_3120_);
lean_dec(v_a_3118_);
lean_dec(v_a_3115_);
lean_del_object(v___x_3112_);
lean_dec(v_fst_3109_);
lean_del_object(v___x_3107_);
lean_dec_ref(v_xs_3077_);
v_a_3147_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3121_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3121_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec(v_a_3118_);
lean_dec(v_a_3115_);
lean_del_object(v___x_3112_);
lean_dec(v_snd_3110_);
lean_dec(v_fst_3109_);
lean_del_object(v___x_3107_);
lean_dec_ref(v_xs_3077_);
v_a_3155_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3119_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3119_);
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
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_dec(v_a_3115_);
lean_del_object(v___x_3112_);
lean_dec(v_snd_3110_);
lean_dec(v_fst_3109_);
lean_del_object(v___x_3107_);
lean_dec_ref(v_xs_3077_);
v_a_3163_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3117_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3117_);
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
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
lean_del_object(v___x_3112_);
lean_dec(v_snd_3110_);
lean_dec(v_fst_3109_);
lean_del_object(v___x_3107_);
lean_dec(v_a_3099_);
lean_dec_ref(v_xs_3077_);
v_a_3171_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3114_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3114_);
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
}
else
{
lean_object* v___x_3181_; lean_object* v___x_3183_; 
lean_dec(v_a_3101_);
lean_dec(v_a_3099_);
lean_dec_ref(v_xs_3077_);
v___x_3181_ = lean_box(0);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 0, v___x_3181_);
v___x_3183_ = v___x_3103_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3181_);
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
lean_dec(v_a_3099_);
lean_dec_ref(v_xs_3077_);
return v___x_3100_;
}
}
else
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3193_; 
lean_dec_ref(v_xs_3077_);
v_a_3186_ = lean_ctor_get(v___x_3098_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3188_ = v___x_3098_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3098_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3191_; 
if (v_isShared_3189_ == 0)
{
v___x_3191_ = v___x_3188_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
else
{
lean_object* v___x_3194_; 
lean_dec_ref(v_xs_3077_);
v___x_3194_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f(v_e_3078_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
return v___x_3194_;
}
}
else
{
lean_object* v___f_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
lean_inc_ref(v_body_3091_);
lean_inc_ref(v_binderType_3090_);
lean_inc(v_binderName_3089_);
lean_dec_ref_known(v_e_3078_, 3);
lean_inc_ref(v_xs_3077_);
v___f_3195_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___lam__0___boxed), 13, 2);
lean_closure_set(v___f_3195_, 0, v_xs_3077_);
lean_closure_set(v___f_3195_, 1, v_body_3091_);
v___x_3196_ = lean_unsigned_to_nat(0u);
v___x_3197_ = lean_array_get_size(v_xs_3077_);
v___x_3198_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_binderType_3090_, v___x_3196_, v___x_3197_, v_xs_3077_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_a_3199_; lean_object* v___x_3200_; 
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
lean_inc(v_a_3199_);
lean_dec_ref_known(v___x_3198_, 1);
v___x_3200_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg(v_binderName_3089_, v_binderInfo_3092_, v_a_3199_, v___f_3195_, v_a_3079_, v_a_3080_, v_a_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_);
return v___x_3200_;
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_dec_ref(v___f_3195_);
lean_dec(v_binderName_3089_);
v_a_3201_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3198_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3198_);
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
lean_object* v___x_3209_; lean_object* v___x_3210_; 
lean_dec_ref(v_e_3078_);
lean_dec_ref(v_xs_3077_);
v___x_3209_ = lean_box(0);
v___x_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
return v___x_3210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___lam__0(lean_object* v_xs_3211_, lean_object* v_body_3212_, lean_object* v_x_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = lean_array_push(v_xs_3211_, v_x_3213_);
v___x_3225_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go(v___x_3224_, v_body_3212_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___boxed(lean_object* v_xs_3226_, lean_object* v_e_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_){
_start:
{
lean_object* v_res_3238_; 
v_res_3238_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go(v_xs_3226_, v_e_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_);
lean_dec(v_a_3236_);
lean_dec_ref(v_a_3235_);
lean_dec(v_a_3234_);
lean_dec_ref(v_a_3233_);
lean_dec(v_a_3232_);
lean_dec_ref(v_a_3231_);
lean_dec(v_a_3230_);
lean_dec_ref(v_a_3229_);
lean_dec(v_a_3228_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0(lean_object* v_fvarId_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg(v_fvarId_3239_, v___y_3241_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___boxed(lean_object* v_fvarId_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0(v_fvarId_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2(lean_object* v_00_u03b1_3257_, lean_object* v_k_3258_, lean_object* v_name_3259_, uint8_t v_bi_3260_, lean_object* v_type_3261_, uint8_t v_kind_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg(v_k_3258_, v_name_3259_, v_bi_3260_, v_type_3261_, v_kind_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3274_, lean_object* v_k_3275_, lean_object* v_name_3276_, lean_object* v_bi_3277_, lean_object* v_type_3278_, lean_object* v_kind_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
uint8_t v_bi_boxed_3290_; uint8_t v_kind_boxed_3291_; lean_object* v_res_3292_; 
v_bi_boxed_3290_ = lean_unbox(v_bi_3277_);
v_kind_boxed_3291_ = lean_unbox(v_kind_3279_);
v_res_3292_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2(v_00_u03b1_3274_, v_k_3275_, v_name_3276_, v_bi_boxed_3290_, v_type_3278_, v_kind_boxed_3291_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0(lean_object* v_00_u03b1_3293_, lean_object* v_name_3294_, uint8_t v_bi_3295_, lean_object* v_type_3296_, lean_object* v_k_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
lean_object* v___x_3308_; 
v___x_3308_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg(v_name_3294_, v_bi_3295_, v_type_3296_, v_k_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___boxed(lean_object* v_00_u03b1_3309_, lean_object* v_name_3310_, lean_object* v_bi_3311_, lean_object* v_type_3312_, lean_object* v_k_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
uint8_t v_bi_boxed_3324_; lean_object* v_res_3325_; 
v_bi_boxed_3324_ = lean_unbox(v_bi_3311_);
v_res_3325_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0(v_00_u03b1_3309_, v_name_3310_, v_bi_boxed_3324_, v_type_3312_, v_k_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f(lean_object* v_e_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_){
_start:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; 
v___x_3345_ = l_Lean_Expr_getForallBody(v_e_3328_);
v___x_3346_ = l_Lean_Expr_cleanupAnnotations(v___x_3345_);
lean_dec_ref(v___x_3345_);
v___x_3347_ = l_Lean_Expr_isApp(v___x_3346_);
if (v___x_3347_ == 0)
{
lean_dec_ref(v___x_3346_);
lean_dec_ref(v_e_3328_);
goto v___jp_3339_;
}
else
{
lean_object* v___x_3348_; uint8_t v___x_3349_; 
v___x_3348_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3346_);
v___x_3349_ = l_Lean_Expr_isApp(v___x_3348_);
if (v___x_3349_ == 0)
{
lean_dec_ref(v___x_3348_);
lean_dec_ref(v___x_3346_);
lean_dec_ref(v_e_3328_);
goto v___jp_3339_;
}
else
{
lean_object* v___x_3350_; lean_object* v___x_3351_; uint8_t v___x_3352_; 
v___x_3350_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3348_);
v___x_3351_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__12));
v___x_3352_ = l_Lean_Expr_isConstOf(v___x_3350_, v___x_3351_);
lean_dec_ref(v___x_3350_);
if (v___x_3352_ == 0)
{
lean_dec_ref(v___x_3348_);
lean_dec_ref(v___x_3346_);
lean_dec_ref(v_e_3328_);
goto v___jp_3339_;
}
else
{
lean_object* v_arg_3353_; uint8_t v___x_3354_; 
v_arg_3353_ = lean_ctor_get(v___x_3348_, 1);
lean_inc_ref(v_arg_3353_);
lean_dec_ref(v___x_3348_);
v___x_3354_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot(v_arg_3353_);
lean_dec_ref(v_arg_3353_);
if (v___x_3354_ == 0)
{
lean_object* v_arg_3355_; uint8_t v___x_3356_; 
v_arg_3355_ = lean_ctor_get(v___x_3346_, 1);
lean_inc_ref(v_arg_3355_);
lean_dec_ref(v___x_3346_);
v___x_3356_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot(v_arg_3355_);
lean_dec_ref(v_arg_3355_);
if (v___x_3356_ == 0)
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
lean_dec_ref(v_e_3328_);
v___x_3357_ = lean_box(0);
v___x_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
return v___x_3358_;
}
else
{
goto v___jp_3342_;
}
}
else
{
lean_dec_ref(v___x_3346_);
goto v___jp_3342_;
}
}
}
}
v___jp_3339_:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = lean_box(0);
v___x_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
return v___x_3341_;
}
v___jp_3342_:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f___closed__0));
v___x_3344_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go(v___x_3343_, v_e_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
return v___x_3344_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f___boxed(lean_object* v_e_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f(v_e_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
lean_dec(v_a_3368_);
lean_dec_ref(v_a_3367_);
lean_dec(v_a_3366_);
lean_dec_ref(v_a_3365_);
lean_dec(v_a_3364_);
lean_dec_ref(v_a_3363_);
lean_dec(v_a_3362_);
lean_dec_ref(v_a_3361_);
lean_dec(v_a_3360_);
return v_res_3370_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__2(void){
_start:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3376_ = lean_box(0);
v___x_3377_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__1));
v___x_3378_ = l_Lean_mkConst(v___x_3377_, v___x_3376_);
return v___x_3378_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__7(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3387_ = lean_box(0);
v___x_3388_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__6));
v___x_3389_ = l_Lean_mkConst(v___x_3388_, v___x_3387_);
return v___x_3389_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__10(void){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3395_ = lean_box(0);
v___x_3396_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__9));
v___x_3397_ = l_Lean_mkConst(v___x_3396_, v___x_3395_);
return v___x_3397_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__13(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3403_ = lean_box(0);
v___x_3404_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__12));
v___x_3405_ = l_Lean_mkConst(v___x_3404_, v___x_3403_);
return v___x_3405_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__18(void){
_start:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3415_ = lean_box(0);
v___x_3416_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__17));
v___x_3417_ = l_Lean_mkConst(v___x_3416_, v___x_3415_);
return v___x_3417_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__19(void){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3418_ = lean_unsigned_to_nat(0u);
v___x_3419_ = l_Lean_Level_ofNat(v___x_3418_);
return v___x_3419_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__20(void){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__19, &l_Lean_Meta_Grind_NormSym_simpForall___closed__19_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__19);
v___x_3421_ = l_Lean_mkSort(v___x_3420_);
return v___x_3421_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__23(void){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
v___x_3425_ = lean_box(0);
v___x_3426_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__22));
v___x_3427_ = l_Lean_mkConst(v___x_3426_, v___x_3425_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpForall(lean_object* v_e_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_){
_start:
{
lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; 
if (lean_obj_tag(v_e_3428_) == 7)
{
lean_object* v_binderName_3533_; lean_object* v_binderType_3534_; lean_object* v_body_3535_; uint8_t v_binderInfo_3536_; uint8_t v___x_3537_; 
v_binderName_3533_ = lean_ctor_get(v_e_3428_, 0);
v_binderType_3534_ = lean_ctor_get(v_e_3428_, 1);
v_body_3535_ = lean_ctor_get(v_e_3428_, 2);
v_binderInfo_3536_ = lean_ctor_get_uint8(v_e_3428_, sizeof(void*)*3 + 8);
v___x_3537_ = l_Lean_Expr_hasLooseBVars(v_body_3535_);
if (v___x_3537_ == 0)
{
uint8_t v___x_3538_; lean_object* v___x_3539_; 
v___x_3538_ = 1;
lean_inc_ref(v_binderType_3534_);
v___x_3539_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3534_, v_a_3435_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3540_);
lean_dec_ref_known(v___x_3539_, 1);
v___x_3541_ = l_Lean_Expr_cleanupAnnotations(v_a_3540_);
lean_dec(v_a_3540_);
v___x_3542_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_3543_ = l_Lean_Expr_isConstOf(v___x_3541_, v___x_3542_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3544_; uint8_t v___x_3545_; 
v___x_3544_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__10));
v___x_3545_ = l_Lean_Expr_isConstOf(v___x_3541_, v___x_3544_);
lean_dec_ref(v___x_3541_);
if (v___x_3545_ == 0)
{
lean_object* v___x_3546_; 
lean_inc_ref(v_body_3535_);
v___x_3546_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_body_3535_, v_a_3435_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v___x_3548_; uint8_t v___x_3549_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_a_3547_);
lean_dec_ref_known(v___x_3546_, 1);
v___x_3548_ = l_Lean_Expr_cleanupAnnotations(v_a_3547_);
lean_dec(v_a_3547_);
v___x_3549_ = l_Lean_Expr_isConstOf(v___x_3548_, v___x_3542_);
if (v___x_3549_ == 0)
{
uint8_t v___x_3550_; 
v___x_3550_ = l_Lean_Expr_isConstOf(v___x_3548_, v___x_3544_);
lean_dec_ref(v___x_3548_);
if (v___x_3550_ == 0)
{
lean_object* v___x_3551_; 
lean_inc_ref(v_binderType_3534_);
v___x_3551_ = l_Lean_Meta_isProp(v_binderType_3534_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; size_t v___x_3553_; size_t v___x_3554_; uint8_t v___x_3555_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3552_);
lean_dec_ref_known(v___x_3551_, 1);
v___x_3553_ = lean_ptr_addr(v_binderType_3534_);
v___x_3554_ = lean_ptr_addr(v_body_3535_);
v___x_3555_ = lean_usize_dec_eq(v___x_3553_, v___x_3554_);
if (v___x_3555_ == 0)
{
lean_dec(v_a_3552_);
v___y_3440_ = v_a_3429_;
v___y_3441_ = v_a_3430_;
v___y_3442_ = v_a_3431_;
v___y_3443_ = v_a_3432_;
v___y_3444_ = v_a_3433_;
v___y_3445_ = v_a_3434_;
v___y_3446_ = v_a_3435_;
v___y_3447_ = v_a_3436_;
v___y_3448_ = v_a_3437_;
goto v___jp_3439_;
}
else
{
uint8_t v___x_3556_; 
v___x_3556_ = lean_unbox(v_a_3552_);
lean_dec(v_a_3552_);
if (v___x_3556_ == 0)
{
v___y_3440_ = v_a_3429_;
v___y_3441_ = v_a_3430_;
v___y_3442_ = v_a_3431_;
v___y_3443_ = v_a_3432_;
v___y_3444_ = v_a_3433_;
v___y_3445_ = v_a_3434_;
v___y_3446_ = v_a_3435_;
v___y_3447_ = v_a_3436_;
v___y_3448_ = v_a_3437_;
goto v___jp_3439_;
}
else
{
lean_object* v___x_3557_; 
lean_inc_ref(v_binderType_3534_);
lean_dec_ref_known(v_e_3428_, 3);
v___x_3557_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3432_);
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
v___x_3562_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__2, &l_Lean_Meta_Grind_NormSym_simpForall___closed__2_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__2);
v___x_3563_ = l_Lean_Expr_app___override(v___x_3562_, v_binderType_3534_);
v___x_3564_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3564_, 0, v_a_3558_);
lean_ctor_set(v___x_3564_, 1, v___x_3563_);
lean_ctor_set_uint8(v___x_3564_, sizeof(void*)*2, v___x_3538_);
lean_ctor_set_uint8(v___x_3564_, sizeof(void*)*2 + 1, v___x_3550_);
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
lean_dec_ref(v_binderType_3534_);
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
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec_ref_known(v_e_3428_, 3);
v_a_3577_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3551_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3551_);
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
lean_object* v___x_3585_; 
lean_inc_ref(v_binderType_3534_);
lean_dec_ref_known(v_e_3428_, 3);
v___x_3585_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3432_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_object* v_a_3586_; lean_object* v___x_3587_; 
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_a_3586_);
lean_dec_ref_known(v___x_3585_, 1);
lean_inc_ref(v_binderType_3534_);
v___x_3587_ = l_Lean_Meta_getLevel(v_binderType_3534_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3601_; 
v_a_3588_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3590_ = v___x_3587_;
v_isShared_3591_ = v_isSharedCheck_3601_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3587_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3601_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3599_; 
v___x_3592_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__4));
v___x_3593_ = lean_box(0);
v___x_3594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3594_, 0, v_a_3588_);
lean_ctor_set(v___x_3594_, 1, v___x_3593_);
v___x_3595_ = l_Lean_mkConst(v___x_3592_, v___x_3594_);
v___x_3596_ = l_Lean_Expr_app___override(v___x_3595_, v_binderType_3534_);
v___x_3597_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3597_, 0, v_a_3586_);
lean_ctor_set(v___x_3597_, 1, v___x_3596_);
lean_ctor_set_uint8(v___x_3597_, sizeof(void*)*2, v___x_3538_);
lean_ctor_set_uint8(v___x_3597_, sizeof(void*)*2 + 1, v___x_3549_);
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 0, v___x_3597_);
v___x_3599_ = v___x_3590_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3597_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
else
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3609_; 
lean_dec(v_a_3586_);
lean_dec_ref(v_binderType_3534_);
v_a_3602_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3604_ = v___x_3587_;
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3587_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3609_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3607_; 
if (v_isShared_3605_ == 0)
{
v___x_3607_ = v___x_3604_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3602_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
lean_dec_ref(v_binderType_3534_);
v_a_3610_ = lean_ctor_get(v___x_3585_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3585_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3585_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3585_);
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
}
else
{
lean_object* v___x_3618_; 
lean_dec_ref(v___x_3548_);
lean_inc_ref(v_binderType_3534_);
v___x_3618_ = l_Lean_Meta_isProp(v_binderType_3534_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; uint8_t v___x_3620_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v___x_3618_, 1);
v___x_3620_ = lean_unbox(v_a_3619_);
lean_dec(v_a_3619_);
if (v___x_3620_ == 0)
{
v___y_3440_ = v_a_3429_;
v___y_3441_ = v_a_3430_;
v___y_3442_ = v_a_3431_;
v___y_3443_ = v_a_3432_;
v___y_3444_ = v_a_3433_;
v___y_3445_ = v_a_3434_;
v___y_3446_ = v_a_3435_;
v___y_3447_ = v_a_3436_;
v___y_3448_ = v_a_3437_;
goto v___jp_3439_;
}
else
{
lean_object* v___x_3621_; 
lean_inc_ref_n(v_binderType_3534_, 2);
lean_dec_ref_known(v_e_3428_, 3);
v___x_3621_ = l_Lean_Meta_Sym_mkNotS(v_binderType_3534_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3632_; 
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3624_ = v___x_3621_;
v_isShared_3625_ = v_isSharedCheck_3632_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3621_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3632_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3630_; 
v___x_3626_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__7, &l_Lean_Meta_Grind_NormSym_simpForall___closed__7_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__7);
v___x_3627_ = l_Lean_Expr_app___override(v___x_3626_, v_binderType_3534_);
v___x_3628_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3628_, 0, v_a_3622_);
lean_ctor_set(v___x_3628_, 1, v___x_3627_);
lean_ctor_set_uint8(v___x_3628_, sizeof(void*)*2, v___x_3545_);
lean_ctor_set_uint8(v___x_3628_, sizeof(void*)*2 + 1, v___x_3545_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 0, v___x_3628_);
v___x_3630_ = v___x_3624_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v___x_3628_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_dec_ref(v_binderType_3534_);
v_a_3633_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3621_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3621_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
}
else
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3648_; 
lean_dec_ref_known(v_e_3428_, 3);
v_a_3641_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3643_ = v___x_3618_;
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3618_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3646_; 
if (v_isShared_3644_ == 0)
{
v___x_3646_ = v___x_3643_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
}
else
{
lean_object* v_a_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3656_; 
lean_dec_ref_known(v_e_3428_, 3);
v_a_3649_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3651_ = v___x_3546_;
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_a_3649_);
lean_dec(v___x_3546_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3656_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3654_; 
if (v_isShared_3652_ == 0)
{
v___x_3654_ = v___x_3651_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_a_3649_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
}
}
}
}
else
{
lean_object* v___x_3657_; 
lean_inc_ref(v_body_3535_);
v___x_3657_ = l_Lean_Meta_isProp(v_body_3535_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3669_; 
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3660_ = v___x_3657_;
v_isShared_3661_ = v_isSharedCheck_3669_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3657_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3669_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
uint8_t v___x_3662_; 
v___x_3662_ = lean_unbox(v_a_3658_);
lean_dec(v_a_3658_);
if (v___x_3662_ == 0)
{
lean_del_object(v___x_3660_);
v___y_3440_ = v_a_3429_;
v___y_3441_ = v_a_3430_;
v___y_3442_ = v_a_3431_;
v___y_3443_ = v_a_3432_;
v___y_3444_ = v_a_3433_;
v___y_3445_ = v_a_3434_;
v___y_3446_ = v_a_3435_;
v___y_3447_ = v_a_3436_;
v___y_3448_ = v_a_3437_;
goto v___jp_3439_;
}
else
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3667_; 
lean_inc_ref_n(v_body_3535_, 2);
lean_dec_ref_known(v_e_3428_, 3);
v___x_3663_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__10, &l_Lean_Meta_Grind_NormSym_simpForall___closed__10_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__10);
v___x_3664_ = l_Lean_Expr_app___override(v___x_3663_, v_body_3535_);
v___x_3665_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3665_, 0, v_body_3535_);
lean_ctor_set(v___x_3665_, 1, v___x_3664_);
lean_ctor_set_uint8(v___x_3665_, sizeof(void*)*2, v___x_3538_);
lean_ctor_set_uint8(v___x_3665_, sizeof(void*)*2 + 1, v___x_3543_);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v___x_3665_);
v___x_3667_ = v___x_3660_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3665_);
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
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
lean_dec_ref_known(v_e_3428_, 3);
v_a_3670_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3657_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3657_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
}
else
{
lean_object* v___x_3678_; 
lean_dec_ref(v___x_3541_);
lean_inc_ref(v_body_3535_);
v___x_3678_ = l_Lean_Meta_isProp(v_body_3535_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; uint8_t v___x_3680_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_a_3679_);
lean_dec_ref_known(v___x_3678_, 1);
v___x_3680_ = lean_unbox(v_a_3679_);
lean_dec(v_a_3679_);
if (v___x_3680_ == 0)
{
v___y_3440_ = v_a_3429_;
v___y_3441_ = v_a_3430_;
v___y_3442_ = v_a_3431_;
v___y_3443_ = v_a_3432_;
v___y_3444_ = v_a_3433_;
v___y_3445_ = v_a_3434_;
v___y_3446_ = v_a_3435_;
v___y_3447_ = v_a_3436_;
v___y_3448_ = v_a_3437_;
goto v___jp_3439_;
}
else
{
lean_object* v___x_3681_; 
lean_inc_ref(v_body_3535_);
lean_dec_ref_known(v_e_3428_, 3);
v___x_3681_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3432_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3692_; 
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3684_ = v___x_3681_;
v_isShared_3685_ = v_isSharedCheck_3692_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3681_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3692_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3690_; 
v___x_3686_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__13, &l_Lean_Meta_Grind_NormSym_simpForall___closed__13_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__13);
v___x_3687_ = l_Lean_Expr_app___override(v___x_3686_, v_body_3535_);
v___x_3688_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3688_, 0, v_a_3682_);
lean_ctor_set(v___x_3688_, 1, v___x_3687_);
lean_ctor_set_uint8(v___x_3688_, sizeof(void*)*2, v___x_3538_);
lean_ctor_set_uint8(v___x_3688_, sizeof(void*)*2 + 1, v___x_3537_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 0, v___x_3688_);
v___x_3690_ = v___x_3684_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3688_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
else
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3700_; 
lean_dec_ref(v_body_3535_);
v_a_3693_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3695_ = v___x_3681_;
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3681_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3698_; 
if (v_isShared_3696_ == 0)
{
v___x_3698_ = v___x_3695_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
}
else
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
lean_dec_ref_known(v_e_3428_, 3);
v_a_3701_ = lean_ctor_get(v___x_3678_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___x_3678_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3678_);
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
lean_dec_ref_known(v_e_3428_, 3);
v_a_3709_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3716_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3716_ == 0)
{
v___x_3711_ = v___x_3539_;
v_isShared_3712_ = v_isSharedCheck_3716_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_a_3709_);
lean_dec(v___x_3539_);
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
uint8_t v___x_3717_; lean_object* v___x_3718_; 
v___x_3717_ = 0;
lean_inc_ref(v_binderType_3534_);
v___x_3718_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3534_, v_a_3435_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; uint8_t v___x_3722_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc(v_a_3719_);
lean_dec_ref_known(v___x_3718_, 1);
v___x_3720_ = l_Lean_Expr_cleanupAnnotations(v_a_3719_);
lean_dec(v_a_3719_);
v___x_3721_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_3722_ = l_Lean_Expr_isConstOf(v___x_3720_, v___x_3721_);
if (v___x_3722_ == 0)
{
lean_object* v___x_3723_; uint8_t v___x_3724_; 
v___x_3723_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__10));
v___x_3724_ = l_Lean_Expr_isConstOf(v___x_3720_, v___x_3723_);
lean_dec_ref(v___x_3720_);
if (v___x_3724_ == 0)
{
v___y_3440_ = v_a_3429_;
v___y_3441_ = v_a_3430_;
v___y_3442_ = v_a_3431_;
v___y_3443_ = v_a_3432_;
v___y_3444_ = v_a_3433_;
v___y_3445_ = v_a_3434_;
v___y_3446_ = v_a_3435_;
v___y_3447_ = v_a_3436_;
v___y_3448_ = v_a_3437_;
goto v___jp_3439_;
}
else
{
lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3725_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__15));
v___x_3726_ = lean_box(0);
v___x_3727_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___redArg(v___x_3725_, v___x_3726_, v_a_3433_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v_a_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref_known(v___x_3727_, 1);
v___x_3729_ = lean_unsigned_to_nat(1u);
v___x_3730_ = lean_mk_empty_array_with_capacity(v___x_3729_);
v___x_3731_ = lean_array_push(v___x_3730_, v_a_3728_);
lean_inc_ref(v_body_3535_);
v___x_3732_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_body_3535_, v___x_3731_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v_a_3733_; lean_object* v___x_3734_; 
v_a_3733_ = lean_ctor_get(v___x_3732_, 0);
lean_inc_n(v_a_3733_, 2);
lean_dec_ref_known(v___x_3732_, 1);
v___x_3734_ = l_Lean_Meta_isProp(v_a_3733_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3747_; 
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3737_ = v___x_3734_;
v_isShared_3738_ = v_isSharedCheck_3747_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3734_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3747_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
uint8_t v___x_3739_; 
v___x_3739_ = lean_unbox(v_a_3735_);
lean_dec(v_a_3735_);
if (v___x_3739_ == 0)
{
lean_del_object(v___x_3737_);
lean_dec(v_a_3733_);
v___y_3440_ = v_a_3429_;
v___y_3441_ = v_a_3430_;
v___y_3442_ = v_a_3431_;
v___y_3443_ = v_a_3432_;
v___y_3444_ = v_a_3433_;
v___y_3445_ = v_a_3434_;
v___y_3446_ = v_a_3435_;
v___y_3447_ = v_a_3436_;
v___y_3448_ = v_a_3437_;
goto v___jp_3439_;
}
else
{
lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3745_; 
lean_inc_ref(v_body_3535_);
lean_inc_ref(v_binderType_3534_);
lean_inc(v_binderName_3533_);
lean_dec_ref_known(v_e_3428_, 3);
v___x_3740_ = l_Lean_mkLambda(v_binderName_3533_, v_binderInfo_3536_, v_binderType_3534_, v_body_3535_);
v___x_3741_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__18, &l_Lean_Meta_Grind_NormSym_simpForall___closed__18_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__18);
v___x_3742_ = l_Lean_Expr_app___override(v___x_3741_, v___x_3740_);
v___x_3743_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3743_, 0, v_a_3733_);
lean_ctor_set(v___x_3743_, 1, v___x_3742_);
lean_ctor_set_uint8(v___x_3743_, sizeof(void*)*2, v___x_3537_);
lean_ctor_set_uint8(v___x_3743_, sizeof(void*)*2 + 1, v___x_3717_);
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 0, v___x_3743_);
v___x_3745_ = v___x_3737_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3743_);
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
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
lean_dec(v_a_3733_);
lean_dec_ref_known(v_e_3428_, 3);
v_a_3748_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3734_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3734_);
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
else
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3763_; 
lean_dec_ref_known(v_e_3428_, 3);
v_a_3756_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3758_ = v___x_3732_;
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3732_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3761_; 
if (v_isShared_3759_ == 0)
{
v___x_3761_ = v___x_3758_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_a_3756_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
else
{
lean_object* v_a_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3771_; 
lean_dec_ref_known(v_e_3428_, 3);
v_a_3764_ = lean_ctor_get(v___x_3727_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3727_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3766_ = v___x_3727_;
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_a_3764_);
lean_dec(v___x_3727_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3769_; 
if (v_isShared_3767_ == 0)
{
v___x_3769_ = v___x_3766_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_a_3764_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
}
}
else
{
lean_object* v___x_3772_; lean_object* v___x_3773_; 
lean_dec_ref(v___x_3720_);
lean_inc_ref(v_body_3535_);
lean_inc_ref(v_binderType_3534_);
lean_inc(v_binderName_3533_);
v___x_3772_ = l_Lean_mkLambda(v_binderName_3533_, v_binderInfo_3536_, v_binderType_3534_, v_body_3535_);
lean_inc(v_a_3437_);
lean_inc_ref(v_a_3436_);
lean_inc(v_a_3435_);
lean_inc_ref(v_a_3434_);
lean_inc_ref(v___x_3772_);
v___x_3773_ = lean_infer_type(v___x_3772_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_object* v_a_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v_a_3774_ = lean_ctor_get(v___x_3773_, 0);
lean_inc(v_a_3774_);
lean_dec_ref_known(v___x_3773_, 1);
v___x_3775_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__20, &l_Lean_Meta_Grind_NormSym_simpForall___closed__20_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__20);
lean_inc_ref(v_binderType_3534_);
lean_inc(v_binderName_3533_);
v___x_3776_ = l_Lean_mkForall(v_binderName_3533_, v_binderInfo_3536_, v_binderType_3534_, v___x_3775_);
v___x_3777_ = l_Lean_Meta_isExprDefEq(v_a_3774_, v___x_3776_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v_a_3778_; uint8_t v___x_3779_; 
v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_a_3778_);
lean_dec_ref_known(v___x_3777_, 1);
v___x_3779_ = lean_unbox(v_a_3778_);
lean_dec(v_a_3778_);
if (v___x_3779_ == 0)
{
lean_dec_ref(v___x_3772_);
v___y_3440_ = v_a_3429_;
v___y_3441_ = v_a_3430_;
v___y_3442_ = v_a_3431_;
v___y_3443_ = v_a_3432_;
v___y_3444_ = v_a_3433_;
v___y_3445_ = v_a_3434_;
v___y_3446_ = v_a_3435_;
v___y_3447_ = v_a_3436_;
v___y_3448_ = v_a_3437_;
goto v___jp_3439_;
}
else
{
lean_object* v___x_3780_; 
lean_dec_ref_known(v_e_3428_, 3);
v___x_3780_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3432_);
if (lean_obj_tag(v___x_3780_) == 0)
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3791_; 
v_a_3781_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3783_ = v___x_3780_;
v_isShared_3784_ = v_isSharedCheck_3791_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3780_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3791_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3789_; 
v___x_3785_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__23, &l_Lean_Meta_Grind_NormSym_simpForall___closed__23_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__23);
v___x_3786_ = l_Lean_Expr_app___override(v___x_3785_, v___x_3772_);
v___x_3787_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3787_, 0, v_a_3781_);
lean_ctor_set(v___x_3787_, 1, v___x_3786_);
lean_ctor_set_uint8(v___x_3787_, sizeof(void*)*2, v___x_3537_);
lean_ctor_set_uint8(v___x_3787_, sizeof(void*)*2 + 1, v___x_3717_);
if (v_isShared_3784_ == 0)
{
lean_ctor_set(v___x_3783_, 0, v___x_3787_);
v___x_3789_ = v___x_3783_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3787_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
lean_dec_ref(v___x_3772_);
v_a_3792_ = lean_ctor_get(v___x_3780_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3780_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3780_);
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
else
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
lean_dec_ref(v___x_3772_);
lean_dec_ref_known(v_e_3428_, 3);
v_a_3800_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3802_ = v___x_3777_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3777_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_dec_ref(v___x_3772_);
lean_dec_ref_known(v_e_3428_, 3);
v_a_3808_ = lean_ctor_get(v___x_3773_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3773_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3773_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
}
else
{
lean_object* v_a_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3823_; 
lean_dec_ref_known(v_e_3428_, 3);
v_a_3816_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3818_ = v___x_3718_;
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_a_3816_);
lean_dec(v___x_3718_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3823_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3821_; 
if (v_isShared_3819_ == 0)
{
v___x_3821_ = v___x_3818_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3816_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
}
else
{
lean_object* v___x_3824_; lean_object* v___x_3825_; 
lean_dec_ref(v_e_3428_);
v___x_3824_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_3825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3824_);
return v___x_3825_;
}
v___jp_3439_:
{
lean_object* v___x_3449_; 
lean_inc_ref(v_e_3428_);
v___x_3449_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f(v_e_3428_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3524_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3452_ = v___x_3449_;
v_isShared_3453_ = v_isSharedCheck_3524_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3449_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3524_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
if (lean_obj_tag(v_a_3450_) == 1)
{
lean_object* v_val_3454_; lean_object* v_fst_3455_; lean_object* v_snd_3456_; uint8_t v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3460_; 
lean_dec_ref(v_e_3428_);
v_val_3454_ = lean_ctor_get(v_a_3450_, 0);
lean_inc(v_val_3454_);
lean_dec_ref_known(v_a_3450_, 1);
v_fst_3455_ = lean_ctor_get(v_val_3454_, 0);
lean_inc(v_fst_3455_);
v_snd_3456_ = lean_ctor_get(v_val_3454_, 1);
lean_inc(v_snd_3456_);
lean_dec(v_val_3454_);
v___x_3457_ = 0;
v___x_3458_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3458_, 0, v_fst_3455_);
lean_ctor_set(v___x_3458_, 1, v_snd_3456_);
lean_ctor_set_uint8(v___x_3458_, sizeof(void*)*2, v___x_3457_);
lean_ctor_set_uint8(v___x_3458_, sizeof(void*)*2 + 1, v___x_3457_);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v___x_3458_);
v___x_3460_ = v___x_3452_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3458_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
else
{
lean_object* v___x_3462_; 
lean_del_object(v___x_3452_);
lean_dec(v_a_3450_);
v___x_3462_ = l_Lean_Meta_Grind_forallImpAnd_x3f(v_e_3428_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3515_; 
v_a_3463_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3465_ = v___x_3462_;
v_isShared_3466_ = v_isSharedCheck_3515_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3462_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3515_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
if (lean_obj_tag(v_a_3463_) == 1)
{
lean_object* v_val_3467_; lean_object* v_snd_3468_; lean_object* v_fst_3469_; lean_object* v_fst_3470_; lean_object* v_snd_3471_; lean_object* v___x_3472_; 
lean_del_object(v___x_3465_);
v_val_3467_ = lean_ctor_get(v_a_3463_, 0);
lean_inc(v_val_3467_);
lean_dec_ref_known(v_a_3463_, 1);
v_snd_3468_ = lean_ctor_get(v_val_3467_, 1);
lean_inc(v_snd_3468_);
v_fst_3469_ = lean_ctor_get(v_val_3467_, 0);
lean_inc(v_fst_3469_);
lean_dec(v_val_3467_);
v_fst_3470_ = lean_ctor_get(v_snd_3468_, 0);
lean_inc(v_fst_3470_);
v_snd_3471_ = lean_ctor_get(v_snd_3468_, 1);
lean_inc(v_snd_3471_);
lean_dec(v_snd_3468_);
v___x_3472_ = l_Lean_Meta_Sym_shareCommonInc(v_fst_3469_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_a_3473_; lean_object* v___x_3474_; 
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_a_3473_);
lean_dec_ref_known(v___x_3472_, 1);
v___x_3474_ = l_Lean_Meta_Sym_shareCommonInc(v_fst_3470_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; lean_object* v___x_3476_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_a_3475_);
lean_dec_ref_known(v___x_3474_, 1);
v___x_3476_ = l_Lean_Meta_Sym_mkAndS(v_a_3473_, v_a_3475_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3486_; 
v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3479_ = v___x_3476_;
v_isShared_3480_ = v_isSharedCheck_3486_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3476_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3486_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
uint8_t v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3484_; 
v___x_3481_ = 0;
v___x_3482_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3482_, 0, v_a_3477_);
lean_ctor_set(v___x_3482_, 1, v_snd_3471_);
lean_ctor_set_uint8(v___x_3482_, sizeof(void*)*2, v___x_3481_);
lean_ctor_set_uint8(v___x_3482_, sizeof(void*)*2 + 1, v___x_3481_);
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v___x_3482_);
v___x_3484_ = v___x_3479_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3482_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
else
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3494_; 
lean_dec(v_snd_3471_);
v_a_3487_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___x_3476_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3476_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
else
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
lean_dec(v_a_3473_);
lean_dec(v_snd_3471_);
v_a_3495_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3497_ = v___x_3474_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3474_);
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
lean_dec(v_snd_3471_);
lean_dec(v_fst_3470_);
v_a_3503_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3472_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3472_);
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
else
{
lean_object* v___x_3511_; lean_object* v___x_3513_; 
lean_dec(v_a_3463_);
v___x_3511_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_3466_ == 0)
{
lean_ctor_set(v___x_3465_, 0, v___x_3511_);
v___x_3513_ = v___x_3465_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3511_);
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
v_a_3516_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3462_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3462_);
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
}
}
else
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
lean_dec_ref(v_e_3428_);
v_a_3525_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3449_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3449_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpForall___boxed(lean_object* v_e_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_Lean_Meta_Grind_NormSym_simpForall(v_e_3826_, v_a_3827_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
lean_dec(v_a_3835_);
lean_dec_ref(v_a_3834_);
lean_dec(v_a_3833_);
lean_dec_ref(v_a_3832_);
lean_dec(v_a_3831_);
lean_dec_ref(v_a_3830_);
lean_dec(v_a_3829_);
lean_dec_ref(v_a_3828_);
lean_dec(v_a_3827_);
return v_res_3837_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__6(void){
_start:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3851_ = lean_box(0);
v___x_3852_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__5));
v___x_3853_ = l_Lean_mkConst(v___x_3852_, v___x_3851_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg(lean_object* v_e_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_){
_start:
{
lean_object* v___x_3883_; uint8_t v___x_3884_; 
v___x_3883_ = l_Lean_Expr_cleanupAnnotations(v_e_3869_);
v___x_3884_ = l_Lean_Expr_isApp(v___x_3883_);
if (v___x_3884_ == 0)
{
lean_dec_ref(v___x_3883_);
goto v___jp_3880_;
}
else
{
lean_object* v___x_3885_; uint8_t v___x_3886_; 
v___x_3885_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3883_);
v___x_3886_ = l_Lean_Expr_isApp(v___x_3885_);
if (v___x_3886_ == 0)
{
lean_dec_ref(v___x_3885_);
lean_dec_ref(v___x_3883_);
goto v___jp_3880_;
}
else
{
lean_object* v___x_3887_; lean_object* v___x_3888_; uint8_t v___x_3889_; 
v___x_3887_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3885_);
v___x_3888_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_etaReduce___closed__1));
v___x_3889_ = l_Lean_Expr_isConstOf(v___x_3887_, v___x_3888_);
if (v___x_3889_ == 0)
{
lean_dec_ref(v___x_3887_);
lean_dec_ref(v___x_3885_);
lean_dec_ref(v___x_3883_);
goto v___jp_3880_;
}
else
{
lean_object* v_arg_3890_; 
v_arg_3890_ = lean_ctor_get(v___x_3883_, 1);
lean_inc_ref(v_arg_3890_);
lean_dec_ref(v___x_3883_);
if (lean_obj_tag(v_arg_3890_) == 6)
{
lean_object* v_binderName_3891_; lean_object* v_body_3892_; lean_object* v_arg_3893_; lean_object* v_u_3894_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; uint8_t v___x_3979_; 
v_binderName_3891_ = lean_ctor_get(v_arg_3890_, 0);
lean_inc(v_binderName_3891_);
v_body_3892_ = lean_ctor_get(v_arg_3890_, 2);
lean_inc_ref(v_body_3892_);
lean_dec_ref_known(v_arg_3890_, 3);
v_arg_3893_ = lean_ctor_get(v___x_3885_, 1);
lean_inc_ref(v_arg_3893_);
lean_dec_ref(v___x_3885_);
v_u_3894_ = l_Lean_Expr_constLevels_x21(v___x_3887_);
v___x_3979_ = l_Lean_Expr_isApp(v_body_3892_);
if (v___x_3979_ == 0)
{
lean_dec(v_binderName_3891_);
lean_dec_ref(v___x_3887_);
v___y_3896_ = v_a_3870_;
v___y_3897_ = v_a_3871_;
v___y_3898_ = v_a_3872_;
v___y_3899_ = v_a_3873_;
v___y_3900_ = v_a_3874_;
v___y_3901_ = v_a_3875_;
goto v___jp_3895_;
}
else
{
lean_object* v___x_3980_; lean_object* v___x_3981_; uint8_t v___x_3982_; 
v___x_3980_ = l_Lean_Expr_getAppNumArgs(v_body_3892_);
v___x_3981_ = lean_unsigned_to_nat(2u);
v___x_3982_ = lean_nat_dec_eq(v___x_3980_, v___x_3981_);
lean_dec(v___x_3980_);
if (v___x_3982_ == 0)
{
lean_dec(v_binderName_3891_);
lean_dec_ref(v___x_3887_);
v___y_3896_ = v_a_3870_;
v___y_3897_ = v_a_3871_;
v___y_3898_ = v_a_3872_;
v___y_3899_ = v_a_3873_;
v___y_3900_ = v_a_3874_;
v___y_3901_ = v_a_3875_;
goto v___jp_3895_;
}
else
{
lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3983_ = l_Lean_Expr_appFn_x21(v_body_3892_);
v___x_3984_ = l_Lean_Expr_appFn_x21(v___x_3983_);
if (lean_obj_tag(v___x_3984_) == 4)
{
lean_object* v_declName_3985_; lean_object* v___x_3986_; uint8_t v___x_3987_; 
v_declName_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_declName_3985_);
lean_dec_ref_known(v___x_3984_, 2);
v___x_3986_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__12));
v___x_3987_ = lean_name_eq(v_declName_3985_, v___x_3986_);
if (v___x_3987_ == 0)
{
lean_object* v___x_3988_; uint8_t v___x_3989_; 
v___x_3988_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__14));
v___x_3989_ = lean_name_eq(v_declName_3985_, v___x_3988_);
lean_dec(v_declName_3985_);
if (v___x_3989_ == 0)
{
lean_dec_ref(v___x_3983_);
lean_dec(v_binderName_3891_);
lean_dec_ref(v___x_3887_);
v___y_3896_ = v_a_3870_;
v___y_3897_ = v_a_3871_;
v___y_3898_ = v_a_3872_;
v___y_3899_ = v_a_3873_;
v___y_3900_ = v_a_3874_;
v___y_3901_ = v_a_3875_;
goto v___jp_3895_;
}
else
{
lean_object* v_b_3990_; lean_object* v_b_3991_; uint8_t v___x_3992_; 
v_b_3990_ = l_Lean_Expr_appArg_x21(v___x_3983_);
lean_dec_ref(v___x_3983_);
v_b_3991_ = l_Lean_Expr_appArg_x21(v_body_3892_);
v___x_3992_ = l_Lean_Expr_hasLooseBVars(v_b_3990_);
if (v___x_3992_ == 0)
{
uint8_t v___x_3993_; lean_object* v___x_3994_; 
lean_dec_ref(v_body_3892_);
v___x_3993_ = 0;
lean_inc_ref(v_arg_3893_);
v___x_3994_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_binderName_3891_, v___x_3993_, v_arg_3893_, v_b_3991_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v_a_3995_; lean_object* v___x_3996_; 
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
lean_inc_n(v_a_3995_, 2);
lean_dec_ref_known(v___x_3994_, 1);
lean_inc_ref(v_arg_3893_);
v___x_3996_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___redArg(v___x_3887_, v_arg_3893_, v_a_3995_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v_a_3997_; lean_object* v___x_3998_; 
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_a_3997_);
lean_dec_ref_known(v___x_3996_, 1);
lean_inc_ref(v_b_3990_);
v___x_3998_ = l_Lean_Meta_Sym_mkAndS(v_b_3990_, v_a_3997_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4010_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4001_ = v___x_3998_;
v_isShared_4002_ = v_isSharedCheck_4010_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3998_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4010_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4008_; 
v___x_4003_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__8));
v___x_4004_ = l_Lean_mkConst(v___x_4003_, v_u_3894_);
v___x_4005_ = l_Lean_mkApp3(v___x_4004_, v_arg_3893_, v_a_3995_, v_b_3990_);
v___x_4006_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_4006_, 0, v_a_3999_);
lean_ctor_set(v___x_4006_, 1, v___x_4005_);
lean_ctor_set_uint8(v___x_4006_, sizeof(void*)*2, v___x_3987_);
lean_ctor_set_uint8(v___x_4006_, sizeof(void*)*2 + 1, v___x_3987_);
if (v_isShared_4002_ == 0)
{
lean_ctor_set(v___x_4001_, 0, v___x_4006_);
v___x_4008_ = v___x_4001_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v___x_4006_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4018_; 
lean_dec(v_a_3995_);
lean_dec_ref(v_b_3990_);
lean_dec(v_u_3894_);
lean_dec_ref(v_arg_3893_);
v_a_4011_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4013_ = v___x_3998_;
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_3998_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
}
else
{
lean_object* v_a_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4026_; 
lean_dec(v_a_3995_);
lean_dec_ref(v_b_3990_);
lean_dec(v_u_3894_);
lean_dec_ref(v_arg_3893_);
v_a_4019_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4026_ == 0)
{
v___x_4021_ = v___x_3996_;
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_a_4019_);
lean_dec(v___x_3996_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4024_; 
if (v_isShared_4022_ == 0)
{
v___x_4024_ = v___x_4021_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v_a_4019_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
}
}
else
{
lean_object* v_a_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4034_; 
lean_dec_ref(v_b_3990_);
lean_dec(v_u_3894_);
lean_dec_ref(v_arg_3893_);
lean_dec_ref(v___x_3887_);
v_a_4027_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4029_ = v___x_3994_;
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_a_4027_);
lean_dec(v___x_3994_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4032_; 
if (v_isShared_4030_ == 0)
{
v___x_4032_ = v___x_4029_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_a_4027_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
else
{
uint8_t v___x_4035_; 
v___x_4035_ = l_Lean_Expr_hasLooseBVars(v_b_3991_);
if (v___x_4035_ == 0)
{
uint8_t v___x_4036_; lean_object* v___x_4037_; 
lean_dec_ref(v_body_3892_);
v___x_4036_ = 0;
lean_inc_ref(v_arg_3893_);
v___x_4037_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_binderName_3891_, v___x_4036_, v_arg_3893_, v_b_3990_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v___x_4039_; 
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
lean_inc_n(v_a_4038_, 2);
lean_dec_ref_known(v___x_4037_, 1);
lean_inc_ref(v_arg_3893_);
v___x_4039_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___redArg(v___x_3887_, v_arg_3893_, v_a_4038_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_a_4040_; lean_object* v___x_4041_; 
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc(v_a_4040_);
lean_dec_ref_known(v___x_4039_, 1);
lean_inc_ref(v_b_3991_);
v___x_4041_ = l_Lean_Meta_Sym_mkAndS(v_a_4040_, v_b_3991_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4053_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4044_ = v___x_4041_;
v_isShared_4045_ = v_isSharedCheck_4053_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4041_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4053_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4051_; 
v___x_4046_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__10));
v___x_4047_ = l_Lean_mkConst(v___x_4046_, v_u_3894_);
v___x_4048_ = l_Lean_mkApp3(v___x_4047_, v_arg_3893_, v_a_4038_, v_b_3991_);
v___x_4049_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_4049_, 0, v_a_4042_);
lean_ctor_set(v___x_4049_, 1, v___x_4048_);
lean_ctor_set_uint8(v___x_4049_, sizeof(void*)*2, v___x_3987_);
lean_ctor_set_uint8(v___x_4049_, sizeof(void*)*2 + 1, v___x_3987_);
if (v_isShared_4045_ == 0)
{
lean_ctor_set(v___x_4044_, 0, v___x_4049_);
v___x_4051_ = v___x_4044_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v___x_4049_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
else
{
lean_object* v_a_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4061_; 
lean_dec(v_a_4038_);
lean_dec_ref(v_b_3991_);
lean_dec(v_u_3894_);
lean_dec_ref(v_arg_3893_);
v_a_4054_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4056_ = v___x_4041_;
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_a_4054_);
lean_dec(v___x_4041_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4061_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4059_; 
if (v_isShared_4057_ == 0)
{
v___x_4059_ = v___x_4056_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_a_4054_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
else
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4069_; 
lean_dec(v_a_4038_);
lean_dec_ref(v_b_3991_);
lean_dec(v_u_3894_);
lean_dec_ref(v_arg_3893_);
v_a_4062_ = lean_ctor_get(v___x_4039_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4064_ = v___x_4039_;
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___x_4039_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4067_; 
if (v_isShared_4065_ == 0)
{
v___x_4067_ = v___x_4064_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_a_4062_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
}
else
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4077_; 
lean_dec_ref(v_b_3991_);
lean_dec(v_u_3894_);
lean_dec_ref(v_arg_3893_);
lean_dec_ref(v___x_3887_);
v_a_4070_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4072_ = v___x_4037_;
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4037_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4075_; 
if (v_isShared_4073_ == 0)
{
v___x_4075_ = v___x_4072_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
}
else
{
lean_dec_ref(v_b_3991_);
lean_dec_ref(v_b_3990_);
lean_dec(v_binderName_3891_);
lean_dec_ref(v___x_3887_);
v___y_3896_ = v_a_3870_;
v___y_3897_ = v_a_3871_;
v___y_3898_ = v_a_3872_;
v___y_3899_ = v_a_3873_;
v___y_3900_ = v_a_3874_;
v___y_3901_ = v_a_3875_;
goto v___jp_3895_;
}
}
}
}
else
{
lean_object* v_pRaw_4078_; lean_object* v_qRaw_4079_; uint8_t v___x_4080_; lean_object* v___x_4081_; 
lean_dec(v_declName_3985_);
v_pRaw_4078_ = l_Lean_Expr_appArg_x21(v___x_3983_);
lean_dec_ref(v___x_3983_);
v_qRaw_4079_ = l_Lean_Expr_appArg_x21(v_body_3892_);
lean_dec_ref(v_body_3892_);
v___x_4080_ = 0;
lean_inc_ref(v_arg_3893_);
lean_inc(v_binderName_3891_);
v___x_4081_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_binderName_3891_, v___x_4080_, v_arg_3893_, v_pRaw_4078_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_a_4082_; lean_object* v___x_4083_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
lean_inc(v_a_4082_);
lean_dec_ref_known(v___x_4081_, 1);
lean_inc_ref(v_arg_3893_);
v___x_4083_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_binderName_3891_, v___x_4080_, v_arg_3893_, v_qRaw_4079_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v_a_4084_; lean_object* v___x_4085_; 
v_a_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc(v_a_4084_);
lean_dec_ref_known(v___x_4083_, 1);
lean_inc(v_a_4082_);
lean_inc_ref(v_arg_3893_);
lean_inc_ref(v___x_3887_);
v___x_4085_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___redArg(v___x_3887_, v_arg_3893_, v_a_4082_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
if (lean_obj_tag(v___x_4085_) == 0)
{
lean_object* v_a_4086_; lean_object* v___x_4087_; 
v_a_4086_ = lean_ctor_get(v___x_4085_, 0);
lean_inc(v_a_4086_);
lean_dec_ref_known(v___x_4085_, 1);
lean_inc(v_a_4084_);
lean_inc_ref(v_arg_3893_);
v___x_4087_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___redArg(v___x_3887_, v_arg_3893_, v_a_4084_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_object* v_a_4088_; lean_object* v___x_4089_; 
v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
lean_inc(v_a_4088_);
lean_dec_ref_known(v___x_4087_, 1);
v___x_4089_ = l_Lean_Meta_Sym_mkOrS(v_a_4086_, v_a_4088_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4102_; 
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4092_ = v___x_4089_;
v_isShared_4093_ = v_isSharedCheck_4102_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4089_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4102_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; uint8_t v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4100_; 
v___x_4094_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__12));
v___x_4095_ = l_Lean_mkConst(v___x_4094_, v_u_3894_);
v___x_4096_ = l_Lean_mkApp3(v___x_4095_, v_arg_3893_, v_a_4082_, v_a_4084_);
v___x_4097_ = 0;
v___x_4098_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_4098_, 0, v_a_4090_);
lean_ctor_set(v___x_4098_, 1, v___x_4096_);
lean_ctor_set_uint8(v___x_4098_, sizeof(void*)*2, v___x_4097_);
lean_ctor_set_uint8(v___x_4098_, sizeof(void*)*2 + 1, v___x_4097_);
if (v_isShared_4093_ == 0)
{
lean_ctor_set(v___x_4092_, 0, v___x_4098_);
v___x_4100_ = v___x_4092_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v___x_4098_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
}
else
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4110_; 
lean_dec(v_a_4084_);
lean_dec(v_a_4082_);
lean_dec(v_u_3894_);
lean_dec_ref(v_arg_3893_);
v_a_4103_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4105_ = v___x_4089_;
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4089_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
}
else
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
lean_dec(v_a_4086_);
lean_dec(v_a_4084_);
lean_dec(v_a_4082_);
lean_dec(v_u_3894_);
lean_dec_ref(v_arg_3893_);
v_a_4111_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4087_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4087_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
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
lean_dec(v_a_4084_);
lean_dec(v_a_4082_);
lean_dec(v_u_3894_);
lean_dec_ref(v_arg_3893_);
lean_dec_ref(v___x_3887_);
v_a_4119_ = lean_ctor_get(v___x_4085_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4085_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_4085_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4085_);
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
else
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4134_; 
lean_dec(v_a_4082_);
lean_dec(v_u_3894_);
lean_dec_ref(v_arg_3893_);
lean_dec_ref(v___x_3887_);
v_a_4127_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4129_ = v___x_4083_;
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4083_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4127_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_dec_ref(v_qRaw_4079_);
lean_dec(v_u_3894_);
lean_dec_ref(v_arg_3893_);
lean_dec(v_binderName_3891_);
lean_dec_ref(v___x_3887_);
v_a_4135_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4081_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4081_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
}
else
{
lean_object* v___x_4143_; lean_object* v___x_4144_; 
lean_dec_ref(v___x_3984_);
lean_dec_ref(v___x_3983_);
lean_dec(v_u_3894_);
lean_dec_ref(v_arg_3893_);
lean_dec_ref(v_body_3892_);
lean_dec(v_binderName_3891_);
lean_dec_ref(v___x_3887_);
v___x_4143_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4143_);
return v___x_4144_;
}
}
}
v___jp_3895_:
{
uint8_t v___x_3902_; 
v___x_3902_ = l_Lean_Expr_hasLooseBVars(v_body_3892_);
if (v___x_3902_ == 0)
{
lean_object* v___x_3903_; 
lean_inc_ref(v_arg_3893_);
v___x_3903_ = l_Lean_Meta_isProp(v_arg_3893_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; uint8_t v___x_3905_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_a_3904_);
lean_dec_ref_known(v___x_3903_, 1);
v___x_3905_ = lean_unbox(v_a_3904_);
if (v___x_3905_ == 0)
{
lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3906_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__1));
lean_inc(v_u_3894_);
v___x_3907_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___redArg(v___x_3906_, v_u_3894_, v___y_3897_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3909_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v___x_3907_, 1);
lean_inc_ref(v_arg_3893_);
v___x_3909_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(v_a_3908_, v_arg_3893_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3911_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v___x_3909_, 1);
v___x_3911_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_3910_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3926_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3914_ = v___x_3911_;
v_isShared_3915_ = v_isSharedCheck_3926_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3911_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3926_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
if (lean_obj_tag(v_a_3912_) == 1)
{
lean_object* v_val_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; uint8_t v___x_3921_; uint8_t v___x_3922_; lean_object* v___x_3924_; 
v_val_3916_ = lean_ctor_get(v_a_3912_, 0);
lean_inc(v_val_3916_);
lean_dec_ref_known(v_a_3912_, 1);
v___x_3917_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__3));
v___x_3918_ = l_Lean_mkConst(v___x_3917_, v_u_3894_);
lean_inc_ref(v_body_3892_);
v___x_3919_ = l_Lean_mkApp3(v___x_3918_, v_arg_3893_, v_val_3916_, v_body_3892_);
v___x_3920_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3920_, 0, v_body_3892_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
v___x_3921_ = lean_unbox(v_a_3904_);
lean_ctor_set_uint8(v___x_3920_, sizeof(void*)*2, v___x_3921_);
v___x_3922_ = lean_unbox(v_a_3904_);
lean_dec(v_a_3904_);
lean_ctor_set_uint8(v___x_3920_, sizeof(void*)*2 + 1, v___x_3922_);
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 0, v___x_3920_);
v___x_3924_ = v___x_3914_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3920_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
else
{
lean_del_object(v___x_3914_);
lean_dec(v_a_3912_);
lean_dec(v_a_3904_);
lean_dec(v_u_3894_);
lean_dec_ref(v_arg_3893_);
lean_dec_ref(v_body_3892_);
goto v___jp_3877_;
}
}
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
lean_dec(v_a_3904_);
lean_dec(v_u_3894_);
lean_dec_ref(v_arg_3893_);
lean_dec_ref(v_body_3892_);
v_a_3927_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3929_ = v___x_3911_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3911_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
lean_dec(v_a_3904_);
lean_dec(v_u_3894_);
lean_dec_ref(v_arg_3893_);
lean_dec_ref(v_body_3892_);
v_a_3935_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3937_ = v___x_3909_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3909_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
else
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
lean_dec(v_a_3904_);
lean_dec(v_u_3894_);
lean_dec_ref(v_arg_3893_);
lean_dec_ref(v_body_3892_);
v_a_3943_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___x_3907_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3907_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3943_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
else
{
lean_object* v___x_3951_; 
lean_dec(v_a_3904_);
lean_dec(v_u_3894_);
lean_inc_ref(v_body_3892_);
lean_inc_ref(v_arg_3893_);
v___x_3951_ = l_Lean_Meta_Sym_mkAndS(v_arg_3893_, v_body_3892_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v_a_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3962_; 
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3954_ = v___x_3951_;
v_isShared_3955_ = v_isSharedCheck_3962_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_a_3952_);
lean_dec(v___x_3951_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3962_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3960_; 
v___x_3956_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__6, &l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__6_once, _init_l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__6);
v___x_3957_ = l_Lean_mkAppB(v___x_3956_, v_arg_3893_, v_body_3892_);
v___x_3958_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3958_, 0, v_a_3952_);
lean_ctor_set(v___x_3958_, 1, v___x_3957_);
lean_ctor_set_uint8(v___x_3958_, sizeof(void*)*2, v___x_3902_);
lean_ctor_set_uint8(v___x_3958_, sizeof(void*)*2 + 1, v___x_3902_);
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 0, v___x_3958_);
v___x_3960_ = v___x_3954_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v___x_3958_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
lean_dec_ref(v_arg_3893_);
lean_dec_ref(v_body_3892_);
v_a_3963_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3951_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3951_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
}
else
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
lean_dec(v_u_3894_);
lean_dec_ref(v_arg_3893_);
lean_dec_ref(v_body_3892_);
v_a_3971_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3903_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3903_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
else
{
lean_dec(v_u_3894_);
lean_dec_ref(v_arg_3893_);
lean_dec_ref(v_body_3892_);
goto v___jp_3877_;
}
}
}
else
{
lean_object* v___x_4145_; lean_object* v___x_4146_; 
lean_dec_ref(v_arg_3890_);
lean_dec_ref(v___x_3887_);
lean_dec_ref(v___x_3885_);
v___x_4145_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4145_);
return v___x_4146_;
}
}
}
}
v___jp_3877_:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3878_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_3879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3878_);
return v___x_3879_;
}
v___jp_3880_:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3881_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
return v___x_3882_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg___boxed(lean_object* v_e_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_){
_start:
{
lean_object* v_res_4155_; 
v_res_4155_ = l_Lean_Meta_Grind_NormSym_simpExists___redArg(v_e_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_, v_a_4153_);
lean_dec(v_a_4153_);
lean_dec_ref(v_a_4152_);
lean_dec(v_a_4151_);
lean_dec_ref(v_a_4150_);
lean_dec(v_a_4149_);
lean_dec_ref(v_a_4148_);
lean_dec_ref(v_e_4147_);
return v_res_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists(lean_object* v_e_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_){
_start:
{
lean_object* v___x_4167_; 
v___x_4167_ = l_Lean_Meta_Grind_NormSym_simpExists___redArg(v_e_4156_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_);
return v___x_4167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists___boxed(lean_object* v_e_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l_Lean_Meta_Grind_NormSym_simpExists(v_e_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_);
lean_dec(v_a_4177_);
lean_dec_ref(v_a_4176_);
lean_dec(v_a_4175_);
lean_dec_ref(v_a_4174_);
lean_dec(v_a_4173_);
lean_dec_ref(v_a_4172_);
lean_dec(v_a_4171_);
lean_dec_ref(v_a_4170_);
lean_dec(v_a_4169_);
lean_dec_ref(v_e_4168_);
return v_res_4179_;
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

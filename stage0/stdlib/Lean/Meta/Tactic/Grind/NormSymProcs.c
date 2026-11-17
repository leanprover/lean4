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
static const lean_ctor_object l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_eraseMData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_hasEtaReducibleArg(lean_object* v_a_66_){
_start:
{
if (lean_obj_tag(v_a_66_) == 5)
{
lean_object* v_fn_67_; lean_object* v_arg_68_; uint8_t v___x_69_; 
v_fn_67_ = lean_ctor_get(v_a_66_, 0);
v_arg_68_ = lean_ctor_get(v_a_66_, 1);
v___x_69_ = l_Lean_Meta_Sym_isEtaReducible(v_arg_68_);
if (v___x_69_ == 0)
{
v_a_66_ = v_fn_67_;
goto _start;
}
else
{
return v___x_69_;
}
}
else
{
uint8_t v___x_71_; 
v___x_71_ = 0;
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_hasEtaReducibleArg___boxed(lean_object* v_a_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_hasEtaReducibleArg(v_a_72_);
lean_dec_ref(v_a_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(lean_object* v_f_75_, lean_object* v_a_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___y_85_; lean_object* v___x_88_; uint8_t v_debug_89_; 
v___x_88_ = lean_st_ref_get(v___y_78_);
v_debug_89_ = lean_ctor_get_uint8(v___x_88_, sizeof(void*)*13);
lean_dec(v___x_88_);
if (v_debug_89_ == 0)
{
v___y_85_ = v___y_78_;
goto v___jp_84_;
}
else
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_75_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v___x_91_; 
lean_dec_ref_known(v___x_90_, 1);
v___x_91_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_dec_ref_known(v___x_91_, 1);
v___y_85_ = v___y_78_;
goto v___jp_84_;
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
lean_dec_ref(v_a_76_);
lean_dec_ref(v_f_75_);
v_a_92_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v___x_91_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_91_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
else
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
lean_dec_ref(v_a_76_);
lean_dec_ref(v_f_75_);
v_a_100_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_107_ == 0)
{
v___x_102_ = v___x_90_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_90_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_a_100_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
v___jp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = l_Lean_Expr_app___override(v_f_75_, v_a_76_);
v___x_87_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_86_, v___y_85_);
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg___boxed(lean_object* v_f_108_, lean_object* v_a_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(v_f_108_, v_a_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0(lean_object* v_f_118_, lean_object* v_a_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(v_f_118_, v_a_119_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___boxed(lean_object* v_f_131_, lean_object* v_a_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0(v_f_131_, v_a_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go(lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
if (lean_obj_tag(v_a_144_) == 5)
{
lean_object* v_fn_155_; lean_object* v_arg_156_; lean_object* v___x_157_; 
v_fn_155_ = lean_ctor_get(v_a_144_, 0);
lean_inc_ref(v_fn_155_);
v_arg_156_ = lean_ctor_get(v_a_144_, 1);
lean_inc_ref(v_arg_156_);
lean_dec_ref_known(v_a_144_, 2);
v___x_157_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go(v_fn_155_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_a_158_);
lean_dec_ref_known(v___x_157_, 1);
v___x_159_ = l_Lean_Meta_Sym_etaReduce(v_arg_156_);
lean_dec_ref(v_arg_156_);
v___x_160_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(v_a_158_, v___x_159_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
return v___x_160_;
}
else
{
lean_dec_ref(v_arg_156_);
return v___x_157_;
}
}
else
{
lean_object* v___x_161_; 
v___x_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_161_, 0, v_a_144_);
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go___boxed(lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go(v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_etaReduce(lean_object* v_e_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v___y_192_; lean_object* v___y_193_; lean_object* v___y_194_; lean_object* v___y_195_; lean_object* v___y_196_; lean_object* v___y_197_; lean_object* v___y_198_; lean_object* v___y_199_; lean_object* v___y_200_; uint8_t v___x_236_; 
v___x_236_ = l_Lean_Expr_isApp(v_e_180_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec_ref(v_e_180_);
v___x_237_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_237_, 0, v___x_236_);
lean_ctor_set_uint8(v___x_237_, 1, v___x_236_);
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
return v___x_238_;
}
else
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Expr_getAppFn(v_e_180_);
if (lean_obj_tag(v___x_239_) == 4)
{
lean_object* v_declName_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v_declName_240_ = lean_ctor_get(v___x_239_, 0);
lean_inc(v_declName_240_);
lean_dec_ref_known(v___x_239_, 2);
v___x_241_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_etaReduce___closed__1));
v___x_242_ = lean_name_eq(v_declName_240_, v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_243_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_etaReduce___closed__3));
v___x_244_ = lean_name_eq(v_declName_240_, v___x_243_);
lean_dec(v_declName_240_);
if (v___x_244_ == 0)
{
v___y_192_ = v_a_181_;
v___y_193_ = v_a_182_;
v___y_194_ = v_a_183_;
v___y_195_ = v_a_184_;
v___y_196_ = v_a_185_;
v___y_197_ = v_a_186_;
v___y_198_ = v_a_187_;
v___y_199_ = v_a_188_;
v___y_200_ = v_a_189_;
goto v___jp_191_;
}
else
{
lean_dec_ref(v_e_180_);
goto v___jp_233_;
}
}
else
{
lean_dec(v_declName_240_);
lean_dec_ref(v_e_180_);
goto v___jp_233_;
}
}
else
{
lean_dec_ref(v___x_239_);
v___y_192_ = v_a_181_;
v___y_193_ = v_a_182_;
v___y_194_ = v_a_183_;
v___y_195_ = v_a_184_;
v___y_196_ = v_a_185_;
v___y_197_ = v_a_186_;
v___y_198_ = v_a_187_;
v___y_199_ = v_a_188_;
v___y_200_ = v_a_189_;
goto v___jp_191_;
}
}
v___jp_191_:
{
uint8_t v___x_201_; 
v___x_201_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_hasEtaReducibleArg(v_e_180_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec_ref(v_e_180_);
v___x_202_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_202_, 0, v___x_201_);
lean_ctor_set_uint8(v___x_202_, 1, v___x_201_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
return v___x_203_;
}
else
{
lean_object* v___x_204_; 
v___x_204_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go(v_e_180_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v___x_206_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc_n(v_a_205_, 2);
lean_dec_ref_known(v___x_204_, 1);
v___x_206_ = l_Lean_Meta_Sym_mkEqRefl(v_a_205_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_216_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_216_ == 0)
{
v___x_209_ = v___x_206_;
v_isShared_210_ = v_isSharedCheck_216_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_206_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_216_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_214_; 
v___x_211_ = 0;
v___x_212_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_212_, 0, v_a_205_);
lean_ctor_set(v___x_212_, 1, v_a_207_);
lean_ctor_set_uint8(v___x_212_, sizeof(void*)*2, v___x_211_);
lean_ctor_set_uint8(v___x_212_, sizeof(void*)*2 + 1, v___x_211_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_212_);
v___x_214_ = v___x_209_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
else
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
lean_dec(v_a_205_);
v_a_217_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v___x_206_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_206_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_217_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
v_a_225_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_204_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_204_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
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
}
v___jp_233_:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_etaReduce___boxed(lean_object* v_e_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Meta_Grind_NormSym_etaReduce(v_e_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(lean_object* v_e_264_){
_start:
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = l_Lean_Expr_cleanupAnnotations(v_e_264_);
v___x_270_ = l_Lean_Expr_isApp(v___x_269_);
if (v___x_270_ == 0)
{
lean_dec_ref(v___x_269_);
goto v___jp_266_;
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_271_ = l_Lean_Expr_appFnCleanup___redArg(v___x_269_);
lean_dec_ref(v___x_269_);
v___x_272_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___closed__3));
v___x_273_ = l_Lean_Expr_isConstOf(v___x_271_, v___x_272_);
lean_dec_ref(v___x_271_);
if (v___x_273_ == 0)
{
goto v___jp_266_;
}
else
{
uint8_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = 0;
v___x_275_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_273_, v___x_274_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
}
v___jp_266_:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___redArg___boxed(lean_object* v_e_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(v_e_277_);
lean_dec_ref(v_e_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond(lean_object* v_e_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Meta_Grind_NormSym_preMatchCond___redArg(v_e_280_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_preMatchCond___boxed(lean_object* v_e_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_Meta_Grind_NormSym_preMatchCond(v_e_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
lean_dec(v_a_293_);
lean_dec_ref(v_e_292_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(lean_object* v_declName_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; lean_object* v_env_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_307_ = lean_st_ref_get(v___y_305_);
v_env_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc_ref(v_env_308_);
lean_dec(v___x_307_);
v___x_309_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_308_, v_declName_304_);
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg___boxed(lean_object* v_declName_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(v_declName_311_, v___y_312_);
lean_dec(v___y_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0(lean_object* v_declName_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(v_declName_315_, v___y_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___boxed(lean_object* v_declName_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0(v_declName_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(lean_object* v_e_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
if (lean_obj_tag(v_e_344_) == 5)
{
lean_object* v_fn_358_; lean_object* v_arg_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v_fn_358_ = lean_ctor_get(v_e_344_, 0);
lean_inc_ref(v_fn_358_);
v_arg_359_ = lean_ctor_get(v_e_344_, 1);
lean_inc_ref(v_arg_359_);
v___x_360_ = l_Lean_Expr_cleanupAnnotations(v_e_344_);
v___x_361_ = l_Lean_Expr_isApp(v___x_360_);
if (v___x_361_ == 0)
{
lean_dec_ref(v___x_360_);
lean_dec_ref(v_arg_359_);
lean_dec_ref_known(v_e_344_, 2);
lean_dec_ref(v_fn_358_);
goto v___jp_355_;
}
else
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = l_Lean_Expr_appFnCleanup___redArg(v___x_360_);
lean_dec_ref(v___x_360_);
v___x_363_ = l_Lean_Expr_isApp(v___x_362_);
if (v___x_363_ == 0)
{
lean_dec_ref(v___x_362_);
lean_dec_ref(v_arg_359_);
lean_dec_ref_known(v_e_344_, 2);
lean_dec_ref(v_fn_358_);
goto v___jp_355_;
}
else
{
lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v___x_364_ = l_Lean_Expr_appFnCleanup___redArg(v___x_362_);
lean_dec_ref(v___x_362_);
v___x_365_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___closed__1));
v___x_366_ = l_Lean_Expr_isConstOf(v___x_364_, v___x_365_);
lean_dec_ref(v___x_364_);
if (v___x_366_ == 0)
{
lean_dec_ref(v_arg_359_);
lean_dec_ref_known(v_e_344_, 2);
lean_dec_ref(v_fn_358_);
goto v___jp_355_;
}
else
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_Expr_getAppFn(v_arg_359_);
if (lean_obj_tag(v___x_367_) == 4)
{
lean_object* v_declName_368_; lean_object* v___x_369_; lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_411_; 
v_declName_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_declName_368_);
lean_dec_ref_known(v___x_367_, 2);
v___x_369_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly_spec__0___redArg(v_declName_368_, v_a_353_);
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_411_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_411_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_411_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
if (lean_obj_tag(v_a_370_) == 1)
{
lean_object* v_val_374_; lean_object* v_numParams_375_; lean_object* v_numDiscrs_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
lean_del_object(v___x_372_);
v_val_374_ = lean_ctor_get(v_a_370_, 0);
lean_inc(v_val_374_);
lean_dec_ref_known(v_a_370_, 1);
v_numParams_375_ = lean_ctor_get(v_val_374_, 0);
lean_inc(v_numParams_375_);
v_numDiscrs_376_ = lean_ctor_get(v_val_374_, 1);
lean_inc(v_numDiscrs_376_);
lean_dec(v_val_374_);
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_nat_add(v_numParams_375_, v___x_377_);
lean_dec(v_numParams_375_);
v___x_379_ = lean_nat_add(v___x_378_, v_numDiscrs_376_);
lean_dec(v_numDiscrs_376_);
lean_inc_ref(v_arg_359_);
v___x_380_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(v_arg_359_, v___x_378_, v___x_379_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
lean_dec(v___x_379_);
lean_dec(v___x_378_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_382_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v___x_380_, 1);
v___x_382_ = l_Lean_Meta_Sym_Simp_mkCongrArg___redArg(v_e_344_, v_fn_358_, v_arg_359_, v_a_381_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_405_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_405_ == 0)
{
v___x_385_ = v___x_382_;
v_isShared_386_ = v_isSharedCheck_405_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_382_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_405_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
if (lean_obj_tag(v_a_383_) == 0)
{
uint8_t v_contextDependent_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v_contextDependent_387_ = lean_ctor_get_uint8(v_a_383_, 1);
lean_dec_ref_known(v_a_383_, 0);
v___x_388_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_366_, v_contextDependent_387_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v___x_388_);
v___x_390_ = v___x_385_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
else
{
lean_object* v_e_x27_392_; lean_object* v_proof_393_; uint8_t v_contextDependent_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_404_; 
v_e_x27_392_ = lean_ctor_get(v_a_383_, 0);
v_proof_393_ = lean_ctor_get(v_a_383_, 1);
v_contextDependent_394_ = lean_ctor_get_uint8(v_a_383_, sizeof(void*)*2 + 1);
v_isSharedCheck_404_ = !lean_is_exclusive(v_a_383_);
if (v_isSharedCheck_404_ == 0)
{
v___x_396_ = v_a_383_;
v_isShared_397_ = v_isSharedCheck_404_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_proof_393_);
lean_inc(v_e_x27_392_);
lean_dec(v_a_383_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_404_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_e_x27_392_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_proof_393_);
lean_ctor_set_uint8(v_reuseFailAlloc_403_, sizeof(void*)*2 + 1, v_contextDependent_394_);
v___x_399_ = v_reuseFailAlloc_403_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_401_; 
lean_ctor_set_uint8(v___x_399_, sizeof(void*)*2, v___x_366_);
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v___x_399_);
v___x_401_ = v___x_385_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
else
{
return v___x_382_;
}
}
else
{
lean_dec_ref(v_arg_359_);
lean_dec_ref_known(v_e_344_, 2);
lean_dec_ref(v_fn_358_);
return v___x_380_;
}
}
else
{
uint8_t v___x_406_; lean_object* v___x_407_; lean_object* v___x_409_; 
lean_dec(v_a_370_);
lean_dec_ref(v_arg_359_);
lean_dec_ref_known(v_e_344_, 2);
lean_dec_ref(v_fn_358_);
v___x_406_ = 0;
v___x_407_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_366_, v___x_406_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_407_);
v___x_409_ = v___x_372_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
else
{
uint8_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
lean_dec_ref(v___x_367_);
lean_dec_ref(v_arg_359_);
lean_dec_ref_known(v_e_344_, 2);
lean_dec_ref(v_fn_358_);
v___x_412_ = 0;
v___x_413_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_366_, v___x_412_);
v___x_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
return v___x_414_;
}
}
}
}
}
else
{
lean_object* v___x_415_; lean_object* v___x_416_; 
lean_dec_ref(v_e_344_);
v___x_415_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
v___jp_355_:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly___boxed(lean_object* v_e_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Meta_Grind_NormSym_simpMatchDiscrsOnly(v_e_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
return v_res_428_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(lean_object* v_declName_452_){
_start:
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__2));
v___x_454_ = lean_name_eq(v_declName_452_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__4));
v___x_456_ = lean_name_eq(v_declName_452_, v___x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__6));
v___x_458_ = lean_name_eq(v_declName_452_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__9));
v___x_460_ = lean_name_eq(v_declName_452_, v___x_459_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___closed__12));
v___x_462_ = lean_name_eq(v_declName_452_, v___x_461_);
return v___x_462_;
}
else
{
return v___x_460_;
}
}
else
{
return v___x_458_;
}
}
else
{
return v___x_456_;
}
}
else
{
return v___x_454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget___boxed(lean_object* v_declName_463_){
_start:
{
uint8_t v_res_464_; lean_object* v_r_465_; 
v_res_464_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(v_declName_463_);
lean_dec(v_declName_463_);
v_r_465_ = lean_box(v_res_464_);
return v_r_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(lean_object* v_u_466_, lean_object* v___y_467_){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = l_Lean_Expr_sort___override(v_u_466_);
v___x_470_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_469_, v___y_467_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg___boxed(lean_object* v_u_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v_u_471_, v___y_472_);
lean_dec(v___y_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1(lean_object* v_u_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v_u_475_, v___y_480_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___boxed(lean_object* v_u_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1(v_u_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___redArg(lean_object* v_f_499_, lean_object* v_a_u2081_500_, lean_object* v_a_u2082_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(v_f_499_, v_a_u2081_500_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___x_509_, 1);
v___x_511_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(v_a_510_, v_a_u2082_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
return v___x_511_;
}
else
{
lean_dec_ref(v_a_u2082_501_);
return v___x_509_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___redArg___boxed(lean_object* v_f_512_, lean_object* v_a_u2081_513_, lean_object* v_a_u2082_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___redArg(v_f_512_, v_a_u2081_513_, v_a_u2082_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(lean_object* v_f_523_, lean_object* v_a_u2081_524_, lean_object* v_a_u2082_525_, lean_object* v_a_u2083_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___redArg(v_f_523_, v_a_u2081_524_, v_a_u2082_525_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_539_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref_known(v___x_537_, 1);
v___x_539_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(v_a_538_, v_a_u2083_526_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
return v___x_539_;
}
else
{
lean_dec_ref(v_a_u2083_526_);
return v___x_537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0___boxed(lean_object* v_f_540_, lean_object* v_a_u2081_541_, lean_object* v_a_u2082_542_, lean_object* v_a_u2083_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v_f_540_, v_a_u2081_541_, v_a_u2082_542_, v_a_u2083_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
return v_res_554_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__5(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_565_ = lean_box(0);
v___x_566_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__4));
v___x_567_ = l_Lean_mkConst(v___x_566_, v___x_565_);
return v___x_567_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__8(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = lean_box(0);
v___x_574_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__7));
v___x_575_ = l_Lean_mkConst(v___x_574_, v___x_573_);
return v___x_575_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__17(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_box(0);
v___x_593_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__16));
v___x_594_ = l_Lean_mkConst(v___x_593_, v___x_592_);
return v___x_594_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__20(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = lean_box(0);
v___x_601_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__19));
v___x_602_ = l_Lean_mkConst(v___x_601_, v___x_600_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpEq(lean_object* v_e_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = l_Lean_Expr_cleanupAnnotations(v_e_603_);
v___x_618_ = l_Lean_Expr_isApp(v___x_617_);
if (v___x_618_ == 0)
{
lean_dec_ref(v___x_617_);
goto v___jp_614_;
}
else
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = l_Lean_Expr_appFnCleanup___redArg(v___x_617_);
v___x_620_ = l_Lean_Expr_isApp(v___x_619_);
if (v___x_620_ == 0)
{
lean_dec_ref(v___x_619_);
lean_dec_ref(v___x_617_);
goto v___jp_614_;
}
else
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = l_Lean_Expr_appFnCleanup___redArg(v___x_619_);
v___x_622_ = l_Lean_Expr_isApp(v___x_621_);
if (v___x_622_ == 0)
{
lean_dec_ref(v___x_621_);
lean_dec_ref(v___x_619_);
lean_dec_ref(v___x_617_);
goto v___jp_614_;
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_623_ = l_Lean_Expr_appFnCleanup___redArg(v___x_621_);
v___x_624_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__1));
v___x_625_ = l_Lean_Expr_isConstOf(v___x_623_, v___x_624_);
if (v___x_625_ == 0)
{
lean_dec_ref(v___x_623_);
lean_dec_ref(v___x_621_);
lean_dec_ref(v___x_619_);
lean_dec_ref(v___x_617_);
goto v___jp_614_;
}
else
{
lean_object* v_arg_626_; lean_object* v_arg_627_; lean_object* v_arg_628_; lean_object* v___x_629_; 
v_arg_626_ = lean_ctor_get(v___x_617_, 1);
lean_inc_ref(v_arg_626_);
lean_dec_ref(v___x_617_);
v_arg_627_ = lean_ctor_get(v___x_619_, 1);
lean_inc_ref(v_arg_627_);
lean_dec_ref(v___x_619_);
v_arg_628_ = lean_ctor_get(v___x_621_, 1);
lean_inc_ref_n(v_arg_628_, 2);
lean_dec_ref(v___x_621_);
v___x_629_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_628_, v_a_610_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_796_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_796_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_796_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_796_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_639_ = l_Lean_Expr_cleanupAnnotations(v_a_630_);
lean_dec(v_a_630_);
v___x_640_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__2));
v___x_641_ = l_Lean_Expr_isConstOf(v___x_639_, v___x_640_);
lean_dec_ref(v___x_639_);
if (v___x_641_ == 0)
{
size_t v___x_642_; size_t v___x_643_; uint8_t v___x_644_; 
lean_del_object(v___x_632_);
v___x_642_ = lean_ptr_addr(v_arg_627_);
v___x_643_ = lean_ptr_addr(v_arg_626_);
v___x_644_ = lean_usize_dec_eq(v___x_642_, v___x_643_);
if (v___x_644_ == 0)
{
uint8_t v___x_645_; 
lean_dec_ref(v_arg_628_);
lean_dec_ref(v___x_623_);
v___x_645_ = l_Lean_Expr_isTrue(v_arg_626_);
if (v___x_645_ == 0)
{
uint8_t v___x_646_; 
v___x_646_ = l_Lean_Expr_isFalse(v_arg_626_);
lean_dec_ref(v_arg_626_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
lean_dec_ref(v_arg_627_);
v___x_647_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_647_, 0, v___x_646_);
lean_ctor_set_uint8(v___x_647_, 1, v___x_646_);
v___x_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
return v___x_648_;
}
else
{
lean_object* v___x_649_; 
lean_inc_ref(v_arg_627_);
v___x_649_ = l_Lean_Meta_Sym_mkNotS(v_arg_627_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_660_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_660_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_660_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_660_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_654_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpEq___closed__5, &l_Lean_Meta_Grind_NormSym_simpEq___closed__5_once, _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__5);
v___x_655_ = l_Lean_Expr_app___override(v___x_654_, v_arg_627_);
v___x_656_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_656_, 0, v_a_650_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
lean_ctor_set_uint8(v___x_656_, sizeof(void*)*2, v___x_645_);
lean_ctor_set_uint8(v___x_656_, sizeof(void*)*2 + 1, v___x_645_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_656_);
v___x_658_ = v___x_652_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec_ref(v_arg_627_);
v_a_661_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_649_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_649_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
lean_dec_ref(v_arg_626_);
v___x_669_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpEq___closed__8, &l_Lean_Meta_Grind_NormSym_simpEq___closed__8_once, _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__8);
lean_inc_ref(v_arg_627_);
v___x_670_ = l_Lean_Expr_app___override(v___x_669_, v_arg_627_);
v___x_671_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_671_, 0, v_arg_627_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
lean_ctor_set_uint8(v___x_671_, sizeof(void*)*2, v___x_625_);
lean_ctor_set_uint8(v___x_671_, sizeof(void*)*2 + 1, v___x_644_);
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
else
{
lean_object* v___x_673_; 
lean_dec_ref(v_arg_626_);
v___x_673_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_607_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_686_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_686_ == 0)
{
v___x_676_ = v___x_673_;
v_isShared_677_ = v_isSharedCheck_686_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_686_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_684_; 
v___x_678_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__10));
v___x_679_ = l_Lean_Expr_constLevels_x21(v___x_623_);
lean_dec_ref(v___x_623_);
v___x_680_ = l_Lean_mkConst(v___x_678_, v___x_679_);
v___x_681_ = l_Lean_mkAppB(v___x_680_, v_arg_628_, v_arg_627_);
v___x_682_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_682_, 0, v_a_674_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
lean_ctor_set_uint8(v___x_682_, sizeof(void*)*2, v___x_625_);
lean_ctor_set_uint8(v___x_682_, sizeof(void*)*2 + 1, v___x_641_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_682_);
v___x_684_ = v___x_676_;
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
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v___x_623_);
v_a_687_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_673_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_673_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
else
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_Expr_getAppFn(v_arg_626_);
if (lean_obj_tag(v___x_695_) == 4)
{
lean_object* v_declName_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v_declName_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_declName_696_);
lean_dec_ref_known(v___x_695_, 2);
v___x_697_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__12));
v___x_698_ = lean_name_eq(v_declName_696_, v___x_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_699_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__14));
v___x_700_ = lean_name_eq(v_declName_696_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_722_; 
lean_del_object(v___x_632_);
v___x_722_ = l_Lean_Expr_getAppFn(v_arg_627_);
if (lean_obj_tag(v___x_722_) == 4)
{
lean_object* v_declName_723_; uint8_t v___x_724_; 
v_declName_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_declName_723_);
lean_dec_ref_known(v___x_722_, 2);
v___x_724_ = lean_name_eq(v_declName_723_, v___x_697_);
if (v___x_724_ == 0)
{
uint8_t v___x_725_; 
v___x_725_ = lean_name_eq(v_declName_723_, v___x_699_);
if (v___x_725_ == 0)
{
uint8_t v___x_788_; 
v___x_788_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(v_declName_723_);
lean_dec(v_declName_723_);
if (v___x_788_ == 0)
{
uint8_t v___x_789_; 
v___x_789_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isBoolEqTarget(v_declName_696_);
lean_dec(v_declName_696_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; lean_object* v___x_791_; 
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_626_);
lean_dec_ref(v___x_623_);
v___x_790_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_790_, 0, v___x_789_);
lean_ctor_set_uint8(v___x_790_, 1, v___x_789_);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
return v___x_791_;
}
else
{
goto v___jp_726_;
}
}
else
{
lean_dec(v_declName_696_);
goto v___jp_726_;
}
}
else
{
lean_dec(v_declName_723_);
lean_dec(v_declName_696_);
goto v___jp_701_;
}
v___jp_726_:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_607_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___x_727_, 1);
v___x_729_ = lean_box(0);
v___x_730_ = l_Lean_Meta_Sym_Internal_mkSortS___at___00Lean_Meta_Grind_NormSym_simpEq_spec__1___redArg(v___x_729_, v_a_608_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_732_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
lean_dec_ref_known(v___x_730_, 1);
lean_inc(v_a_728_);
lean_inc_ref(v_arg_627_);
lean_inc_ref(v_arg_628_);
lean_inc_ref(v___x_623_);
v___x_732_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v___x_623_, v_arg_628_, v_arg_627_, v_a_728_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v___x_732_, 1);
lean_inc_ref(v_arg_626_);
lean_inc_ref(v___x_623_);
v___x_734_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v___x_623_, v_arg_628_, v_arg_626_, v_a_728_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_736_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
v___x_736_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v___x_623_, v_a_731_, v_a_733_, v_a_735_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_747_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_747_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_747_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_747_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_741_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpEq___closed__20, &l_Lean_Meta_Grind_NormSym_simpEq___closed__20_once, _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__20);
v___x_742_ = l_Lean_mkAppB(v___x_741_, v_arg_627_, v_arg_626_);
v___x_743_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_743_, 0, v_a_737_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
lean_ctor_set_uint8(v___x_743_, sizeof(void*)*2, v___x_725_);
lean_ctor_set_uint8(v___x_743_, sizeof(void*)*2 + 1, v___x_725_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_743_);
v___x_745_ = v___x_739_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_626_);
v_a_748_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_736_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_736_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v_a_733_);
lean_dec(v_a_731_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_626_);
lean_dec_ref(v___x_623_);
v_a_756_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_734_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_734_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec(v_a_731_);
lean_dec(v_a_728_);
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_626_);
lean_dec_ref(v___x_623_);
v_a_764_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_732_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_732_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec(v_a_728_);
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_626_);
lean_dec_ref(v___x_623_);
v_a_772_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_730_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_730_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_787_; 
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_626_);
lean_dec_ref(v___x_623_);
v_a_780_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_787_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_787_ == 0)
{
v___x_782_ = v___x_727_;
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_727_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_787_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_780_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
else
{
lean_dec(v_declName_723_);
lean_dec(v_declName_696_);
goto v___jp_701_;
}
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; 
lean_dec_ref(v___x_722_);
lean_dec(v_declName_696_);
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_626_);
lean_dec_ref(v___x_623_);
v___x_792_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_792_, 0, v___x_700_);
lean_ctor_set_uint8(v___x_792_, 1, v___x_700_);
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
return v___x_793_;
}
}
else
{
lean_dec(v_declName_696_);
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_626_);
lean_dec_ref(v___x_623_);
goto v___jp_634_;
}
v___jp_701_:
{
lean_object* v___x_702_; 
lean_inc_ref(v_arg_627_);
lean_inc_ref(v_arg_626_);
v___x_702_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v___x_623_, v_arg_628_, v_arg_626_, v_arg_627_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_713_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_713_ == 0)
{
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_713_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_713_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_707_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpEq___closed__17, &l_Lean_Meta_Grind_NormSym_simpEq___closed__17_once, _init_l_Lean_Meta_Grind_NormSym_simpEq___closed__17);
v___x_708_ = l_Lean_mkAppB(v___x_707_, v_arg_627_, v_arg_626_);
v___x_709_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_709_, 0, v_a_703_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
lean_ctor_set_uint8(v___x_709_, sizeof(void*)*2, v___x_700_);
lean_ctor_set_uint8(v___x_709_, sizeof(void*)*2 + 1, v___x_700_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_709_);
v___x_711_ = v___x_705_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_626_);
v_a_714_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_702_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_702_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
}
else
{
lean_dec(v_declName_696_);
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_626_);
lean_dec_ref(v___x_623_);
goto v___jp_634_;
}
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; 
lean_dec_ref(v___x_695_);
lean_del_object(v___x_632_);
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_626_);
lean_dec_ref(v___x_623_);
v___x_794_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
return v___x_795_;
}
}
v___jp_634_:
{
lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_635_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v___x_635_);
v___x_637_ = v___x_632_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_635_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec_ref(v_arg_628_);
lean_dec_ref(v_arg_627_);
lean_dec_ref(v_arg_626_);
lean_dec_ref(v___x_623_);
v_a_797_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_629_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_629_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
}
}
}
v___jp_614_:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
return v___x_616_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpEq___boxed(lean_object* v_e_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_Meta_Grind_NormSym_simpEq(v_e_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_e_805_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0(lean_object* v_f_817_, lean_object* v_a_u2081_818_, lean_object* v_a_u2082_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___redArg(v_f_817_, v_a_u2081_818_, v_a_u2082_819_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___boxed(lean_object* v_f_831_, lean_object* v_a_u2081_832_, lean_object* v_a_u2082_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0(v_f_831_, v_a_u2081_832_, v_a_u2082_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___redArg(lean_object* v_declName_845_, lean_object* v_us_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = l_Lean_Expr_const___override(v_declName_845_, v_us_846_);
v___x_850_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_849_, v___y_847_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___redArg___boxed(lean_object* v_declName_851_, lean_object* v_us_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___redArg(v_declName_851_, v_us_852_, v___y_853_);
lean_dec(v___y_853_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0(lean_object* v_declName_856_, lean_object* v_us_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___redArg(v_declName_856_, v_us_857_, v___y_862_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___boxed(lean_object* v_declName_869_, lean_object* v_us_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0(v_declName_869_, v_us_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1_spec__1(lean_object* v_f_882_, lean_object* v_a_u2081_883_, lean_object* v_a_u2082_884_, lean_object* v_a_u2083_885_, lean_object* v_a_u2084_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v_f_882_, v_a_u2081_883_, v_a_u2082_884_, v_a_u2083_885_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_899_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_897_, 1);
v___x_899_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(v_a_898_, v_a_u2084_886_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
return v___x_899_;
}
else
{
lean_dec_ref(v_a_u2084_886_);
return v___x_897_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1_spec__1___boxed(lean_object* v_f_900_, lean_object* v_a_u2081_901_, lean_object* v_a_u2082_902_, lean_object* v_a_u2083_903_, lean_object* v_a_u2084_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1_spec__1(v_f_900_, v_a_u2081_901_, v_a_u2082_902_, v_a_u2083_903_, v_a_u2084_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1(lean_object* v_f_916_, lean_object* v_a_u2081_917_, lean_object* v_a_u2082_918_, lean_object* v_a_u2083_919_, lean_object* v_a_u2084_920_, lean_object* v_a_u2085_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1_spec__1(v_f_916_, v_a_u2081_917_, v_a_u2082_918_, v_a_u2083_919_, v_a_u2084_920_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_934_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_932_, 1);
v___x_934_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(v_a_933_, v_a_u2085_921_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
return v___x_934_;
}
else
{
lean_dec_ref(v_a_u2085_921_);
return v___x_932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1___boxed(lean_object* v_f_935_, lean_object* v_a_u2081_936_, lean_object* v_a_u2082_937_, lean_object* v_a_u2083_938_, lean_object* v_a_u2084_939_, lean_object* v_a_u2085_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1(v_f_935_, v_a_u2081_936_, v_a_u2082_937_, v_a_u2083_938_, v_a_u2084_939_, v_a_u2085_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpDIte(lean_object* v_e_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_975_ = l_Lean_Expr_cleanupAnnotations(v_e_961_);
v___x_976_ = l_Lean_Expr_isApp(v___x_975_);
if (v___x_976_ == 0)
{
lean_dec_ref(v___x_975_);
goto v___jp_972_;
}
else
{
lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_977_ = l_Lean_Expr_appFnCleanup___redArg(v___x_975_);
v___x_978_ = l_Lean_Expr_isApp(v___x_977_);
if (v___x_978_ == 0)
{
lean_dec_ref(v___x_977_);
lean_dec_ref(v___x_975_);
goto v___jp_972_;
}
else
{
lean_object* v___x_979_; uint8_t v___x_980_; 
v___x_979_ = l_Lean_Expr_appFnCleanup___redArg(v___x_977_);
v___x_980_ = l_Lean_Expr_isApp(v___x_979_);
if (v___x_980_ == 0)
{
lean_dec_ref(v___x_979_);
lean_dec_ref(v___x_977_);
lean_dec_ref(v___x_975_);
goto v___jp_972_;
}
else
{
lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_981_ = l_Lean_Expr_appFnCleanup___redArg(v___x_979_);
v___x_982_ = l_Lean_Expr_isApp(v___x_981_);
if (v___x_982_ == 0)
{
lean_dec_ref(v___x_981_);
lean_dec_ref(v___x_979_);
lean_dec_ref(v___x_977_);
lean_dec_ref(v___x_975_);
goto v___jp_972_;
}
else
{
lean_object* v___x_983_; uint8_t v___x_984_; 
v___x_983_ = l_Lean_Expr_appFnCleanup___redArg(v___x_981_);
v___x_984_ = l_Lean_Expr_isApp(v___x_983_);
if (v___x_984_ == 0)
{
lean_dec_ref(v___x_983_);
lean_dec_ref(v___x_981_);
lean_dec_ref(v___x_979_);
lean_dec_ref(v___x_977_);
lean_dec_ref(v___x_975_);
goto v___jp_972_;
}
else
{
lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_985_ = l_Lean_Expr_appFnCleanup___redArg(v___x_983_);
v___x_986_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpDIte___closed__1));
v___x_987_ = l_Lean_Expr_isConstOf(v___x_985_, v___x_986_);
if (v___x_987_ == 0)
{
lean_dec_ref(v___x_985_);
lean_dec_ref(v___x_983_);
lean_dec_ref(v___x_981_);
lean_dec_ref(v___x_979_);
lean_dec_ref(v___x_977_);
lean_dec_ref(v___x_975_);
goto v___jp_972_;
}
else
{
lean_object* v_arg_988_; 
v_arg_988_ = lean_ctor_get(v___x_977_, 1);
lean_inc_ref(v_arg_988_);
lean_dec_ref(v___x_977_);
if (lean_obj_tag(v_arg_988_) == 6)
{
lean_object* v_body_989_; uint8_t v___x_990_; 
v_body_989_ = lean_ctor_get(v_arg_988_, 2);
lean_inc_ref(v_body_989_);
lean_dec_ref_known(v_arg_988_, 3);
v___x_990_ = l_Lean_Expr_hasLooseBVars(v_body_989_);
if (v___x_990_ == 0)
{
lean_object* v_arg_991_; 
v_arg_991_ = lean_ctor_get(v___x_975_, 1);
lean_inc_ref(v_arg_991_);
lean_dec_ref(v___x_975_);
if (lean_obj_tag(v_arg_991_) == 6)
{
lean_object* v_body_992_; uint8_t v___x_993_; 
v_body_992_ = lean_ctor_get(v_arg_991_, 2);
lean_inc_ref(v_body_992_);
lean_dec_ref_known(v_arg_991_, 3);
v___x_993_ = l_Lean_Expr_hasLooseBVars(v_body_992_);
if (v___x_993_ == 0)
{
lean_object* v_arg_994_; lean_object* v_arg_995_; lean_object* v_arg_996_; lean_object* v_us_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v_arg_994_ = lean_ctor_get(v___x_979_, 1);
lean_inc_ref(v_arg_994_);
lean_dec_ref(v___x_979_);
v_arg_995_ = lean_ctor_get(v___x_981_, 1);
lean_inc_ref(v_arg_995_);
lean_dec_ref(v___x_981_);
v_arg_996_ = lean_ctor_get(v___x_983_, 1);
lean_inc_ref(v_arg_996_);
lean_dec_ref(v___x_983_);
v_us_997_ = l_Lean_Expr_constLevels_x21(v___x_985_);
lean_dec_ref(v___x_985_);
v___x_998_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpDIte___closed__3));
lean_inc(v_us_997_);
v___x_999_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___redArg(v___x_998_, v_us_997_, v_a_966_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
lean_inc_ref(v_body_992_);
lean_inc_ref(v_body_989_);
lean_inc_ref(v_arg_994_);
lean_inc_ref(v_arg_995_);
lean_inc_ref(v_arg_996_);
v___x_1001_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1(v_a_1000_, v_arg_996_, v_arg_995_, v_arg_994_, v_body_989_, v_body_992_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1013_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1013_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1013_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1006_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpDIte___closed__5));
v___x_1007_ = l_Lean_mkConst(v___x_1006_, v_us_997_);
v___x_1008_ = l_Lean_mkApp5(v___x_1007_, v_arg_995_, v_arg_996_, v_body_989_, v_body_992_, v_arg_994_);
v___x_1009_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1009_, 0, v_a_1002_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
lean_ctor_set_uint8(v___x_1009_, sizeof(void*)*2, v___x_993_);
lean_ctor_set_uint8(v___x_1009_, sizeof(void*)*2 + 1, v___x_993_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_1009_);
v___x_1011_ = v___x_1004_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec(v_us_997_);
lean_dec_ref(v_arg_996_);
lean_dec_ref(v_arg_995_);
lean_dec_ref(v_arg_994_);
lean_dec_ref(v_body_992_);
lean_dec_ref(v_body_989_);
v_a_1014_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_1001_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1001_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec(v_us_997_);
lean_dec_ref(v_arg_996_);
lean_dec_ref(v_arg_995_);
lean_dec_ref(v_arg_994_);
lean_dec_ref(v_body_992_);
lean_dec_ref(v_body_989_);
v_a_1022_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_999_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_999_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
lean_dec_ref(v_body_992_);
lean_dec_ref(v_body_989_);
lean_dec_ref(v___x_985_);
lean_dec_ref(v___x_983_);
lean_dec_ref(v___x_981_);
lean_dec_ref(v___x_979_);
v___x_1030_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1030_, 0, v___x_990_);
lean_ctor_set_uint8(v___x_1030_, 1, v___x_990_);
v___x_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
return v___x_1031_;
}
}
else
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec_ref(v_arg_991_);
lean_dec_ref(v_body_989_);
lean_dec_ref(v___x_985_);
lean_dec_ref(v___x_983_);
lean_dec_ref(v___x_981_);
lean_dec_ref(v___x_979_);
v___x_1032_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1032_, 0, v___x_990_);
lean_ctor_set_uint8(v___x_1032_, 1, v___x_990_);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
lean_dec_ref(v_body_989_);
lean_dec_ref(v___x_985_);
lean_dec_ref(v___x_983_);
lean_dec_ref(v___x_981_);
lean_dec_ref(v___x_979_);
lean_dec_ref(v___x_975_);
v___x_1034_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
return v___x_1035_;
}
}
else
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
lean_dec_ref(v_arg_988_);
lean_dec_ref(v___x_985_);
lean_dec_ref(v___x_983_);
lean_dec_ref(v___x_981_);
lean_dec_ref(v___x_979_);
lean_dec_ref(v___x_975_);
v___x_1036_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
return v___x_1037_;
}
}
}
}
}
}
}
v___jp_972_:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpDIte___boxed(lean_object* v_e_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_Meta_Grind_NormSym_simpDIte(v_e_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_);
lean_dec(v_a_1047_);
lean_dec_ref(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
lean_dec(v_a_1043_);
lean_dec_ref(v_a_1042_);
lean_dec(v_a_1041_);
lean_dec_ref(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_e_1038_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(lean_object* v_x_1050_, uint8_t v_bi_1051_, lean_object* v_t_1052_, lean_object* v_b_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v___y_1062_; lean_object* v___x_1065_; uint8_t v_debug_1066_; 
v___x_1065_ = lean_st_ref_get(v___y_1055_);
v_debug_1066_ = lean_ctor_get_uint8(v___x_1065_, sizeof(void*)*13);
lean_dec(v___x_1065_);
if (v_debug_1066_ == 0)
{
v___y_1062_ = v___y_1055_;
goto v___jp_1061_;
}
else
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1052_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v___x_1068_; 
lean_dec_ref_known(v___x_1067_, 1);
v___x_1068_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_dec_ref_known(v___x_1068_, 1);
v___y_1062_ = v___y_1055_;
goto v___jp_1061_;
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec_ref(v_b_1053_);
lean_dec_ref(v_t_1052_);
lean_dec(v_x_1050_);
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1068_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1068_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
lean_dec_ref(v_b_1053_);
lean_dec_ref(v_t_1052_);
lean_dec(v_x_1050_);
v_a_1077_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1067_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1067_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
v___jp_1061_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = l_Lean_Expr_lam___override(v_x_1050_, v_t_1052_, v_b_1053_, v_bi_1051_);
v___x_1064_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1063_, v___y_1062_);
return v___x_1064_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg___boxed(lean_object* v_x_1085_, lean_object* v_bi_1086_, lean_object* v_t_1087_, lean_object* v_b_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
uint8_t v_bi_boxed_1096_; lean_object* v_res_1097_; 
v_bi_boxed_1096_ = lean_unbox(v_bi_1086_);
v_res_1097_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_x_1085_, v_bi_boxed_1096_, v_t_1087_, v_b_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec_ref(v___y_1089_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0(lean_object* v_x_1098_, uint8_t v_bi_1099_, lean_object* v_t_1100_, lean_object* v_b_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_x_1098_, v_bi_1099_, v_t_1100_, v_b_1101_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___boxed(lean_object* v_x_1113_, lean_object* v_bi_1114_, lean_object* v_t_1115_, lean_object* v_b_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
uint8_t v_bi_boxed_1127_; lean_object* v_res_1128_; 
v_bi_boxed_1127_ = lean_unbox(v_bi_1114_);
v_res_1128_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0(v_x_1113_, v_bi_boxed_1127_, v_t_1115_, v_b_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(lean_object* v_idx_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1132_ = l_Lean_Expr_bvar___override(v_idx_1129_);
v___x_1133_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1132_, v___y_1130_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg___boxed(lean_object* v_idx_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(v_idx_1134_, v___y_1135_);
lean_dec(v___y_1135_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1(lean_object* v_idx_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(v_idx_1138_, v___y_1143_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___boxed(lean_object* v_idx_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1(v_idx_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(lean_object* v_x_1162_, uint8_t v_bi_1163_, lean_object* v_t_1164_, lean_object* v_b_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v___y_1174_; lean_object* v___x_1177_; uint8_t v_debug_1178_; 
v___x_1177_ = lean_st_ref_get(v___y_1167_);
v_debug_1178_ = lean_ctor_get_uint8(v___x_1177_, sizeof(void*)*13);
lean_dec(v___x_1177_);
if (v_debug_1178_ == 0)
{
v___y_1174_ = v___y_1167_;
goto v___jp_1173_;
}
else
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_t_1164_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v___x_1180_; 
lean_dec_ref_known(v___x_1179_, 1);
v___x_1180_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_b_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_dec_ref_known(v___x_1180_, 1);
v___y_1174_ = v___y_1167_;
goto v___jp_1173_;
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec_ref(v_b_1165_);
lean_dec_ref(v_t_1164_);
lean_dec(v_x_1162_);
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1180_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1180_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
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
lean_dec_ref(v_b_1165_);
lean_dec_ref(v_t_1164_);
lean_dec(v_x_1162_);
v_a_1189_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1179_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1179_);
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
v___jp_1173_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = l_Lean_Expr_forallE___override(v_x_1162_, v_t_1164_, v_b_1165_, v_bi_1163_);
v___x_1176_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1175_, v___y_1174_);
return v___x_1176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg___boxed(lean_object* v_x_1197_, lean_object* v_bi_1198_, lean_object* v_t_1199_, lean_object* v_b_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
uint8_t v_bi_boxed_1208_; lean_object* v_res_1209_; 
v_bi_boxed_1208_ = lean_unbox(v_bi_1198_);
v_res_1209_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_x_1197_, v_bi_boxed_1208_, v_t_1199_, v_b_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2(lean_object* v_x_1210_, uint8_t v_bi_1211_, lean_object* v_t_1212_, lean_object* v_b_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_x_1210_, v_bi_1211_, v_t_1212_, v_b_1213_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___boxed(lean_object* v_x_1225_, lean_object* v_bi_1226_, lean_object* v_t_1227_, lean_object* v_b_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
uint8_t v_bi_boxed_1239_; lean_object* v_res_1240_; 
v_bi_boxed_1239_ = lean_unbox(v_bi_1226_);
v_res_1240_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2(v_x_1225_, v_bi_boxed_1239_, v_t_1227_, v_b_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
return v_res_1240_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__6(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1254_ = lean_box(0);
v___x_1255_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__5));
v___x_1256_ = l_Lean_mkConst(v___x_1255_, v___x_1254_);
return v___x_1256_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__17(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = lean_box(0);
v___x_1275_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__16));
v___x_1276_ = l_Lean_mkConst(v___x_1275_, v___x_1274_);
return v___x_1276_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__20(void){
_start:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = lean_box(0);
v___x_1282_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__19));
v___x_1283_ = l_Lean_mkConst(v___x_1282_, v___x_1281_);
return v___x_1283_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__23(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = lean_box(0);
v___x_1289_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__22));
v___x_1290_ = l_Lean_mkConst(v___x_1289_, v___x_1288_);
return v___x_1290_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__26(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_box(0);
v___x_1297_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__25));
v___x_1298_ = l_Lean_mkConst(v___x_1297_, v___x_1296_);
return v___x_1298_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__29(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1304_ = lean_box(0);
v___x_1305_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__28));
v___x_1306_ = l_Lean_mkConst(v___x_1305_, v___x_1304_);
return v___x_1306_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__32(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = lean_box(0);
v___x_1313_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__31));
v___x_1314_ = l_Lean_mkConst(v___x_1313_, v___x_1312_);
return v___x_1314_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__39(void){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = lean_box(0);
v___x_1329_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__38));
v___x_1330_ = l_Lean_mkConst(v___x_1329_, v___x_1328_);
return v___x_1330_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__42(void){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1336_ = lean_box(0);
v___x_1337_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__41));
v___x_1338_ = l_Lean_mkConst(v___x_1337_, v___x_1336_);
return v___x_1338_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__45(void){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = lean_box(0);
v___x_1345_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__44));
v___x_1346_ = l_Lean_mkConst(v___x_1345_, v___x_1344_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_pushNot(lean_object* v_e_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; uint8_t v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; uint8_t v___y_1372_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1430_ = l_Lean_Expr_cleanupAnnotations(v_e_1347_);
v___x_1431_ = l_Lean_Expr_isApp(v___x_1430_);
if (v___x_1431_ == 0)
{
lean_dec_ref(v___x_1430_);
goto v___jp_1427_;
}
else
{
lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1432_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1430_);
v___x_1433_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__3));
v___x_1434_ = l_Lean_Expr_isConstOf(v___x_1432_, v___x_1433_);
lean_dec_ref(v___x_1432_);
if (v___x_1434_ == 0)
{
lean_dec_ref(v___x_1430_);
goto v___jp_1427_;
}
else
{
lean_object* v_arg_1435_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___x_1496_; 
v_arg_1435_ = lean_ctor_get(v___x_1430_, 1);
lean_inc_ref_n(v_arg_1435_, 2);
lean_dec_ref(v___x_1430_);
v___x_1496_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1435_, v_a_1354_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1880_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1499_ = v___x_1496_;
v_isShared_1500_ = v_isSharedCheck_1880_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1880_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1501_ = l_Lean_Expr_cleanupAnnotations(v_a_1497_);
lean_dec(v_a_1497_);
v___x_1502_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_1503_ = l_Lean_Expr_isConstOf(v___x_1501_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; uint8_t v___x_1505_; 
v___x_1504_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__10));
v___x_1505_ = l_Lean_Expr_isConstOf(v___x_1501_, v___x_1504_);
if (v___x_1505_ == 0)
{
uint8_t v___x_1506_; 
v___x_1506_ = l_Lean_Expr_isApp(v___x_1501_);
if (v___x_1506_ == 0)
{
lean_dec_ref(v___x_1501_);
lean_del_object(v___x_1499_);
v___y_1437_ = v_a_1348_;
v___y_1438_ = v_a_1349_;
v___y_1439_ = v_a_1350_;
v___y_1440_ = v_a_1351_;
v___y_1441_ = v_a_1352_;
v___y_1442_ = v_a_1353_;
v___y_1443_ = v_a_1354_;
v___y_1444_ = v_a_1355_;
v___y_1445_ = v_a_1356_;
goto v___jp_1436_;
}
else
{
lean_object* v_arg_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
v_arg_1507_ = lean_ctor_get(v___x_1501_, 1);
lean_inc_ref(v_arg_1507_);
v___x_1508_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1501_);
lean_dec_ref(v___x_1501_);
v___x_1509_ = l_Lean_Expr_isConstOf(v___x_1508_, v___x_1433_);
if (v___x_1509_ == 0)
{
uint8_t v___x_1510_; 
lean_del_object(v___x_1499_);
v___x_1510_ = l_Lean_Expr_isApp(v___x_1508_);
if (v___x_1510_ == 0)
{
lean_dec_ref(v___x_1508_);
lean_dec_ref(v_arg_1507_);
v___y_1437_ = v_a_1348_;
v___y_1438_ = v_a_1349_;
v___y_1439_ = v_a_1350_;
v___y_1440_ = v_a_1351_;
v___y_1441_ = v_a_1352_;
v___y_1442_ = v_a_1353_;
v___y_1443_ = v_a_1354_;
v___y_1444_ = v_a_1355_;
v___y_1445_ = v_a_1356_;
goto v___jp_1436_;
}
else
{
lean_object* v_arg_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v_arg_1511_ = lean_ctor_get(v___x_1508_, 1);
lean_inc_ref(v_arg_1511_);
v___x_1512_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1508_);
lean_dec_ref(v___x_1508_);
v___x_1513_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_etaReduce___closed__1));
v___x_1514_ = l_Lean_Expr_isConstOf(v___x_1512_, v___x_1513_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1515_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__12));
v___x_1516_ = l_Lean_Expr_isConstOf(v___x_1512_, v___x_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1517_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__14));
v___x_1518_ = l_Lean_Expr_isConstOf(v___x_1512_, v___x_1517_);
if (v___x_1518_ == 0)
{
uint8_t v___x_1519_; 
v___x_1519_ = l_Lean_Expr_isApp(v___x_1512_);
if (v___x_1519_ == 0)
{
lean_dec_ref(v___x_1512_);
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1507_);
v___y_1437_ = v_a_1348_;
v___y_1438_ = v_a_1349_;
v___y_1439_ = v_a_1350_;
v___y_1440_ = v_a_1351_;
v___y_1441_ = v_a_1352_;
v___y_1442_ = v_a_1353_;
v___y_1443_ = v_a_1354_;
v___y_1444_ = v_a_1355_;
v___y_1445_ = v_a_1356_;
goto v___jp_1436_;
}
else
{
lean_object* v_arg_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v_arg_1520_ = lean_ctor_get(v___x_1512_, 1);
lean_inc_ref(v_arg_1520_);
v___x_1521_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1512_);
lean_dec_ref(v___x_1512_);
v___x_1522_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__1));
v___x_1523_ = l_Lean_Expr_isConstOf(v___x_1521_, v___x_1522_);
if (v___x_1523_ == 0)
{
uint8_t v___x_1524_; 
v___x_1524_ = l_Lean_Expr_isApp(v___x_1521_);
if (v___x_1524_ == 0)
{
lean_dec_ref(v___x_1521_);
lean_dec_ref(v_arg_1520_);
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1507_);
v___y_1437_ = v_a_1348_;
v___y_1438_ = v_a_1349_;
v___y_1439_ = v_a_1350_;
v___y_1440_ = v_a_1351_;
v___y_1441_ = v_a_1352_;
v___y_1442_ = v_a_1353_;
v___y_1443_ = v_a_1354_;
v___y_1444_ = v_a_1355_;
v___y_1445_ = v_a_1356_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1525_; uint8_t v___x_1526_; 
v___x_1525_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1521_);
v___x_1526_ = l_Lean_Expr_isApp(v___x_1525_);
if (v___x_1526_ == 0)
{
lean_dec_ref(v___x_1525_);
lean_dec_ref(v___x_1521_);
lean_dec_ref(v_arg_1520_);
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1507_);
v___y_1437_ = v_a_1348_;
v___y_1438_ = v_a_1349_;
v___y_1439_ = v_a_1350_;
v___y_1440_ = v_a_1351_;
v___y_1441_ = v_a_1352_;
v___y_1442_ = v_a_1353_;
v___y_1443_ = v_a_1354_;
v___y_1444_ = v_a_1355_;
v___y_1445_ = v_a_1356_;
goto v___jp_1436_;
}
else
{
lean_object* v___x_1527_; lean_object* v___x_1528_; uint8_t v___x_1529_; 
v___x_1527_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1525_);
v___x_1528_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpDIte___closed__3));
v___x_1529_ = l_Lean_Expr_isConstOf(v___x_1527_, v___x_1528_);
if (v___x_1529_ == 0)
{
lean_dec_ref(v___x_1527_);
lean_dec_ref(v___x_1525_);
lean_dec_ref(v___x_1521_);
lean_dec_ref(v_arg_1520_);
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1507_);
v___y_1437_ = v_a_1348_;
v___y_1438_ = v_a_1349_;
v___y_1439_ = v_a_1350_;
v___y_1440_ = v_a_1351_;
v___y_1441_ = v_a_1352_;
v___y_1442_ = v_a_1353_;
v___y_1443_ = v_a_1354_;
v___y_1444_ = v_a_1355_;
v___y_1445_ = v_a_1356_;
goto v___jp_1436_;
}
else
{
lean_object* v_arg_1530_; lean_object* v_arg_1531_; lean_object* v___x_1532_; 
lean_dec_ref(v_arg_1435_);
v_arg_1530_ = lean_ctor_get(v___x_1521_, 1);
lean_inc_ref(v_arg_1530_);
lean_dec_ref(v___x_1521_);
v_arg_1531_ = lean_ctor_get(v___x_1525_, 1);
lean_inc_ref(v_arg_1531_);
lean_dec_ref(v___x_1525_);
lean_inc_ref(v_arg_1511_);
v___x_1532_ = l_Lean_Meta_Sym_mkNotS(v_arg_1511_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1534_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1532_, 1);
lean_inc_ref(v_arg_1507_);
v___x_1534_ = l_Lean_Meta_Sym_mkNotS(v_arg_1507_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v___x_1536_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1534_, 1);
lean_inc_ref(v_arg_1520_);
lean_inc_ref(v_arg_1530_);
v___x_1536_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__1(v___x_1527_, v_arg_1531_, v_arg_1530_, v_arg_1520_, v_a_1533_, v_a_1535_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1547_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1547_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1547_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; 
v___x_1541_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__17, &l_Lean_Meta_Grind_NormSym_pushNot___closed__17_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__17);
v___x_1542_ = l_Lean_mkApp4(v___x_1541_, v_arg_1530_, v_arg_1520_, v_arg_1511_, v_arg_1507_);
v___x_1543_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1543_, 0, v_a_1537_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
lean_ctor_set_uint8(v___x_1543_, sizeof(void*)*2, v___x_1523_);
lean_ctor_set_uint8(v___x_1543_, sizeof(void*)*2 + 1, v___x_1523_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v___x_1543_);
v___x_1545_ = v___x_1539_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_dec_ref(v_arg_1530_);
lean_dec_ref(v_arg_1520_);
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1507_);
v_a_1548_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1536_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1536_);
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
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v_a_1533_);
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_arg_1530_);
lean_dec_ref(v___x_1527_);
lean_dec_ref(v_arg_1520_);
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1507_);
v_a_1556_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1534_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1534_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec_ref(v_arg_1531_);
lean_dec_ref(v_arg_1530_);
lean_dec_ref(v___x_1527_);
lean_dec_ref(v_arg_1520_);
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1507_);
v_a_1564_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1532_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1532_);
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
}
}
}
else
{
uint8_t v___x_1572_; 
lean_dec_ref(v_arg_1435_);
v___x_1572_ = l_Lean_Expr_isProp(v_arg_1520_);
if (v___x_1572_ == 0)
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1507_, v_a_1354_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1647_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1576_ = v___x_1573_;
v_isShared_1577_ = v_isSharedCheck_1647_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1647_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1578_ = l_Lean_Expr_cleanupAnnotations(v_a_1574_);
lean_dec(v_a_1574_);
v___x_1579_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__14));
v___x_1580_ = l_Lean_Expr_isConstOf(v___x_1578_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1581_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__12));
v___x_1582_ = l_Lean_Expr_isConstOf(v___x_1578_, v___x_1581_);
lean_dec_ref(v___x_1578_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1585_; 
lean_dec_ref(v___x_1521_);
lean_dec_ref(v_arg_1520_);
lean_dec_ref(v_arg_1511_);
v___x_1583_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1583_, 0, v___x_1572_);
lean_ctor_set_uint8(v___x_1583_, 1, v___x_1572_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1583_);
v___x_1585_ = v___x_1576_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
else
{
lean_object* v___x_1587_; 
lean_del_object(v___x_1576_);
v___x_1587_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_1351_);
if (lean_obj_tag(v___x_1587_) == 0)
{
lean_object* v_a_1588_; lean_object* v___x_1589_; 
v_a_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v___x_1587_, 1);
lean_inc_ref(v_arg_1511_);
v___x_1589_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v___x_1521_, v_arg_1520_, v_arg_1511_, v_a_1588_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1600_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1600_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1600_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1594_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__20, &l_Lean_Meta_Grind_NormSym_pushNot___closed__20_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__20);
v___x_1595_ = l_Lean_Expr_app___override(v___x_1594_, v_arg_1511_);
v___x_1596_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1596_, 0, v_a_1590_);
lean_ctor_set(v___x_1596_, 1, v___x_1595_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*2, v___x_1572_);
lean_ctor_set_uint8(v___x_1596_, sizeof(void*)*2 + 1, v___x_1572_);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v___x_1596_);
v___x_1598_ = v___x_1592_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec_ref(v_arg_1511_);
v_a_1601_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1589_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1589_);
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
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_dec_ref(v___x_1521_);
lean_dec_ref(v_arg_1520_);
lean_dec_ref(v_arg_1511_);
v_a_1609_ = lean_ctor_get(v___x_1587_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1587_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1587_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1587_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
}
else
{
lean_object* v___x_1617_; 
lean_dec_ref(v___x_1578_);
lean_del_object(v___x_1576_);
v___x_1617_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_1351_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1619_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v___x_1617_, 1);
lean_inc_ref(v_arg_1511_);
v___x_1619_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v___x_1521_, v_arg_1520_, v_arg_1511_, v_a_1618_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1630_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1622_ = v___x_1619_;
v_isShared_1623_ = v_isSharedCheck_1630_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1619_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1630_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1624_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__23, &l_Lean_Meta_Grind_NormSym_pushNot___closed__23_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__23);
v___x_1625_ = l_Lean_Expr_app___override(v___x_1624_, v_arg_1511_);
v___x_1626_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1626_, 0, v_a_1620_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
lean_ctor_set_uint8(v___x_1626_, sizeof(void*)*2, v___x_1572_);
lean_ctor_set_uint8(v___x_1626_, sizeof(void*)*2 + 1, v___x_1572_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v___x_1626_);
v___x_1628_ = v___x_1622_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec_ref(v_arg_1511_);
v_a_1631_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1619_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1619_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec_ref(v___x_1521_);
lean_dec_ref(v_arg_1520_);
lean_dec_ref(v_arg_1511_);
v_a_1639_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1617_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1617_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
lean_dec_ref(v___x_1521_);
lean_dec_ref(v_arg_1520_);
lean_dec_ref(v_arg_1511_);
v_a_1648_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1573_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1573_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
else
{
lean_object* v___x_1656_; 
lean_inc_ref(v_arg_1507_);
v___x_1656_ = l_Lean_Meta_Sym_mkNotS(v_arg_1507_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1658_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 1);
lean_inc_ref(v_arg_1511_);
v___x_1658_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0(v___x_1521_, v_arg_1520_, v_arg_1511_, v_a_1657_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1669_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1661_ = v___x_1658_;
v_isShared_1662_ = v_isSharedCheck_1669_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1658_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1669_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1663_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__26, &l_Lean_Meta_Grind_NormSym_pushNot___closed__26_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__26);
v___x_1664_ = l_Lean_mkAppB(v___x_1663_, v_arg_1511_, v_arg_1507_);
v___x_1665_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1665_, 0, v_a_1659_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
lean_ctor_set_uint8(v___x_1665_, sizeof(void*)*2, v___x_1518_);
lean_ctor_set_uint8(v___x_1665_, sizeof(void*)*2 + 1, v___x_1518_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 0, v___x_1665_);
v___x_1667_ = v___x_1661_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1507_);
v_a_1670_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1658_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1658_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_dec_ref(v___x_1521_);
lean_dec_ref(v_arg_1520_);
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1507_);
v_a_1678_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1656_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1656_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1686_; 
lean_dec_ref(v___x_1512_);
lean_dec_ref(v_arg_1435_);
lean_inc_ref(v_arg_1511_);
v___x_1686_ = l_Lean_Meta_Sym_mkNotS(v_arg_1511_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1688_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref_known(v___x_1686_, 1);
lean_inc_ref(v_arg_1507_);
v___x_1688_ = l_Lean_Meta_Sym_mkNotS(v_arg_1507_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1690_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1689_);
lean_dec_ref_known(v___x_1688_, 1);
v___x_1690_ = l_Lean_Meta_Sym_mkOrS(v_a_1687_, v_a_1689_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1701_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1693_ = v___x_1690_;
v_isShared_1694_ = v_isSharedCheck_1701_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1690_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1701_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1695_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__29, &l_Lean_Meta_Grind_NormSym_pushNot___closed__29_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__29);
v___x_1696_ = l_Lean_mkAppB(v___x_1695_, v_arg_1511_, v_arg_1507_);
v___x_1697_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1697_, 0, v_a_1691_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
lean_ctor_set_uint8(v___x_1697_, sizeof(void*)*2, v___x_1516_);
lean_ctor_set_uint8(v___x_1697_, sizeof(void*)*2 + 1, v___x_1516_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 0, v___x_1697_);
v___x_1699_ = v___x_1693_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
else
{
lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1709_; 
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1507_);
v_a_1702_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1704_ = v___x_1690_;
v_isShared_1705_ = v_isSharedCheck_1709_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1690_);
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
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec(v_a_1687_);
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1507_);
v_a_1710_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1688_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1688_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1507_);
v_a_1718_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1686_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1686_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
else
{
lean_object* v___x_1726_; 
lean_dec_ref(v___x_1512_);
lean_dec_ref(v_arg_1435_);
lean_inc_ref(v_arg_1511_);
v___x_1726_ = l_Lean_Meta_Sym_mkNotS(v_arg_1511_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1728_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1726_, 1);
lean_inc_ref(v_arg_1507_);
v___x_1728_ = l_Lean_Meta_Sym_mkNotS(v_arg_1507_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1730_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref_known(v___x_1728_, 1);
v___x_1730_ = l_Lean_Meta_Sym_mkAndS(v_a_1727_, v_a_1729_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1741_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1733_ = v___x_1730_;
v_isShared_1734_ = v_isSharedCheck_1741_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1730_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1741_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1735_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__32, &l_Lean_Meta_Grind_NormSym_pushNot___closed__32_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__32);
v___x_1736_ = l_Lean_mkAppB(v___x_1735_, v_arg_1511_, v_arg_1507_);
v___x_1737_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1737_, 0, v_a_1731_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
lean_ctor_set_uint8(v___x_1737_, sizeof(void*)*2, v___x_1514_);
lean_ctor_set_uint8(v___x_1737_, sizeof(void*)*2 + 1, v___x_1514_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 0, v___x_1737_);
v___x_1739_ = v___x_1733_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1507_);
v_a_1742_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1730_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1730_);
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
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_dec(v_a_1727_);
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1507_);
v_a_1750_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1728_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1728_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
else
{
lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1507_);
v_a_1758_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1760_ = v___x_1726_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1726_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
lean_dec_ref(v___x_1512_);
lean_dec_ref(v_arg_1435_);
v___x_1766_ = lean_unsigned_to_nat(0u);
v___x_1767_ = l_Lean_Meta_Sym_Internal_mkBVarS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__1___redArg(v___x_1766_, v_a_1352_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1768_);
lean_dec_ref_known(v___x_1767_, 1);
v___x_1769_ = lean_unsigned_to_nat(1u);
v___x_1770_ = lean_mk_empty_array_with_capacity(v___x_1769_);
v___x_1771_ = lean_array_push(v___x_1770_, v_a_1768_);
lean_inc_ref(v_arg_1507_);
v___x_1772_ = l_Lean_Meta_Sym_betaS(v_arg_1507_, v___x_1771_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1774_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1772_, 1);
v___x_1774_ = l_Lean_Meta_Sym_mkNotS(v_a_1773_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; lean_object* v___x_1778_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref_known(v___x_1774_, 1);
v___x_1776_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__34));
v___x_1777_ = 0;
lean_inc_ref(v_arg_1511_);
v___x_1778_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v___x_1776_, v___x_1777_, v_arg_1511_, v_a_1775_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1778_) == 0)
{
lean_object* v_a_1779_; lean_object* v___x_1780_; 
v_a_1779_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_a_1779_);
lean_dec_ref_known(v___x_1778_, 1);
lean_inc_ref(v_arg_1511_);
v___x_1780_ = l_Lean_Meta_Sym_getLevel___redArg(v_arg_1511_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1794_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1783_ = v___x_1780_;
v_isShared_1784_ = v_isSharedCheck_1794_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1780_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1794_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1792_; 
v___x_1785_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__36));
v___x_1786_ = lean_box(0);
v___x_1787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1787_, 0, v_a_1781_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = l_Lean_mkConst(v___x_1785_, v___x_1787_);
v___x_1789_ = l_Lean_mkAppB(v___x_1788_, v_arg_1511_, v_arg_1507_);
v___x_1790_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1790_, 0, v_a_1779_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
lean_ctor_set_uint8(v___x_1790_, sizeof(void*)*2, v___x_1509_);
lean_ctor_set_uint8(v___x_1790_, sizeof(void*)*2 + 1, v___x_1509_);
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 0, v___x_1790_);
v___x_1792_ = v___x_1783_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1790_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec(v_a_1779_);
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1507_);
v_a_1795_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1780_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1780_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1507_);
v_a_1803_ = lean_ctor_get(v___x_1778_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1778_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1778_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1778_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1507_);
v_a_1811_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1774_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1774_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1507_);
v_a_1819_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1772_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1772_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
lean_dec_ref(v_arg_1511_);
lean_dec_ref(v_arg_1507_);
v_a_1827_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1767_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1767_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
}
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1839_; 
lean_dec_ref(v___x_1508_);
lean_dec_ref(v_arg_1435_);
v___x_1835_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__39, &l_Lean_Meta_Grind_NormSym_pushNot___closed__39_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__39);
lean_inc_ref(v_arg_1507_);
v___x_1836_ = l_Lean_Expr_app___override(v___x_1835_, v_arg_1507_);
v___x_1837_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1837_, 0, v_arg_1507_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
lean_ctor_set_uint8(v___x_1837_, sizeof(void*)*2, v___x_1505_);
lean_ctor_set_uint8(v___x_1837_, sizeof(void*)*2 + 1, v___x_1505_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v___x_1837_);
v___x_1839_ = v___x_1499_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
else
{
lean_object* v___x_1841_; 
lean_dec_ref(v___x_1501_);
lean_del_object(v___x_1499_);
lean_dec_ref(v_arg_1435_);
v___x_1841_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_1351_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1851_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1844_ = v___x_1841_;
v_isShared_1845_ = v_isSharedCheck_1851_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1851_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1846_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__42, &l_Lean_Meta_Grind_NormSym_pushNot___closed__42_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__42);
v___x_1847_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1847_, 0, v_a_1842_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*2, v___x_1503_);
lean_ctor_set_uint8(v___x_1847_, sizeof(void*)*2 + 1, v___x_1503_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1847_);
v___x_1849_ = v___x_1844_;
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
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
v_a_1852_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1841_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1841_);
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
lean_object* v___x_1860_; 
lean_dec_ref(v___x_1501_);
lean_del_object(v___x_1499_);
lean_dec_ref(v_arg_1435_);
v___x_1860_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_1351_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1871_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1871_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1871_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1865_; uint8_t v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1865_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__45, &l_Lean_Meta_Grind_NormSym_pushNot___closed__45_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__45);
v___x_1866_ = 0;
v___x_1867_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1867_, 0, v_a_1861_);
lean_ctor_set(v___x_1867_, 1, v___x_1865_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*2, v___x_1866_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*2 + 1, v___x_1866_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1867_);
v___x_1869_ = v___x_1863_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
v_a_1872_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1860_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1860_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_dec_ref(v_arg_1435_);
v_a_1881_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1496_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1496_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
v___jp_1436_:
{
if (lean_obj_tag(v_arg_1435_) == 7)
{
lean_object* v_binderName_1446_; lean_object* v_binderType_1447_; lean_object* v_body_1448_; uint8_t v_binderInfo_1449_; lean_object* v___x_1450_; 
v_binderName_1446_ = lean_ctor_get(v_arg_1435_, 0);
lean_inc(v_binderName_1446_);
v_binderType_1447_ = lean_ctor_get(v_arg_1435_, 1);
lean_inc_ref_n(v_binderType_1447_, 2);
v_body_1448_ = lean_ctor_get(v_arg_1435_, 2);
lean_inc_ref(v_body_1448_);
v_binderInfo_1449_ = lean_ctor_get_uint8(v_arg_1435_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_arg_1435_, 3);
v___x_1450_ = l_Lean_Meta_isProp(v_binderType_1447_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; uint8_t v___x_1452_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___x_1450_, 1);
v___x_1452_ = l_Lean_Expr_hasLooseBVars(v_body_1448_);
if (v___x_1452_ == 0)
{
uint8_t v___x_1453_; 
v___x_1453_ = lean_unbox(v_a_1451_);
if (v___x_1453_ == 0)
{
uint8_t v___x_1454_; 
v___x_1454_ = lean_unbox(v_a_1451_);
lean_dec(v_a_1451_);
v___y_1359_ = v___y_1443_;
v___y_1360_ = v___y_1437_;
v___y_1361_ = v___y_1438_;
v___y_1362_ = v___y_1442_;
v___y_1363_ = v_binderInfo_1449_;
v___y_1364_ = v___y_1445_;
v___y_1365_ = v___y_1439_;
v___y_1366_ = v___y_1444_;
v___y_1367_ = v_binderType_1447_;
v___y_1368_ = v_body_1448_;
v___y_1369_ = v___y_1441_;
v___y_1370_ = v_binderName_1446_;
v___y_1371_ = v___y_1440_;
v___y_1372_ = v___x_1454_;
goto v___jp_1358_;
}
else
{
lean_object* v___x_1455_; 
lean_dec(v_a_1451_);
lean_dec(v_binderName_1446_);
lean_inc_ref(v_body_1448_);
v___x_1455_ = l_Lean_Meta_Sym_mkNotS(v_body_1448_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1457_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1455_, 1);
lean_inc_ref(v_binderType_1447_);
v___x_1457_ = l_Lean_Meta_Sym_mkAndS(v_binderType_1447_, v_a_1456_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1468_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1468_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1468_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1462_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_pushNot___closed__6, &l_Lean_Meta_Grind_NormSym_pushNot___closed__6_once, _init_l_Lean_Meta_Grind_NormSym_pushNot___closed__6);
v___x_1463_ = l_Lean_mkAppB(v___x_1462_, v_binderType_1447_, v_body_1448_);
v___x_1464_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1464_, 0, v_a_1458_);
lean_ctor_set(v___x_1464_, 1, v___x_1463_);
lean_ctor_set_uint8(v___x_1464_, sizeof(void*)*2, v___x_1452_);
lean_ctor_set_uint8(v___x_1464_, sizeof(void*)*2 + 1, v___x_1452_);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1464_);
v___x_1466_ = v___x_1460_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec_ref(v_body_1448_);
lean_dec_ref(v_binderType_1447_);
v_a_1469_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1457_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1457_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
else
{
lean_object* v_a_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
lean_dec_ref(v_body_1448_);
lean_dec_ref(v_binderType_1447_);
v_a_1477_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1484_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1484_ == 0)
{
v___x_1479_ = v___x_1455_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_a_1477_);
lean_dec(v___x_1455_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_a_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
}
else
{
uint8_t v___x_1485_; 
lean_dec(v_a_1451_);
v___x_1485_ = 0;
v___y_1359_ = v___y_1443_;
v___y_1360_ = v___y_1437_;
v___y_1361_ = v___y_1438_;
v___y_1362_ = v___y_1442_;
v___y_1363_ = v_binderInfo_1449_;
v___y_1364_ = v___y_1445_;
v___y_1365_ = v___y_1439_;
v___y_1366_ = v___y_1444_;
v___y_1367_ = v_binderType_1447_;
v___y_1368_ = v_body_1448_;
v___y_1369_ = v___y_1441_;
v___y_1370_ = v_binderName_1446_;
v___y_1371_ = v___y_1440_;
v___y_1372_ = v___x_1485_;
goto v___jp_1358_;
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec_ref(v_body_1448_);
lean_dec_ref(v_binderType_1447_);
lean_dec(v_binderName_1446_);
v_a_1486_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1450_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1450_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
else
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
lean_dec_ref(v_arg_1435_);
v___x_1494_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
return v___x_1495_;
}
}
}
}
v___jp_1358_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_inc_ref(v___y_1368_);
lean_inc_ref(v___y_1367_);
lean_inc(v___y_1370_);
v___x_1373_ = l_Lean_mkLambda(v___y_1370_, v___y_1363_, v___y_1367_, v___y_1368_);
v___x_1374_ = l_Lean_Meta_Sym_mkNotS(v___y_1368_, v___y_1371_, v___y_1369_, v___y_1362_, v___y_1359_, v___y_1366_, v___y_1364_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1376_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
lean_inc_ref(v___y_1367_);
v___x_1376_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v___y_1370_, v___y_1363_, v___y_1367_, v_a_1375_, v___y_1371_, v___y_1369_, v___y_1362_, v___y_1359_, v___y_1366_, v___y_1364_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1378_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_a_1377_);
lean_dec_ref_known(v___x_1376_, 1);
lean_inc_ref(v___y_1367_);
v___x_1378_ = l_Lean_Meta_Sym_getLevel___redArg(v___y_1367_, v___y_1369_, v___y_1362_, v___y_1359_, v___y_1366_, v___y_1364_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1380_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc_n(v_a_1379_, 2);
lean_dec_ref_known(v___x_1378_, 1);
lean_inc_ref(v___y_1367_);
v___x_1380_ = l_Lean_Meta_Sym_mkExistsS(v_a_1379_, v___y_1367_, v_a_1377_, v___y_1371_, v___y_1369_, v___y_1362_, v___y_1359_, v___y_1366_, v___y_1364_);
if (lean_obj_tag(v___x_1380_) == 0)
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1394_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1383_ = v___x_1380_;
v_isShared_1384_ = v_isSharedCheck_1394_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1380_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1394_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1385_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__1));
v___x_1386_ = lean_box(0);
v___x_1387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1387_, 0, v_a_1379_);
lean_ctor_set(v___x_1387_, 1, v___x_1386_);
v___x_1388_ = l_Lean_mkConst(v___x_1385_, v___x_1387_);
v___x_1389_ = l_Lean_mkAppB(v___x_1388_, v___y_1367_, v___x_1373_);
v___x_1390_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1390_, 0, v_a_1381_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
lean_ctor_set_uint8(v___x_1390_, sizeof(void*)*2, v___y_1372_);
lean_ctor_set_uint8(v___x_1390_, sizeof(void*)*2 + 1, v___y_1372_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 0, v___x_1390_);
v___x_1392_ = v___x_1383_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
else
{
lean_object* v_a_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1402_; 
lean_dec(v_a_1379_);
lean_dec_ref(v___x_1373_);
lean_dec_ref(v___y_1367_);
v_a_1395_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1380_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1380_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1400_; 
if (v_isShared_1398_ == 0)
{
v___x_1400_ = v___x_1397_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
lean_dec(v_a_1377_);
lean_dec_ref(v___x_1373_);
lean_dec_ref(v___y_1367_);
v_a_1403_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1378_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1378_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_dec_ref(v___x_1373_);
lean_dec_ref(v___y_1367_);
v_a_1411_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1376_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1376_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
else
{
lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1426_; 
lean_dec_ref(v___x_1373_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1367_);
v_a_1419_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1426_ == 0)
{
v___x_1421_ = v___x_1374_;
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1374_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1426_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1424_; 
if (v_isShared_1422_ == 0)
{
v___x_1424_ = v___x_1421_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_a_1419_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
v___jp_1427_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1428_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
return v___x_1429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_pushNot___boxed(lean_object* v_e_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_Meta_Grind_NormSym_pushNot(v_e_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
lean_dec(v_a_1896_);
lean_dec_ref(v_a_1895_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec_ref(v_e_1889_);
return v_res_1900_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2(void){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1906_ = lean_box(0);
v___x_1907_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__1));
v___x_1908_ = l_Lean_mkConst(v___x_1907_, v___x_1906_);
return v___x_1908_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = lean_box(0);
v___x_1915_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__4));
v___x_1916_ = l_Lean_mkConst(v___x_1915_, v___x_1914_);
return v___x_1916_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8(void){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1920_ = lean_box(0);
v___x_1921_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__7));
v___x_1922_ = l_Lean_mkConst(v___x_1921_, v___x_1920_);
return v___x_1922_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1926_ = lean_box(0);
v___x_1927_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__10));
v___x_1928_ = l_Lean_mkConst(v___x_1927_, v___x_1926_);
return v___x_1928_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14(void){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1934_ = lean_box(0);
v___x_1935_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__13));
v___x_1936_ = l_Lean_mkConst(v___x_1935_, v___x_1934_);
return v___x_1936_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17(void){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1940_ = lean_box(0);
v___x_1941_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__16));
v___x_1942_ = l_Lean_mkConst(v___x_1941_, v___x_1940_);
return v___x_1942_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20(void){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1946_ = lean_box(0);
v___x_1947_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__19));
v___x_1948_ = l_Lean_mkConst(v___x_1947_, v___x_1946_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg(lean_object* v_e_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1963_ = l_Lean_Expr_cleanupAnnotations(v_e_1949_);
v___x_1964_ = l_Lean_Expr_isApp(v___x_1963_);
if (v___x_1964_ == 0)
{
lean_dec_ref(v___x_1963_);
goto v___jp_1960_;
}
else
{
lean_object* v___x_1965_; uint8_t v___x_1966_; 
v___x_1965_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1963_);
v___x_1966_ = l_Lean_Expr_isApp(v___x_1965_);
if (v___x_1966_ == 0)
{
lean_dec_ref(v___x_1965_);
lean_dec_ref(v___x_1963_);
goto v___jp_1960_;
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; uint8_t v___x_1969_; 
v___x_1967_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1965_);
v___x_1968_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__12));
v___x_1969_ = l_Lean_Expr_isConstOf(v___x_1967_, v___x_1968_);
lean_dec_ref(v___x_1967_);
if (v___x_1969_ == 0)
{
lean_dec_ref(v___x_1965_);
lean_dec_ref(v___x_1963_);
goto v___jp_1960_;
}
else
{
lean_object* v_arg_1970_; lean_object* v_arg_1971_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___x_2089_; 
v_arg_1970_ = lean_ctor_get(v___x_1963_, 1);
lean_inc_ref(v_arg_1970_);
lean_dec_ref(v___x_1963_);
v_arg_1971_ = lean_ctor_get(v___x_1965_, 1);
lean_inc_ref_n(v_arg_1971_, 2);
lean_dec_ref(v___x_1965_);
v___x_2089_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1971_, v_a_1953_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2149_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2149_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2149_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; uint8_t v___x_2096_; 
v___x_2094_ = l_Lean_Expr_cleanupAnnotations(v_a_2090_);
lean_dec(v_a_2090_);
v___x_2095_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_2096_ = l_Lean_Expr_isConstOf(v___x_2094_, v___x_2095_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; uint8_t v___x_2098_; 
v___x_2097_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__10));
v___x_2098_ = l_Lean_Expr_isConstOf(v___x_2094_, v___x_2097_);
if (v___x_2098_ == 0)
{
uint8_t v___x_2099_; 
lean_del_object(v___x_2092_);
v___x_2099_ = l_Lean_Expr_isApp(v___x_2094_);
if (v___x_2099_ == 0)
{
lean_dec_ref(v___x_2094_);
v___y_1973_ = v_a_1950_;
v___y_1974_ = v_a_1951_;
v___y_1975_ = v_a_1952_;
v___y_1976_ = v_a_1953_;
v___y_1977_ = v_a_1954_;
v___y_1978_ = v_a_1955_;
goto v___jp_1972_;
}
else
{
lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2100_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2094_);
v___x_2101_ = l_Lean_Expr_isApp(v___x_2100_);
if (v___x_2101_ == 0)
{
lean_dec_ref(v___x_2100_);
lean_dec_ref(v___x_2094_);
v___y_1973_ = v_a_1950_;
v___y_1974_ = v_a_1951_;
v___y_1975_ = v_a_1952_;
v___y_1976_ = v_a_1953_;
v___y_1977_ = v_a_1954_;
v___y_1978_ = v_a_1955_;
goto v___jp_1972_;
}
else
{
lean_object* v___x_2102_; uint8_t v___x_2103_; 
v___x_2102_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2100_);
v___x_2103_ = l_Lean_Expr_isConstOf(v___x_2102_, v___x_1968_);
lean_dec_ref(v___x_2102_);
if (v___x_2103_ == 0)
{
lean_dec_ref(v___x_2100_);
lean_dec_ref(v___x_2094_);
v___y_1973_ = v_a_1950_;
v___y_1974_ = v_a_1951_;
v___y_1975_ = v_a_1952_;
v___y_1976_ = v_a_1953_;
v___y_1977_ = v_a_1954_;
v___y_1978_ = v_a_1955_;
goto v___jp_1972_;
}
else
{
lean_object* v_arg_2104_; lean_object* v_arg_2105_; lean_object* v___x_2106_; 
lean_dec_ref(v_arg_1971_);
v_arg_2104_ = lean_ctor_get(v___x_2094_, 1);
lean_inc_ref_n(v_arg_2104_, 2);
lean_dec_ref(v___x_2094_);
v_arg_2105_ = lean_ctor_get(v___x_2100_, 1);
lean_inc_ref(v_arg_2105_);
lean_dec_ref(v___x_2100_);
lean_inc_ref(v_arg_1970_);
v___x_2106_ = l_Lean_Meta_Sym_mkOrS(v_arg_2104_, v_arg_1970_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; lean_object* v___x_2108_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___x_2106_, 1);
lean_inc_ref(v_arg_2105_);
v___x_2108_ = l_Lean_Meta_Sym_mkOrS(v_arg_2105_, v_a_2107_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2119_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2111_ = v___x_2108_;
v_isShared_2112_ = v_isSharedCheck_2119_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2108_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2119_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2113_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__14);
v___x_2114_ = l_Lean_mkApp3(v___x_2113_, v_arg_2105_, v_arg_2104_, v_arg_1970_);
v___x_2115_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2115_, 0, v_a_2109_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*2, v___x_2098_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*2 + 1, v___x_2098_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2115_);
v___x_2117_ = v___x_2111_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_dec_ref(v_arg_2105_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_arg_1970_);
v_a_2120_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2108_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2108_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec_ref(v_arg_2105_);
lean_dec_ref(v_arg_2104_);
lean_dec_ref(v_arg_1970_);
v_a_2128_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2106_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2106_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2140_; 
lean_dec_ref(v___x_2094_);
v___x_2136_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__17);
v___x_2137_ = l_Lean_Expr_app___override(v___x_2136_, v_arg_1970_);
v___x_2138_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2138_, 0, v_arg_1971_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
lean_ctor_set_uint8(v___x_2138_, sizeof(void*)*2, v___x_2096_);
lean_ctor_set_uint8(v___x_2138_, sizeof(void*)*2 + 1, v___x_2096_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2138_);
v___x_2140_ = v___x_2092_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2147_; 
lean_dec_ref(v___x_2094_);
lean_dec_ref(v_arg_1971_);
v___x_2142_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__20);
lean_inc_ref(v_arg_1970_);
v___x_2143_ = l_Lean_Expr_app___override(v___x_2142_, v_arg_1970_);
v___x_2144_ = 0;
v___x_2145_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2145_, 0, v_arg_1970_);
lean_ctor_set(v___x_2145_, 1, v___x_2143_);
lean_ctor_set_uint8(v___x_2145_, sizeof(void*)*2, v___x_2144_);
lean_ctor_set_uint8(v___x_2145_, sizeof(void*)*2 + 1, v___x_2144_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2145_);
v___x_2147_ = v___x_2092_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_dec_ref(v_arg_1971_);
lean_dec_ref(v_arg_1970_);
v_a_2150_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2089_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2089_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
v___jp_1972_:
{
lean_object* v___x_1979_; 
lean_inc_ref(v_arg_1970_);
v___x_1979_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_1970_, v___y_1976_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2080_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_2080_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2080_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1984_ = l_Lean_Expr_cleanupAnnotations(v_a_1980_);
lean_dec(v_a_1980_);
v___x_1985_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_1986_ = l_Lean_Expr_isConstOf(v___x_1984_, v___x_1985_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1987_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__10));
v___x_1988_ = l_Lean_Expr_isConstOf(v___x_1984_, v___x_1987_);
if (v___x_1988_ == 0)
{
uint8_t v___x_1989_; 
lean_dec_ref(v_arg_1970_);
v___x_1989_ = l_Lean_Expr_isApp(v___x_1984_);
if (v___x_1989_ == 0)
{
lean_dec_ref(v___x_1984_);
lean_del_object(v___x_1982_);
lean_dec_ref(v_arg_1971_);
goto v___jp_1957_;
}
else
{
lean_object* v___x_1990_; uint8_t v___x_1991_; 
v___x_1990_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1984_);
v___x_1991_ = l_Lean_Expr_isApp(v___x_1990_);
if (v___x_1991_ == 0)
{
lean_dec_ref(v___x_1990_);
lean_dec_ref(v___x_1984_);
lean_del_object(v___x_1982_);
lean_dec_ref(v_arg_1971_);
goto v___jp_1957_;
}
else
{
lean_object* v___x_1992_; uint8_t v___x_1993_; 
v___x_1992_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1990_);
v___x_1993_ = l_Lean_Expr_isConstOf(v___x_1992_, v___x_1968_);
lean_dec_ref(v___x_1992_);
if (v___x_1993_ == 0)
{
lean_dec_ref(v___x_1990_);
lean_dec_ref(v___x_1984_);
lean_del_object(v___x_1982_);
lean_dec_ref(v_arg_1971_);
goto v___jp_1957_;
}
else
{
uint8_t v___x_1994_; 
v___x_1994_ = l_Lean_Expr_isForall(v_arg_1971_);
if (v___x_1994_ == 0)
{
lean_object* v_arg_1995_; lean_object* v_arg_1996_; uint8_t v___x_1997_; 
v_arg_1995_ = lean_ctor_get(v___x_1984_, 1);
lean_inc_ref(v_arg_1995_);
lean_dec_ref(v___x_1984_);
v_arg_1996_ = lean_ctor_get(v___x_1990_, 1);
lean_inc_ref(v_arg_1996_);
lean_dec_ref(v___x_1990_);
v___x_1997_ = l_Lean_Expr_isForall(v_arg_1996_);
if (v___x_1997_ == 0)
{
uint8_t v___x_1998_; 
v___x_1998_ = l_Lean_Expr_isForall(v_arg_1995_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
lean_dec_ref(v_arg_1996_);
lean_dec_ref(v_arg_1995_);
lean_dec_ref(v_arg_1971_);
v___x_1999_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1999_, 0, v___x_1998_);
lean_ctor_set_uint8(v___x_1999_, 1, v___x_1998_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1999_);
v___x_2001_ = v___x_1982_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
else
{
lean_object* v___x_2003_; 
lean_del_object(v___x_1982_);
lean_inc_ref(v_arg_1971_);
lean_inc_ref(v_arg_1996_);
v___x_2003_ = l_Lean_Meta_Sym_mkOrS(v_arg_1996_, v_arg_1971_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2005_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
lean_inc_ref(v_arg_1995_);
v___x_2005_ = l_Lean_Meta_Sym_mkOrS(v_arg_1995_, v_a_2004_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2016_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2008_ = v___x_2005_;
v_isShared_2009_ = v_isSharedCheck_2016_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_2005_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2016_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2010_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__2);
v___x_2011_ = l_Lean_mkApp3(v___x_2010_, v_arg_1971_, v_arg_1996_, v_arg_1995_);
v___x_2012_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2012_, 0, v_a_2006_);
lean_ctor_set(v___x_2012_, 1, v___x_2011_);
lean_ctor_set_uint8(v___x_2012_, sizeof(void*)*2, v___x_1997_);
lean_ctor_set_uint8(v___x_2012_, sizeof(void*)*2 + 1, v___x_1997_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 0, v___x_2012_);
v___x_2014_ = v___x_2008_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec_ref(v_arg_1996_);
lean_dec_ref(v_arg_1995_);
lean_dec_ref(v_arg_1971_);
v_a_2017_ = lean_ctor_get(v___x_2005_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2005_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_2005_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2005_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec_ref(v_arg_1996_);
lean_dec_ref(v_arg_1995_);
lean_dec_ref(v_arg_1971_);
v_a_2025_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2003_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2003_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
}
else
{
lean_object* v___x_2033_; 
lean_del_object(v___x_1982_);
lean_inc_ref(v_arg_1995_);
lean_inc_ref(v_arg_1971_);
v___x_2033_ = l_Lean_Meta_Sym_mkOrS(v_arg_1971_, v_arg_1995_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2035_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___x_2033_, 1);
lean_inc_ref(v_arg_1996_);
v___x_2035_ = l_Lean_Meta_Sym_mkOrS(v_arg_1996_, v_a_2034_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2046_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2038_ = v___x_2035_;
v_isShared_2039_ = v_isSharedCheck_2046_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2035_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2046_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2040_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__5);
v___x_2041_ = l_Lean_mkApp3(v___x_2040_, v_arg_1971_, v_arg_1996_, v_arg_1995_);
v___x_2042_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2042_, 0, v_a_2036_);
lean_ctor_set(v___x_2042_, 1, v___x_2041_);
lean_ctor_set_uint8(v___x_2042_, sizeof(void*)*2, v___x_1994_);
lean_ctor_set_uint8(v___x_2042_, sizeof(void*)*2 + 1, v___x_1994_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 0, v___x_2042_);
v___x_2044_ = v___x_2038_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec_ref(v_arg_1996_);
lean_dec_ref(v_arg_1995_);
lean_dec_ref(v_arg_1971_);
v_a_2047_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2035_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2035_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec_ref(v_arg_1996_);
lean_dec_ref(v_arg_1995_);
lean_dec_ref(v_arg_1971_);
v_a_2055_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2033_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2033_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
else
{
lean_object* v___x_2063_; lean_object* v___x_2065_; 
lean_dec_ref(v___x_1990_);
lean_dec_ref(v___x_1984_);
lean_dec_ref(v_arg_1971_);
v___x_2063_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2063_, 0, v___x_1988_);
lean_ctor_set_uint8(v___x_2063_, 1, v___x_1988_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_2063_);
v___x_2065_ = v___x_1982_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
}
else
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2071_; 
lean_dec_ref(v___x_1984_);
v___x_2067_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__8);
v___x_2068_ = l_Lean_Expr_app___override(v___x_2067_, v_arg_1971_);
v___x_2069_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2069_, 0, v_arg_1970_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*2, v___x_1986_);
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*2 + 1, v___x_1986_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_2069_);
v___x_2071_ = v___x_1982_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2078_; 
lean_dec_ref(v___x_1984_);
lean_dec_ref(v_arg_1970_);
v___x_2073_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11, &l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11_once, _init_l_Lean_Meta_Grind_NormSym_simpOr___redArg___closed__11);
lean_inc_ref(v_arg_1971_);
v___x_2074_ = l_Lean_Expr_app___override(v___x_2073_, v_arg_1971_);
v___x_2075_ = 0;
v___x_2076_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2076_, 0, v_arg_1971_);
lean_ctor_set(v___x_2076_, 1, v___x_2074_);
lean_ctor_set_uint8(v___x_2076_, sizeof(void*)*2, v___x_2075_);
lean_ctor_set_uint8(v___x_2076_, sizeof(void*)*2 + 1, v___x_2075_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_2076_);
v___x_2078_ = v___x_1982_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2076_);
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
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec_ref(v_arg_1971_);
lean_dec_ref(v_arg_1970_);
v_a_2081_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_1979_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_1979_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
}
}
}
v___jp_1957_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1958_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1958_);
return v___x_1959_;
}
v___jp_1960_:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1961_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
return v___x_1962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr___redArg___boxed(lean_object* v_e_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Lean_Meta_Grind_NormSym_simpOr___redArg(v_e_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
lean_dec(v_a_2164_);
lean_dec_ref(v_a_2163_);
lean_dec(v_a_2162_);
lean_dec_ref(v_a_2161_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec_ref(v_e_2158_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr(lean_object* v_e_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_, lean_object* v_a_2175_, lean_object* v_a_2176_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_Meta_Grind_NormSym_simpOr___redArg(v_e_2167_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpOr___boxed(lean_object* v_e_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Lean_Meta_Grind_NormSym_simpOr(v_e_2179_, v_a_2180_, v_a_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_a_2188_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
lean_dec(v_a_2186_);
lean_dec_ref(v_a_2185_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2183_);
lean_dec(v_a_2182_);
lean_dec_ref(v_a_2181_);
lean_dec(v_a_2180_);
lean_dec_ref(v_e_2179_);
return v_res_2190_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2191_ = lean_box(0);
v___x_2192_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_2193_ = l_Lean_mkConst(v___x_2192_, v___x_2191_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0(uint8_t v___x_2194_, uint8_t v___x_2195_, lean_object* v_h_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v___y_2208_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2217_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0, &l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0);
lean_inc_ref(v_h_2196_);
v___x_2218_ = l_Lean_Meta_mkNoConfusion(v___x_2217_, v_h_2196_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_a_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; uint8_t v___x_2223_; lean_object* v___x_2224_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v___x_2218_, 1);
v___x_2220_ = lean_unsigned_to_nat(1u);
v___x_2221_ = lean_mk_empty_array_with_capacity(v___x_2220_);
v___x_2222_ = lean_array_push(v___x_2221_, v_h_2196_);
v___x_2223_ = 1;
v___x_2224_ = l_Lean_Meta_mkLambdaFVars(v___x_2222_, v_a_2219_, v___x_2194_, v___x_2195_, v___x_2194_, v___x_2195_, v___x_2223_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
lean_dec_ref(v___x_2222_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; lean_object* v___x_2226_; uint8_t v_transparency_2227_; uint8_t v___x_2228_; uint8_t v___x_2229_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref_known(v___x_2224_, 1);
v___x_2226_ = l_Lean_Meta_Context_config(v___y_2202_);
v_transparency_2227_ = lean_ctor_get_uint8(v___x_2226_, 9);
lean_dec_ref(v___x_2226_);
v___x_2228_ = 1;
v___x_2229_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2227_, v___x_2228_);
if (v___x_2229_ == 0)
{
lean_object* v_keyedConfig_2230_; uint8_t v_trackZetaDelta_2231_; lean_object* v_zetaDeltaSet_2232_; lean_object* v_lctx_2233_; lean_object* v_localInstances_2234_; lean_object* v_defEqCtx_x3f_2235_; lean_object* v_synthPendingDepth_2236_; lean_object* v_customCanUnfoldPredicate_x3f_2237_; uint8_t v_univApprox_2238_; uint8_t v_inTypeClassResolution_2239_; uint8_t v_cacheInferType_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v_keyedConfig_2230_ = lean_ctor_get(v___y_2202_, 0);
v_trackZetaDelta_2231_ = lean_ctor_get_uint8(v___y_2202_, sizeof(void*)*7);
v_zetaDeltaSet_2232_ = lean_ctor_get(v___y_2202_, 1);
v_lctx_2233_ = lean_ctor_get(v___y_2202_, 2);
v_localInstances_2234_ = lean_ctor_get(v___y_2202_, 3);
v_defEqCtx_x3f_2235_ = lean_ctor_get(v___y_2202_, 4);
v_synthPendingDepth_2236_ = lean_ctor_get(v___y_2202_, 5);
v_customCanUnfoldPredicate_x3f_2237_ = lean_ctor_get(v___y_2202_, 6);
v_univApprox_2238_ = lean_ctor_get_uint8(v___y_2202_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2239_ = lean_ctor_get_uint8(v___y_2202_, sizeof(void*)*7 + 2);
v_cacheInferType_2240_ = lean_ctor_get_uint8(v___y_2202_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2230_);
v___x_2241_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2228_, v_keyedConfig_2230_);
lean_inc(v_customCanUnfoldPredicate_x3f_2237_);
lean_inc(v_synthPendingDepth_2236_);
lean_inc(v_defEqCtx_x3f_2235_);
lean_inc_ref(v_localInstances_2234_);
lean_inc_ref(v_lctx_2233_);
lean_inc(v_zetaDeltaSet_2232_);
v___x_2242_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
lean_ctor_set(v___x_2242_, 1, v_zetaDeltaSet_2232_);
lean_ctor_set(v___x_2242_, 2, v_lctx_2233_);
lean_ctor_set(v___x_2242_, 3, v_localInstances_2234_);
lean_ctor_set(v___x_2242_, 4, v_defEqCtx_x3f_2235_);
lean_ctor_set(v___x_2242_, 5, v_synthPendingDepth_2236_);
lean_ctor_set(v___x_2242_, 6, v_customCanUnfoldPredicate_x3f_2237_);
lean_ctor_set_uint8(v___x_2242_, sizeof(void*)*7, v_trackZetaDelta_2231_);
lean_ctor_set_uint8(v___x_2242_, sizeof(void*)*7 + 1, v_univApprox_2238_);
lean_ctor_set_uint8(v___x_2242_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2239_);
lean_ctor_set_uint8(v___x_2242_, sizeof(void*)*7 + 3, v_cacheInferType_2240_);
v___x_2243_ = l_Lean_Meta_mkEqFalse_x27(v_a_2225_, v___x_2242_, v___y_2203_, v___y_2204_, v___y_2205_);
lean_dec_ref_known(v___x_2242_, 7);
v___y_2208_ = v___x_2243_;
goto v___jp_2207_;
}
else
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Lean_Meta_mkEqFalse_x27(v_a_2225_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
v___y_2208_ = v___x_2244_;
goto v___jp_2207_;
}
}
else
{
return v___x_2224_;
}
}
else
{
lean_dec_ref(v_h_2196_);
return v___x_2218_;
}
v___jp_2207_:
{
if (lean_obj_tag(v___y_2208_) == 0)
{
return v___y_2208_;
}
else
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
v_a_2209_ = lean_ctor_get(v___y_2208_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___y_2208_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___y_2208_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___y_2208_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___boxed(lean_object* v___x_2245_, lean_object* v___x_2246_, lean_object* v_h_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
uint8_t v___x_16165__boxed_2258_; uint8_t v___x_16166__boxed_2259_; lean_object* v_res_2260_; 
v___x_16165__boxed_2258_ = lean_unbox(v___x_2245_);
v___x_16166__boxed_2259_ = lean_unbox(v___x_2246_);
v_res_2260_ = l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0(v___x_16165__boxed_2258_, v___x_16166__boxed_2259_, v_h_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0(lean_object* v_k_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v_b_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___x_2273_; 
lean_inc(v___y_2271_);
lean_inc_ref(v___y_2270_);
lean_inc(v___y_2269_);
lean_inc_ref(v___y_2268_);
lean_inc(v___y_2266_);
lean_inc_ref(v___y_2265_);
lean_inc(v___y_2264_);
lean_inc_ref(v___y_2263_);
lean_inc(v___y_2262_);
v___x_2273_ = lean_apply_11(v_k_2261_, v_b_2267_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, lean_box(0));
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v_b_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0(v_k_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v_b_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(lean_object* v_name_2287_, uint8_t v_bi_2288_, lean_object* v_type_2289_, lean_object* v_k_2290_, uint8_t v_kind_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v___f_2302_; lean_object* v___x_2303_; 
lean_inc(v___y_2296_);
lean_inc_ref(v___y_2295_);
lean_inc(v___y_2294_);
lean_inc_ref(v___y_2293_);
lean_inc(v___y_2292_);
v___f_2302_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_2302_, 0, v_k_2290_);
lean_closure_set(v___f_2302_, 1, v___y_2292_);
lean_closure_set(v___f_2302_, 2, v___y_2293_);
lean_closure_set(v___f_2302_, 3, v___y_2294_);
lean_closure_set(v___f_2302_, 4, v___y_2295_);
lean_closure_set(v___f_2302_, 5, v___y_2296_);
v___x_2303_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2287_, v_bi_2288_, v_type_2289_, v___f_2302_, v_kind_2291_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
if (lean_obj_tag(v___x_2303_) == 0)
{
return v___x_2303_;
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2303_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2303_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg___boxed(lean_object* v_name_2312_, lean_object* v_bi_2313_, lean_object* v_type_2314_, lean_object* v_k_2315_, lean_object* v_kind_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
uint8_t v_bi_boxed_2327_; uint8_t v_kind_boxed_2328_; lean_object* v_res_2329_; 
v_bi_boxed_2327_ = lean_unbox(v_bi_2313_);
v_kind_boxed_2328_ = lean_unbox(v_kind_2316_);
v_res_2329_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(v_name_2312_, v_bi_boxed_2327_, v_type_2314_, v_k_2315_, v_kind_boxed_2328_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(lean_object* v_name_2330_, lean_object* v_type_2331_, lean_object* v_k_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
uint8_t v___x_2343_; uint8_t v___x_2344_; lean_object* v___x_2345_; 
v___x_2343_ = 0;
v___x_2344_ = 0;
v___x_2345_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(v_name_2330_, v___x_2343_, v_type_2331_, v_k_2332_, v___x_2344_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg___boxed(lean_object* v_name_2346_, lean_object* v_type_2347_, lean_object* v_k_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_name_2346_, v_type_2347_, v_k_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq(lean_object* v_e_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v___x_2377_; uint8_t v___x_2378_; 
v___x_2377_ = l_Lean_Expr_cleanupAnnotations(v_e_2363_);
v___x_2378_ = l_Lean_Expr_isApp(v___x_2377_);
if (v___x_2378_ == 0)
{
lean_dec_ref(v___x_2377_);
lean_dec_ref(v_e_2363_);
goto v___jp_2374_;
}
else
{
lean_object* v___x_2379_; uint8_t v___x_2380_; 
v___x_2379_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2377_);
v___x_2380_ = l_Lean_Expr_isApp(v___x_2379_);
if (v___x_2380_ == 0)
{
lean_dec_ref(v___x_2379_);
lean_dec_ref(v___x_2377_);
lean_dec_ref(v_e_2363_);
goto v___jp_2374_;
}
else
{
lean_object* v___x_2381_; uint8_t v___x_2382_; 
v___x_2381_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2379_);
v___x_2382_ = l_Lean_Expr_isApp(v___x_2381_);
if (v___x_2382_ == 0)
{
lean_dec_ref(v___x_2381_);
lean_dec_ref(v___x_2379_);
lean_dec_ref(v___x_2377_);
lean_dec_ref(v_e_2363_);
goto v___jp_2374_;
}
else
{
lean_object* v___x_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; 
v___x_2383_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2381_);
lean_dec_ref(v___x_2381_);
v___x_2384_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpEq___closed__1));
v___x_2385_ = l_Lean_Expr_isConstOf(v___x_2383_, v___x_2384_);
lean_dec_ref(v___x_2383_);
if (v___x_2385_ == 0)
{
lean_dec_ref(v___x_2379_);
lean_dec_ref(v___x_2377_);
lean_dec_ref(v_e_2363_);
goto v___jp_2374_;
}
else
{
lean_object* v_arg_2386_; lean_object* v_arg_2387_; lean_object* v___x_2388_; 
v_arg_2386_ = lean_ctor_get(v___x_2377_, 1);
lean_inc_ref(v_arg_2386_);
lean_dec_ref(v___x_2377_);
v_arg_2387_ = lean_ctor_get(v___x_2379_, 1);
lean_inc_ref(v_arg_2387_);
lean_dec_ref(v___x_2379_);
v___x_2388_ = l_Lean_Meta_isConstructorApp_x3f(v_arg_2387_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2458_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2391_ = v___x_2388_;
v_isShared_2392_ = v_isSharedCheck_2458_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2388_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2458_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
if (lean_obj_tag(v_a_2389_) == 1)
{
lean_object* v_val_2393_; lean_object* v___x_2394_; 
lean_del_object(v___x_2391_);
v_val_2393_ = lean_ctor_get(v_a_2389_, 0);
lean_inc(v_val_2393_);
lean_dec_ref_known(v_a_2389_, 1);
v___x_2394_ = l_Lean_Meta_isConstructorApp_x3f(v_arg_2386_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2445_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2397_ = v___x_2394_;
v_isShared_2398_ = v_isSharedCheck_2445_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2445_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
if (lean_obj_tag(v_a_2395_) == 1)
{
lean_object* v_toConstantVal_2399_; lean_object* v_val_2400_; lean_object* v_toConstantVal_2401_; lean_object* v_name_2402_; lean_object* v_name_2403_; uint8_t v___x_2404_; 
v_toConstantVal_2399_ = lean_ctor_get(v_val_2393_, 0);
lean_inc_ref(v_toConstantVal_2399_);
lean_dec(v_val_2393_);
v_val_2400_ = lean_ctor_get(v_a_2395_, 0);
lean_inc(v_val_2400_);
lean_dec_ref_known(v_a_2395_, 1);
v_toConstantVal_2401_ = lean_ctor_get(v_val_2400_, 0);
lean_inc_ref(v_toConstantVal_2401_);
lean_dec(v_val_2400_);
v_name_2402_ = lean_ctor_get(v_toConstantVal_2399_, 0);
lean_inc(v_name_2402_);
lean_dec_ref(v_toConstantVal_2399_);
v_name_2403_ = lean_ctor_get(v_toConstantVal_2401_, 0);
lean_inc(v_name_2403_);
lean_dec_ref(v_toConstantVal_2401_);
v___x_2404_ = lean_name_eq(v_name_2402_, v_name_2403_);
lean_dec(v_name_2403_);
lean_dec(v_name_2402_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___f_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
lean_del_object(v___x_2397_);
v___x_2405_ = lean_box(v___x_2404_);
v___x_2406_ = lean_box(v___x_2385_);
v___f_2407_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___boxed), 13, 2);
lean_closure_set(v___f_2407_, 0, v___x_2405_);
lean_closure_set(v___f_2407_, 1, v___x_2406_);
v___x_2408_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_reduceCtorEq___closed__1));
v___x_2409_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v___x_2408_, v_e_2363_, v___f_2407_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2411_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref_known(v___x_2409_, 1);
v___x_2411_ = l_Lean_Meta_Sym_getFalseExpr___redArg(v_a_2367_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2420_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2414_ = v___x_2411_;
v_isShared_2415_ = v_isSharedCheck_2420_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2411_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2420_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2416_; lean_object* v___x_2418_; 
v___x_2416_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2416_, 0, v_a_2412_);
lean_ctor_set(v___x_2416_, 1, v_a_2410_);
lean_ctor_set_uint8(v___x_2416_, sizeof(void*)*2, v___x_2385_);
lean_ctor_set_uint8(v___x_2416_, sizeof(void*)*2 + 1, v___x_2404_);
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 0, v___x_2416_);
v___x_2418_ = v___x_2414_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2416_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
lean_dec(v_a_2410_);
v_a_2421_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2411_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2411_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
v_a_2429_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2409_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2409_);
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
lean_object* v___x_2437_; lean_object* v___x_2439_; 
lean_dec_ref(v_e_2363_);
v___x_2437_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2437_);
v___x_2439_ = v___x_2397_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2437_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
else
{
lean_object* v___x_2441_; lean_object* v___x_2443_; 
lean_dec(v_a_2395_);
lean_dec(v_val_2393_);
lean_dec_ref(v_e_2363_);
v___x_2441_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2441_);
v___x_2443_ = v___x_2397_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2441_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec(v_val_2393_);
lean_dec_ref(v_e_2363_);
v_a_2446_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2394_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2394_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
else
{
lean_object* v___x_2454_; lean_object* v___x_2456_; 
lean_dec(v_a_2389_);
lean_dec_ref(v_arg_2386_);
lean_dec_ref(v_e_2363_);
v___x_2454_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 0, v___x_2454_);
v___x_2456_ = v___x_2391_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2454_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
lean_dec_ref(v_arg_2386_);
lean_dec_ref(v_e_2363_);
v_a_2459_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2388_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2388_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
}
}
v___jp_2374_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
return v___x_2376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_reduceCtorEq___boxed(lean_object* v_e_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Lean_Meta_Grind_NormSym_reduceCtorEq(v_e_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
lean_dec(v_a_2470_);
lean_dec_ref(v_a_2469_);
lean_dec(v_a_2468_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0(lean_object* v_00_u03b1_2479_, lean_object* v_name_2480_, uint8_t v_bi_2481_, lean_object* v_type_2482_, lean_object* v_k_2483_, uint8_t v_kind_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___redArg(v_name_2480_, v_bi_2481_, v_type_2482_, v_k_2483_, v_kind_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2496_, lean_object* v_name_2497_, lean_object* v_bi_2498_, lean_object* v_type_2499_, lean_object* v_k_2500_, lean_object* v_kind_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
uint8_t v_bi_boxed_2512_; uint8_t v_kind_boxed_2513_; lean_object* v_res_2514_; 
v_bi_boxed_2512_ = lean_unbox(v_bi_2498_);
v_kind_boxed_2513_ = lean_unbox(v_kind_2501_);
v_res_2514_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0(v_00_u03b1_2496_, v_name_2497_, v_bi_boxed_2512_, v_type_2499_, v_k_2500_, v_kind_boxed_2513_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0(lean_object* v_00_u03b1_2515_, lean_object* v_name_2516_, lean_object* v_type_2517_, lean_object* v_k_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_name_2516_, v_type_2517_, v_k_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___boxed(lean_object* v_00_u03b1_2530_, lean_object* v_name_2531_, lean_object* v_type_2532_, lean_object* v_k_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0(v_00_u03b1_2530_, v_name_2531_, v_type_2532_, v_k_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(lean_object* v_e_2545_){
_start:
{
if (lean_obj_tag(v_e_2545_) == 7)
{
lean_object* v_binderName_2546_; lean_object* v_binderType_2547_; lean_object* v_body_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v_binderName_2546_ = lean_ctor_get(v_e_2545_, 0);
v_binderType_2547_ = lean_ctor_get(v_e_2545_, 1);
v_body_2548_ = lean_ctor_get(v_e_2545_, 2);
lean_inc_ref(v_body_2548_);
lean_inc_ref(v_binderType_2547_);
v___x_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2549_, 0, v_binderType_2547_);
lean_ctor_set(v___x_2549_, 1, v_body_2548_);
lean_inc(v_binderName_2546_);
v___x_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2550_, 0, v_binderName_2546_);
lean_ctor_set(v___x_2550_, 1, v___x_2549_);
v___x_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
return v___x_2551_;
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; 
v___x_2552_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__3));
v___x_2553_ = lean_unsigned_to_nat(1u);
v___x_2554_ = l_Lean_Expr_isAppOfArity(v_e_2545_, v___x_2552_, v___x_2553_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_box(0);
return v___x_2555_;
}
else
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2556_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__34));
v___x_2557_ = l_Lean_Expr_appArg_x21(v_e_2545_);
v___x_2558_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0, &l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_NormSym_reduceCtorEq___lam__0___closed__0);
v___x_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2557_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2556_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
v___x_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
return v___x_2561_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f___boxed(lean_object* v_e_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(v_e_2562_);
lean_dec_ref(v_e_2562_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0(lean_object* v_fst_2564_, lean_object* v_a_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = lean_expr_instantiate1(v_fst_2564_, v_a_2565_);
v___x_2577_ = l_Lean_Meta_getLevel(v___x_2576_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0___boxed(lean_object* v_fst_2578_, lean_object* v_a_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0(v_fst_2578_, v_a_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec_ref(v_a_2579_);
lean_dec_ref(v_fst_2578_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f(lean_object* v_e_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_){
_start:
{
if (lean_obj_tag(v_e_2601_) == 7)
{
lean_object* v_binderName_2615_; lean_object* v_binderType_2616_; lean_object* v_body_2617_; uint8_t v_binderInfo_2618_; lean_object* v___x_2619_; uint8_t v___x_2620_; 
v_binderName_2615_ = lean_ctor_get(v_e_2601_, 0);
lean_inc(v_binderName_2615_);
v_binderType_2616_ = lean_ctor_get(v_e_2601_, 1);
lean_inc_ref(v_binderType_2616_);
v_body_2617_ = lean_ctor_get(v_e_2601_, 2);
lean_inc_ref(v_body_2617_);
v_binderInfo_2618_ = lean_ctor_get_uint8(v_e_2601_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2601_, 3);
v___x_2619_ = l_Lean_Expr_cleanupAnnotations(v_body_2617_);
lean_dec_ref(v_body_2617_);
v___x_2620_ = l_Lean_Expr_isApp(v___x_2619_);
if (v___x_2620_ == 0)
{
lean_dec_ref(v___x_2619_);
lean_dec_ref(v_binderType_2616_);
lean_dec(v_binderName_2615_);
goto v___jp_2612_;
}
else
{
lean_object* v___x_2621_; uint8_t v___x_2622_; 
v___x_2621_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2619_);
v___x_2622_ = l_Lean_Expr_isApp(v___x_2621_);
if (v___x_2622_ == 0)
{
lean_dec_ref(v___x_2621_);
lean_dec_ref(v___x_2619_);
lean_dec_ref(v_binderType_2616_);
lean_dec(v_binderName_2615_);
goto v___jp_2612_;
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; 
v___x_2623_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2621_);
v___x_2624_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__12));
v___x_2625_ = l_Lean_Expr_isConstOf(v___x_2623_, v___x_2624_);
lean_dec_ref(v___x_2623_);
if (v___x_2625_ == 0)
{
lean_dec_ref(v___x_2621_);
lean_dec_ref(v___x_2619_);
lean_dec_ref(v_binderType_2616_);
lean_dec(v_binderName_2615_);
goto v___jp_2612_;
}
else
{
lean_object* v_arg_2626_; lean_object* v_arg_2627_; lean_object* v___x_2628_; 
v_arg_2626_ = lean_ctor_get(v___x_2619_, 1);
lean_inc_ref(v_arg_2626_);
lean_dec_ref(v___x_2619_);
v_arg_2627_ = lean_ctor_get(v___x_2621_, 1);
lean_inc_ref(v_arg_2627_);
lean_dec_ref(v___x_2621_);
v___x_2628_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(v_arg_2627_);
if (lean_obj_tag(v___x_2628_) == 1)
{
lean_object* v_val_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2735_; 
lean_dec_ref(v_arg_2627_);
v_val_2629_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2631_ = v___x_2628_;
v_isShared_2632_ = v_isSharedCheck_2735_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_val_2629_);
lean_dec(v___x_2628_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2735_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v_snd_2633_; lean_object* v_fst_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2734_; 
v_snd_2633_ = lean_ctor_get(v_val_2629_, 1);
v_fst_2634_ = lean_ctor_get(v_val_2629_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v_val_2629_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2636_ = v_val_2629_;
v_isShared_2637_ = v_isSharedCheck_2734_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_snd_2633_);
lean_inc(v_fst_2634_);
lean_dec(v_val_2629_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2734_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v_fst_2638_; lean_object* v_snd_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2733_; 
v_fst_2638_ = lean_ctor_get(v_snd_2633_, 0);
v_snd_2639_ = lean_ctor_get(v_snd_2633_, 1);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_snd_2633_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2641_ = v_snd_2633_;
v_isShared_2642_ = v_isSharedCheck_2733_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_snd_2639_);
lean_inc(v_fst_2638_);
lean_dec(v_snd_2633_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2733_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___f_2643_; lean_object* v_p_2644_; uint8_t v___x_2645_; lean_object* v___x_2646_; lean_object* v_q_2647_; lean_object* v_00_u03b2_2648_; lean_object* v___x_2649_; 
lean_inc_n(v_fst_2638_, 3);
v___f_2643_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2643_, 0, v_fst_2638_);
lean_inc_ref(v_arg_2626_);
lean_inc_ref_n(v_binderType_2616_, 4);
lean_inc_n(v_binderName_2615_, 3);
v_p_2644_ = l_Lean_mkLambda(v_binderName_2615_, v_binderInfo_2618_, v_binderType_2616_, v_arg_2626_);
v___x_2645_ = 0;
lean_inc(v_snd_2639_);
lean_inc(v_fst_2634_);
v___x_2646_ = l_Lean_mkLambda(v_fst_2634_, v___x_2645_, v_fst_2638_, v_snd_2639_);
v_q_2647_ = l_Lean_mkLambda(v_binderName_2615_, v_binderInfo_2618_, v_binderType_2616_, v___x_2646_);
v_00_u03b2_2648_ = l_Lean_mkLambda(v_binderName_2615_, v_binderInfo_2618_, v_binderType_2616_, v_fst_2638_);
v___x_2649_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2616_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2651_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref_known(v___x_2649_, 1);
lean_inc_ref(v_binderType_2616_);
lean_inc(v_binderName_2615_);
v___x_2651_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_binderName_2615_, v_binderType_2616_, v___f_2643_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v_a_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref_known(v___x_2651_, 1);
v___x_2653_ = lean_unsigned_to_nat(0u);
v___x_2654_ = lean_unsigned_to_nat(1u);
v___x_2655_ = lean_expr_lift_loose_bvars(v_arg_2626_, v___x_2653_, v___x_2654_);
lean_dec_ref(v_arg_2626_);
v___x_2656_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2655_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2658_ = l_Lean_Meta_Sym_mkOrS(v_snd_2639_, v_a_2657_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2660_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref_known(v___x_2658_, 1);
v___x_2660_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_fst_2634_, v___x_2645_, v_fst_2638_, v_a_2659_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_a_2661_; lean_object* v___x_2662_; 
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2661_);
lean_dec_ref_known(v___x_2660_, 1);
lean_inc_ref(v_binderType_2616_);
v___x_2662_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_binderName_2615_, v_binderInfo_2618_, v_binderType_2616_, v_a_2661_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2684_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2665_ = v___x_2662_;
v_isShared_2666_ = v_isSharedCheck_2684_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2662_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2684_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2670_; 
v___x_2667_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__1));
v___x_2668_ = lean_box(0);
if (v_isShared_2637_ == 0)
{
lean_ctor_set_tag(v___x_2636_, 1);
lean_ctor_set(v___x_2636_, 1, v___x_2668_);
lean_ctor_set(v___x_2636_, 0, v_a_2652_);
v___x_2670_ = v___x_2636_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2652_);
lean_ctor_set(v_reuseFailAlloc_2683_, 1, v___x_2668_);
v___x_2670_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2671_, 0, v_a_2650_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = l_Lean_mkConst(v___x_2667_, v___x_2671_);
v___x_2673_ = l_Lean_mkApp4(v___x_2672_, v_binderType_2616_, v_00_u03b2_2648_, v_p_2644_, v_q_2647_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 1, v___x_2673_);
lean_ctor_set(v___x_2641_, 0, v_a_2663_);
v___x_2675_ = v___x_2641_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2663_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
lean_object* v___x_2677_; 
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v___x_2675_);
v___x_2677_ = v___x_2631_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2675_);
v___x_2677_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
lean_object* v___x_2679_; 
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 0, v___x_2677_);
v___x_2679_ = v___x_2665_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2677_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec(v_a_2652_);
lean_dec(v_a_2650_);
lean_dec_ref(v_00_u03b2_2648_);
lean_dec_ref(v_q_2647_);
lean_dec_ref(v_p_2644_);
lean_del_object(v___x_2641_);
lean_del_object(v___x_2636_);
lean_del_object(v___x_2631_);
lean_dec_ref(v_binderType_2616_);
v_a_2685_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2662_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2662_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
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
lean_dec(v_a_2652_);
lean_dec(v_a_2650_);
lean_dec_ref(v_00_u03b2_2648_);
lean_dec_ref(v_q_2647_);
lean_dec_ref(v_p_2644_);
lean_del_object(v___x_2641_);
lean_del_object(v___x_2636_);
lean_del_object(v___x_2631_);
lean_dec_ref(v_binderType_2616_);
lean_dec(v_binderName_2615_);
v_a_2693_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2660_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2660_);
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
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
lean_dec(v_a_2652_);
lean_dec(v_a_2650_);
lean_dec_ref(v_00_u03b2_2648_);
lean_dec_ref(v_q_2647_);
lean_dec_ref(v_p_2644_);
lean_del_object(v___x_2641_);
lean_dec(v_fst_2638_);
lean_del_object(v___x_2636_);
lean_dec(v_fst_2634_);
lean_del_object(v___x_2631_);
lean_dec_ref(v_binderType_2616_);
lean_dec(v_binderName_2615_);
v_a_2701_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2658_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2658_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_dec(v_a_2652_);
lean_dec(v_a_2650_);
lean_dec_ref(v_00_u03b2_2648_);
lean_dec_ref(v_q_2647_);
lean_dec_ref(v_p_2644_);
lean_del_object(v___x_2641_);
lean_dec(v_snd_2639_);
lean_dec(v_fst_2638_);
lean_del_object(v___x_2636_);
lean_dec(v_fst_2634_);
lean_del_object(v___x_2631_);
lean_dec_ref(v_binderType_2616_);
lean_dec(v_binderName_2615_);
v_a_2709_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2656_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2656_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
lean_dec(v_a_2650_);
lean_dec_ref(v_00_u03b2_2648_);
lean_dec_ref(v_q_2647_);
lean_dec_ref(v_p_2644_);
lean_del_object(v___x_2641_);
lean_dec(v_snd_2639_);
lean_dec(v_fst_2638_);
lean_del_object(v___x_2636_);
lean_dec(v_fst_2634_);
lean_del_object(v___x_2631_);
lean_dec_ref(v_arg_2626_);
lean_dec_ref(v_binderType_2616_);
lean_dec(v_binderName_2615_);
v_a_2717_ = lean_ctor_get(v___x_2651_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2651_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2651_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2651_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec_ref(v_00_u03b2_2648_);
lean_dec_ref(v_q_2647_);
lean_dec_ref(v_p_2644_);
lean_dec_ref(v___f_2643_);
lean_del_object(v___x_2641_);
lean_dec(v_snd_2639_);
lean_dec(v_fst_2638_);
lean_del_object(v___x_2636_);
lean_dec(v_fst_2634_);
lean_del_object(v___x_2631_);
lean_dec_ref(v_arg_2626_);
lean_dec_ref(v_binderType_2616_);
lean_dec(v_binderName_2615_);
v_a_2725_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2649_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2649_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2736_; 
lean_dec(v___x_2628_);
v___x_2736_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(v_arg_2626_);
lean_dec_ref(v_arg_2626_);
if (lean_obj_tag(v___x_2736_) == 1)
{
lean_object* v_val_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2843_; 
v_val_2737_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2739_ = v___x_2736_;
v_isShared_2740_ = v_isSharedCheck_2843_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_val_2737_);
lean_dec(v___x_2736_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2843_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v_snd_2741_; lean_object* v_fst_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2842_; 
v_snd_2741_ = lean_ctor_get(v_val_2737_, 1);
v_fst_2742_ = lean_ctor_get(v_val_2737_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_val_2737_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2744_ = v_val_2737_;
v_isShared_2745_ = v_isSharedCheck_2842_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_snd_2741_);
lean_inc(v_fst_2742_);
lean_dec(v_val_2737_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2842_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v_fst_2746_; lean_object* v_snd_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2841_; 
v_fst_2746_ = lean_ctor_get(v_snd_2741_, 0);
v_snd_2747_ = lean_ctor_get(v_snd_2741_, 1);
v_isSharedCheck_2841_ = !lean_is_exclusive(v_snd_2741_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2749_ = v_snd_2741_;
v_isShared_2750_ = v_isSharedCheck_2841_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_snd_2747_);
lean_inc(v_fst_2746_);
lean_dec(v_snd_2741_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2841_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___f_2751_; lean_object* v_p_2752_; uint8_t v___x_2753_; lean_object* v___x_2754_; lean_object* v_q_2755_; lean_object* v_00_u03b2_2756_; lean_object* v___x_2757_; 
lean_inc_n(v_fst_2746_, 3);
v___f_2751_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___lam__0___boxed), 12, 1);
lean_closure_set(v___f_2751_, 0, v_fst_2746_);
lean_inc_ref(v_arg_2627_);
lean_inc_ref_n(v_binderType_2616_, 4);
lean_inc_n(v_binderName_2615_, 3);
v_p_2752_ = l_Lean_mkLambda(v_binderName_2615_, v_binderInfo_2618_, v_binderType_2616_, v_arg_2627_);
v___x_2753_ = 0;
lean_inc(v_snd_2747_);
lean_inc(v_fst_2742_);
v___x_2754_ = l_Lean_mkLambda(v_fst_2742_, v___x_2753_, v_fst_2746_, v_snd_2747_);
v_q_2755_ = l_Lean_mkLambda(v_binderName_2615_, v_binderInfo_2618_, v_binderType_2616_, v___x_2754_);
v_00_u03b2_2756_ = l_Lean_mkLambda(v_binderName_2615_, v_binderInfo_2618_, v_binderType_2616_, v_fst_2746_);
v___x_2757_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2616_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v___x_2759_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_a_2758_);
lean_dec_ref_known(v___x_2757_, 1);
lean_inc_ref(v_binderType_2616_);
lean_inc(v_binderName_2615_);
v___x_2759_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0___redArg(v_binderName_2615_, v_binderType_2616_, v___f_2751_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_a_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2759_, 1);
v___x_2761_ = lean_unsigned_to_nat(0u);
v___x_2762_ = lean_unsigned_to_nat(1u);
v___x_2763_ = lean_expr_lift_loose_bvars(v_arg_2627_, v___x_2761_, v___x_2762_);
lean_dec_ref(v_arg_2627_);
v___x_2764_ = l_Lean_Meta_Sym_shareCommonInc(v___x_2763_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2766_; 
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2764_, 1);
v___x_2766_ = l_Lean_Meta_Sym_mkOrS(v_a_2765_, v_snd_2747_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2768_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
lean_dec_ref_known(v___x_2766_, 1);
v___x_2768_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_fst_2742_, v___x_2753_, v_fst_2746_, v_a_2767_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2770_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2769_);
lean_dec_ref_known(v___x_2768_, 1);
lean_inc_ref(v_binderType_2616_);
v___x_2770_ = l_Lean_Meta_Sym_Internal_mkForallS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__2___redArg(v_binderName_2615_, v_binderInfo_2618_, v_binderType_2616_, v_a_2769_, v_a_2605_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_, v_a_2610_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2792_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2773_ = v___x_2770_;
v_isShared_2774_ = v_isSharedCheck_2792_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2770_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2792_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2778_; 
v___x_2775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___closed__3));
v___x_2776_ = lean_box(0);
if (v_isShared_2745_ == 0)
{
lean_ctor_set_tag(v___x_2744_, 1);
lean_ctor_set(v___x_2744_, 1, v___x_2776_);
lean_ctor_set(v___x_2744_, 0, v_a_2760_);
v___x_2778_ = v___x_2744_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2760_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2783_; 
v___x_2779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2779_, 0, v_a_2758_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = l_Lean_mkConst(v___x_2775_, v___x_2779_);
v___x_2781_ = l_Lean_mkApp4(v___x_2780_, v_binderType_2616_, v_00_u03b2_2756_, v_p_2752_, v_q_2755_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 1, v___x_2781_);
lean_ctor_set(v___x_2749_, 0, v_a_2771_);
v___x_2783_ = v___x_2749_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2771_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v___x_2781_);
v___x_2783_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
lean_object* v___x_2785_; 
if (v_isShared_2740_ == 0)
{
lean_ctor_set(v___x_2739_, 0, v___x_2783_);
v___x_2785_ = v___x_2739_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
lean_object* v___x_2787_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 0, v___x_2785_);
v___x_2787_ = v___x_2773_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
}
}
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
lean_dec(v_a_2760_);
lean_dec(v_a_2758_);
lean_dec_ref(v_00_u03b2_2756_);
lean_dec_ref(v_q_2755_);
lean_dec_ref(v_p_2752_);
lean_del_object(v___x_2749_);
lean_del_object(v___x_2744_);
lean_del_object(v___x_2739_);
lean_dec_ref(v_binderType_2616_);
v_a_2793_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2770_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2770_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v_a_2760_);
lean_dec(v_a_2758_);
lean_dec_ref(v_00_u03b2_2756_);
lean_dec_ref(v_q_2755_);
lean_dec_ref(v_p_2752_);
lean_del_object(v___x_2749_);
lean_del_object(v___x_2744_);
lean_del_object(v___x_2739_);
lean_dec_ref(v_binderType_2616_);
lean_dec(v_binderName_2615_);
v_a_2801_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2768_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2768_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_dec(v_a_2760_);
lean_dec(v_a_2758_);
lean_dec_ref(v_00_u03b2_2756_);
lean_dec_ref(v_q_2755_);
lean_dec_ref(v_p_2752_);
lean_del_object(v___x_2749_);
lean_dec(v_fst_2746_);
lean_del_object(v___x_2744_);
lean_dec(v_fst_2742_);
lean_del_object(v___x_2739_);
lean_dec_ref(v_binderType_2616_);
lean_dec(v_binderName_2615_);
v_a_2809_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2766_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2766_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
lean_dec(v_a_2760_);
lean_dec(v_a_2758_);
lean_dec_ref(v_00_u03b2_2756_);
lean_dec_ref(v_q_2755_);
lean_dec_ref(v_p_2752_);
lean_del_object(v___x_2749_);
lean_dec(v_snd_2747_);
lean_dec(v_fst_2746_);
lean_del_object(v___x_2744_);
lean_dec(v_fst_2742_);
lean_del_object(v___x_2739_);
lean_dec_ref(v_binderType_2616_);
lean_dec(v_binderName_2615_);
v_a_2817_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2764_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2764_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
else
{
lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_dec(v_a_2758_);
lean_dec_ref(v_00_u03b2_2756_);
lean_dec_ref(v_q_2755_);
lean_dec_ref(v_p_2752_);
lean_del_object(v___x_2749_);
lean_dec(v_snd_2747_);
lean_dec(v_fst_2746_);
lean_del_object(v___x_2744_);
lean_dec(v_fst_2742_);
lean_del_object(v___x_2739_);
lean_dec_ref(v_arg_2627_);
lean_dec_ref(v_binderType_2616_);
lean_dec(v_binderName_2615_);
v_a_2825_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2759_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2759_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
else
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2840_; 
lean_dec_ref(v_00_u03b2_2756_);
lean_dec_ref(v_q_2755_);
lean_dec_ref(v_p_2752_);
lean_dec_ref(v___f_2751_);
lean_del_object(v___x_2749_);
lean_dec(v_snd_2747_);
lean_dec(v_fst_2746_);
lean_del_object(v___x_2744_);
lean_dec(v_fst_2742_);
lean_del_object(v___x_2739_);
lean_dec_ref(v_arg_2627_);
lean_dec_ref(v_binderType_2616_);
lean_dec(v_binderName_2615_);
v_a_2833_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2835_ = v___x_2757_;
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___x_2757_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2840_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2838_; 
if (v_isShared_2836_ == 0)
{
v___x_2838_ = v___x_2835_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2844_; lean_object* v___x_2845_; 
lean_dec(v___x_2736_);
lean_dec_ref(v_arg_2627_);
lean_dec_ref(v_binderType_2616_);
lean_dec(v_binderName_2615_);
v___x_2844_ = lean_box(0);
v___x_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2844_);
return v___x_2845_;
}
}
}
}
}
}
else
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
lean_dec_ref(v_e_2601_);
v___x_2846_ = lean_box(0);
v___x_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
return v___x_2847_;
}
v___jp_2612_:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = lean_box(0);
v___x_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
return v___x_2614_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f___boxed(lean_object* v_e_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f(v_e_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_);
lean_dec(v_a_2857_);
lean_dec_ref(v_a_2856_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec(v_a_2853_);
lean_dec_ref(v_a_2852_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_a_2849_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg(lean_object* v_fvarId_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2863_ = l_Lean_Expr_fvar___override(v_fvarId_2860_);
v___x_2864_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2863_, v___y_2861_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg___boxed(lean_object* v_fvarId_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg(v_fvarId_2865_, v___y_2866_);
lean_dec(v___y_2866_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___lam__0(lean_object* v___y_2869_, lean_object* v_k_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v_b_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2881_ = l_Lean_Expr_fvarId_x21(v_b_2875_);
v___x_2882_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg(v___x_2881_, v___y_2869_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; lean_object* v___x_2884_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref_known(v___x_2882_, 1);
lean_inc(v___y_2879_);
lean_inc_ref(v___y_2878_);
lean_inc(v___y_2877_);
lean_inc_ref(v___y_2876_);
lean_inc(v___y_2869_);
lean_inc_ref(v___y_2874_);
lean_inc(v___y_2873_);
lean_inc_ref(v___y_2872_);
lean_inc(v___y_2871_);
v___x_2884_ = lean_apply_11(v_k_2870_, v_a_2883_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2869_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, lean_box(0));
return v___x_2884_;
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
lean_dec_ref(v_k_2870_);
v_a_2885_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2882_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2882_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___lam__0___boxed(lean_object* v___y_2893_, lean_object* v_k_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v_b_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___lam__0(v___y_2893_, v_k_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v_b_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
lean_dec_ref(v_b_2899_);
lean_dec_ref(v___y_2898_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec(v___y_2893_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg(lean_object* v_k_2906_, lean_object* v_name_2907_, uint8_t v_bi_2908_, lean_object* v_type_2909_, uint8_t v_kind_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v___f_2921_; lean_object* v___x_2922_; 
lean_inc_ref(v___y_2914_);
lean_inc(v___y_2913_);
lean_inc_ref(v___y_2912_);
lean_inc(v___y_2911_);
lean_inc(v___y_2915_);
v___f_2921_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___lam__0___boxed), 12, 6);
lean_closure_set(v___f_2921_, 0, v___y_2915_);
lean_closure_set(v___f_2921_, 1, v_k_2906_);
lean_closure_set(v___f_2921_, 2, v___y_2911_);
lean_closure_set(v___f_2921_, 3, v___y_2912_);
lean_closure_set(v___f_2921_, 4, v___y_2913_);
lean_closure_set(v___f_2921_, 5, v___y_2914_);
v___x_2922_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2907_, v_bi_2908_, v_type_2909_, v___f_2921_, v_kind_2910_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
if (lean_obj_tag(v___x_2922_) == 0)
{
return v___x_2922_;
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2922_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2922_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg___boxed(lean_object* v_k_2931_, lean_object* v_name_2932_, lean_object* v_bi_2933_, lean_object* v_type_2934_, lean_object* v_kind_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
uint8_t v_bi_boxed_2946_; uint8_t v_kind_boxed_2947_; lean_object* v_res_2948_; 
v_bi_boxed_2946_ = lean_unbox(v_bi_2933_);
v_kind_boxed_2947_ = lean_unbox(v_kind_2935_);
v_res_2948_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg(v_k_2931_, v_name_2932_, v_bi_boxed_2946_, v_type_2934_, v_kind_boxed_2947_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg(lean_object* v_name_2949_, uint8_t v_bi_2950_, lean_object* v_type_2951_, lean_object* v_k_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
uint8_t v___x_2963_; lean_object* v___x_2964_; 
v___x_2963_ = 0;
v___x_2964_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg(v_k_2952_, v_name_2949_, v_bi_2950_, v_type_2951_, v___x_2963_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg___boxed(lean_object* v_name_2965_, lean_object* v_bi_2966_, lean_object* v_type_2967_, lean_object* v_k_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
uint8_t v_bi_boxed_2979_; lean_object* v_res_2980_; 
v_bi_boxed_2979_ = lean_unbox(v_bi_2966_);
v_res_2980_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg(v_name_2965_, v_bi_boxed_2979_, v_type_2967_, v_k_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec_ref(v___y_2972_);
lean_dec(v___y_2971_);
lean_dec_ref(v___y_2970_);
lean_dec(v___y_2969_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___lam__0___boxed(lean_object* v_xs_2981_, lean_object* v_body_2982_, lean_object* v_x_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___lam__0(v_xs_2981_, v_body_2982_, v_x_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_);
lean_dec(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v___y_2984_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go(lean_object* v_xs_2995_, lean_object* v_e_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_){
_start:
{
if (lean_obj_tag(v_e_2996_) == 7)
{
lean_object* v_binderName_3007_; lean_object* v_binderType_3008_; lean_object* v_body_3009_; uint8_t v_binderInfo_3010_; uint8_t v___x_3011_; 
v_binderName_3007_ = lean_ctor_get(v_e_2996_, 0);
v_binderType_3008_ = lean_ctor_get(v_e_2996_, 1);
v_body_3009_ = lean_ctor_get(v_e_2996_, 2);
v_binderInfo_3010_ = lean_ctor_get_uint8(v_e_2996_, sizeof(void*)*3 + 8);
v___x_3011_ = l_Lean_Expr_isForall(v_body_3009_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; 
v___x_3012_ = lean_array_get_size(v_xs_2995_);
v___x_3013_ = lean_unsigned_to_nat(0u);
v___x_3014_ = lean_nat_dec_eq(v___x_3012_, v___x_3013_);
if (v___x_3014_ == 0)
{
uint8_t v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = 1;
lean_inc_ref(v_xs_2995_);
v___x_3016_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_e_2996_, v___x_3013_, v___x_3012_, v_xs_2995_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3018_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc_n(v_a_3017_, 2);
lean_dec_ref_known(v___x_3016_, 1);
v___x_3018_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f(v_a_3017_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3103_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3021_ = v___x_3018_;
v_isShared_3022_ = v_isSharedCheck_3103_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3018_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3103_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
if (lean_obj_tag(v_a_3019_) == 1)
{
lean_object* v_val_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3098_; 
lean_del_object(v___x_3021_);
v_val_3023_ = lean_ctor_get(v_a_3019_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v_a_3019_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3025_ = v_a_3019_;
v_isShared_3026_ = v_isSharedCheck_3098_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_val_3023_);
lean_dec(v_a_3019_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3098_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v_fst_3027_; lean_object* v_snd_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3097_; 
v_fst_3027_ = lean_ctor_get(v_val_3023_, 0);
v_snd_3028_ = lean_ctor_get(v_val_3023_, 1);
v_isSharedCheck_3097_ = !lean_is_exclusive(v_val_3023_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3030_ = v_val_3023_;
v_isShared_3031_ = v_isSharedCheck_3097_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_snd_3028_);
lean_inc(v_fst_3027_);
lean_dec(v_val_3023_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3097_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3032_; 
lean_inc_ref(v_xs_2995_);
v___x_3032_ = l_Lean_Meta_Sym_Simp_mkForallCongrFor(v_xs_2995_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; uint8_t v___x_3034_; lean_object* v___x_3035_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
v___x_3034_ = 1;
v___x_3035_ = l_Lean_Meta_mkLambdaFVars(v_xs_2995_, v_a_3017_, v___x_3014_, v___x_3015_, v___x_3014_, v___x_3015_, v___x_3034_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3037_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_a_3036_);
lean_dec_ref_known(v___x_3035_, 1);
lean_inc(v_fst_3027_);
v___x_3037_ = l_Lean_Meta_mkLambdaFVars(v_xs_2995_, v_fst_3027_, v___x_3014_, v___x_3015_, v___x_3014_, v___x_3015_, v___x_3034_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3039_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_a_3038_);
lean_dec_ref_known(v___x_3037_, 1);
v___x_3039_ = l_Lean_Meta_mkLambdaFVars(v_xs_2995_, v_snd_3028_, v___x_3014_, v___x_3015_, v___x_3014_, v___x_3015_, v___x_3034_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_object* v_a_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
lean_inc(v_a_3040_);
lean_dec_ref_known(v___x_3039_, 1);
v___x_3041_ = l_Lean_mkApp3(v_a_3033_, v_a_3036_, v_a_3038_, v_a_3040_);
v___x_3042_ = l_Lean_Meta_Sym_mkForallFVarsS(v_xs_2995_, v_fst_3027_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3056_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3045_ = v___x_3042_;
v_isShared_3046_ = v_isSharedCheck_3056_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3042_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3056_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 1, v___x_3041_);
lean_ctor_set(v___x_3030_, 0, v_a_3043_);
v___x_3048_ = v___x_3030_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3043_);
lean_ctor_set(v_reuseFailAlloc_3055_, 1, v___x_3041_);
v___x_3048_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3050_; 
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 0, v___x_3048_);
v___x_3050_ = v___x_3025_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3052_; 
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3050_);
v___x_3052_ = v___x_3045_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v___x_3050_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
}
else
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
lean_dec_ref(v___x_3041_);
lean_del_object(v___x_3030_);
lean_del_object(v___x_3025_);
v_a_3057_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___x_3042_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___x_3042_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3057_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
}
else
{
lean_object* v_a_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
lean_dec(v_a_3038_);
lean_dec(v_a_3036_);
lean_dec(v_a_3033_);
lean_del_object(v___x_3030_);
lean_dec(v_fst_3027_);
lean_del_object(v___x_3025_);
lean_dec_ref(v_xs_2995_);
v_a_3065_ = lean_ctor_get(v___x_3039_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3067_ = v___x_3039_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_a_3065_);
lean_dec(v___x_3039_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_a_3065_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
lean_dec(v_a_3036_);
lean_dec(v_a_3033_);
lean_del_object(v___x_3030_);
lean_dec(v_snd_3028_);
lean_dec(v_fst_3027_);
lean_del_object(v___x_3025_);
lean_dec_ref(v_xs_2995_);
v_a_3073_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3037_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3037_);
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
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec(v_a_3033_);
lean_del_object(v___x_3030_);
lean_dec(v_snd_3028_);
lean_dec(v_fst_3027_);
lean_del_object(v___x_3025_);
lean_dec_ref(v_xs_2995_);
v_a_3081_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3035_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3035_);
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
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_del_object(v___x_3030_);
lean_dec(v_snd_3028_);
lean_dec(v_fst_3027_);
lean_del_object(v___x_3025_);
lean_dec(v_a_3017_);
lean_dec_ref(v_xs_2995_);
v_a_3089_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3032_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3032_);
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
}
else
{
lean_object* v___x_3099_; lean_object* v___x_3101_; 
lean_dec(v_a_3019_);
lean_dec(v_a_3017_);
lean_dec_ref(v_xs_2995_);
v___x_3099_ = lean_box(0);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 0, v___x_3099_);
v___x_3101_ = v___x_3021_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3099_);
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
lean_dec(v_a_3017_);
lean_dec_ref(v_xs_2995_);
return v___x_3018_;
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec_ref(v_xs_2995_);
v_a_3104_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3016_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3016_);
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
lean_object* v___x_3112_; 
lean_dec_ref(v_xs_2995_);
v___x_3112_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOrCore_x3f(v_e_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
return v___x_3112_;
}
}
else
{
lean_object* v___f_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
lean_inc_ref(v_body_3009_);
lean_inc_ref(v_binderType_3008_);
lean_inc(v_binderName_3007_);
lean_dec_ref_known(v_e_2996_, 3);
lean_inc_ref(v_xs_2995_);
v___f_3113_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___lam__0___boxed), 13, 2);
lean_closure_set(v___f_3113_, 0, v_xs_2995_);
lean_closure_set(v___f_3113_, 1, v_body_3009_);
v___x_3114_ = lean_unsigned_to_nat(0u);
v___x_3115_ = lean_array_get_size(v_xs_2995_);
v___x_3116_ = l_Lean_Meta_Sym_instantiateRevRangeS(v_binderType_3008_, v___x_3114_, v___x_3115_, v_xs_2995_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; lean_object* v___x_3118_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_a_3117_);
lean_dec_ref_known(v___x_3116_, 1);
v___x_3118_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg(v_binderName_3007_, v_binderInfo_3010_, v_a_3117_, v___f_3113_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_);
return v___x_3118_;
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec_ref(v___f_3113_);
lean_dec(v_binderName_3007_);
v_a_3119_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3116_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3116_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
else
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
lean_dec_ref(v_e_2996_);
lean_dec_ref(v_xs_2995_);
v___x_3127_ = lean_box(0);
v___x_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
return v___x_3128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___lam__0(lean_object* v_xs_3129_, lean_object* v_body_3130_, lean_object* v_x_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
v___x_3142_ = lean_array_push(v_xs_3129_, v_x_3131_);
v___x_3143_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go(v___x_3142_, v_body_3130_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go___boxed(lean_object* v_xs_3144_, lean_object* v_e_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go(v_xs_3144_, v_e_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_);
lean_dec(v_a_3154_);
lean_dec_ref(v_a_3153_);
lean_dec(v_a_3152_);
lean_dec_ref(v_a_3151_);
lean_dec(v_a_3150_);
lean_dec_ref(v_a_3149_);
lean_dec(v_a_3148_);
lean_dec_ref(v_a_3147_);
lean_dec(v_a_3146_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0(lean_object* v_fvarId_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v___x_3165_; 
v___x_3165_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___redArg(v_fvarId_3157_, v___y_3159_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0___boxed(lean_object* v_fvarId_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_Lean_Meta_Sym_Internal_mkFVarS___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__0(v_fvarId_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2(lean_object* v_00_u03b1_3175_, lean_object* v_k_3176_, lean_object* v_name_3177_, uint8_t v_bi_3178_, lean_object* v_type_3179_, uint8_t v_kind_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v___x_3191_; 
v___x_3191_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___redArg(v_k_3176_, v_name_3177_, v_bi_3178_, v_type_3179_, v_kind_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2___boxed(lean_object* v_00_u03b1_3192_, lean_object* v_k_3193_, lean_object* v_name_3194_, lean_object* v_bi_3195_, lean_object* v_type_3196_, lean_object* v_kind_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
uint8_t v_bi_boxed_3208_; uint8_t v_kind_boxed_3209_; lean_object* v_res_3210_; 
v_bi_boxed_3208_ = lean_unbox(v_bi_3195_);
v_kind_boxed_3209_ = lean_unbox(v_kind_3197_);
v_res_3210_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_NormSym_reduceCtorEq_spec__0_spec__0___at___00Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0_spec__2(v_00_u03b1_3192_, v_k_3193_, v_name_3194_, v_bi_boxed_3208_, v_type_3196_, v_kind_boxed_3209_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_);
lean_dec(v___y_3206_);
lean_dec_ref(v___y_3205_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v___y_3198_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0(lean_object* v_00_u03b1_3211_, lean_object* v_name_3212_, uint8_t v_bi_3213_, lean_object* v_type_3214_, lean_object* v_k_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
lean_object* v___x_3226_; 
v___x_3226_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___redArg(v_name_3212_, v_bi_3213_, v_type_3214_, v_k_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0___boxed(lean_object* v_00_u03b1_3227_, lean_object* v_name_3228_, lean_object* v_bi_3229_, lean_object* v_type_3230_, lean_object* v_k_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_){
_start:
{
uint8_t v_bi_boxed_3242_; lean_object* v_res_3243_; 
v_bi_boxed_3242_ = lean_unbox(v_bi_3229_);
v_res_3243_ = l_Lean_Meta_Sym_withLocalDeclS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go_spec__0(v_00_u03b1_3227_, v_name_3228_, v_bi_boxed_3242_, v_type_3230_, v_k_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f(lean_object* v_e_3246_, lean_object* v_a_3247_, lean_object* v_a_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; uint8_t v___x_3265_; 
v___x_3263_ = l_Lean_Expr_getForallBody(v_e_3246_);
v___x_3264_ = l_Lean_Expr_cleanupAnnotations(v___x_3263_);
lean_dec_ref(v___x_3263_);
v___x_3265_ = l_Lean_Expr_isApp(v___x_3264_);
if (v___x_3265_ == 0)
{
lean_dec_ref(v___x_3264_);
lean_dec_ref(v_e_3246_);
goto v___jp_3257_;
}
else
{
lean_object* v___x_3266_; uint8_t v___x_3267_; 
v___x_3266_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3264_);
v___x_3267_ = l_Lean_Expr_isApp(v___x_3266_);
if (v___x_3267_ == 0)
{
lean_dec_ref(v___x_3266_);
lean_dec_ref(v___x_3264_);
lean_dec_ref(v_e_3246_);
goto v___jp_3257_;
}
else
{
lean_object* v___x_3268_; lean_object* v___x_3269_; uint8_t v___x_3270_; 
v___x_3268_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3266_);
v___x_3269_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__12));
v___x_3270_ = l_Lean_Expr_isConstOf(v___x_3268_, v___x_3269_);
lean_dec_ref(v___x_3268_);
if (v___x_3270_ == 0)
{
lean_dec_ref(v___x_3266_);
lean_dec_ref(v___x_3264_);
lean_dec_ref(v_e_3246_);
goto v___jp_3257_;
}
else
{
lean_object* v_arg_3271_; lean_object* v_arg_3272_; lean_object* v___x_3273_; 
v_arg_3271_ = lean_ctor_get(v___x_3264_, 1);
lean_inc_ref(v_arg_3271_);
lean_dec_ref(v___x_3264_);
v_arg_3272_ = lean_ctor_get(v___x_3266_, 1);
lean_inc_ref(v_arg_3272_);
lean_dec_ref(v___x_3266_);
v___x_3273_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(v_arg_3272_);
lean_dec_ref(v_arg_3272_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v___x_3274_; 
v___x_3274_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_isForallOrNot_x3f(v_arg_3271_);
lean_dec_ref(v_arg_3271_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
lean_dec_ref(v_e_3246_);
v___x_3275_ = lean_box(0);
v___x_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3275_);
return v___x_3276_;
}
else
{
lean_dec_ref_known(v___x_3274_, 1);
goto v___jp_3260_;
}
}
else
{
lean_dec_ref_known(v___x_3273_, 1);
lean_dec_ref(v_arg_3271_);
goto v___jp_3260_;
}
}
}
}
v___jp_3257_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = lean_box(0);
v___x_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3259_, 0, v___x_3258_);
return v___x_3259_;
}
v___jp_3260_:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3261_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f___closed__0));
v___x_3262_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f_go(v___x_3261_, v_e_3246_, v_a_3247_, v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_);
return v___x_3262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f___boxed(lean_object* v_e_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f(v_e_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec_ref(v_a_3283_);
lean_dec(v_a_3282_);
lean_dec_ref(v_a_3281_);
lean_dec(v_a_3280_);
lean_dec_ref(v_a_3279_);
lean_dec(v_a_3278_);
return v_res_3288_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__2(void){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3294_ = lean_box(0);
v___x_3295_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__1));
v___x_3296_ = l_Lean_mkConst(v___x_3295_, v___x_3294_);
return v___x_3296_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__7(void){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3305_ = lean_box(0);
v___x_3306_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__6));
v___x_3307_ = l_Lean_mkConst(v___x_3306_, v___x_3305_);
return v___x_3307_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__10(void){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3313_ = lean_box(0);
v___x_3314_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__9));
v___x_3315_ = l_Lean_mkConst(v___x_3314_, v___x_3313_);
return v___x_3315_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__13(void){
_start:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3321_ = lean_box(0);
v___x_3322_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__12));
v___x_3323_ = l_Lean_mkConst(v___x_3322_, v___x_3321_);
return v___x_3323_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__18(void){
_start:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3333_ = lean_box(0);
v___x_3334_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__17));
v___x_3335_ = l_Lean_mkConst(v___x_3334_, v___x_3333_);
return v___x_3335_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__19(void){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3336_ = lean_unsigned_to_nat(0u);
v___x_3337_ = l_Lean_Level_ofNat(v___x_3336_);
return v___x_3337_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__20(void){
_start:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3338_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__19, &l_Lean_Meta_Grind_NormSym_simpForall___closed__19_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__19);
v___x_3339_ = l_Lean_mkSort(v___x_3338_);
return v___x_3339_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__23(void){
_start:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3343_ = lean_box(0);
v___x_3344_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__22));
v___x_3345_ = l_Lean_mkConst(v___x_3344_, v___x_3343_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpForall(lean_object* v_e_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_){
_start:
{
lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; lean_object* v___y_3365_; lean_object* v___y_3366_; 
if (lean_obj_tag(v_e_3346_) == 7)
{
lean_object* v_binderName_3451_; lean_object* v_binderType_3452_; lean_object* v_body_3453_; uint8_t v_binderInfo_3454_; uint8_t v___x_3455_; 
v_binderName_3451_ = lean_ctor_get(v_e_3346_, 0);
v_binderType_3452_ = lean_ctor_get(v_e_3346_, 1);
v_body_3453_ = lean_ctor_get(v_e_3346_, 2);
v_binderInfo_3454_ = lean_ctor_get_uint8(v_e_3346_, sizeof(void*)*3 + 8);
v___x_3455_ = l_Lean_Expr_hasLooseBVars(v_body_3453_);
if (v___x_3455_ == 0)
{
uint8_t v___x_3456_; lean_object* v___x_3457_; 
v___x_3456_ = 1;
lean_inc_ref(v_binderType_3452_);
v___x_3457_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3452_, v_a_3353_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; uint8_t v___x_3461_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref_known(v___x_3457_, 1);
v___x_3459_ = l_Lean_Expr_cleanupAnnotations(v_a_3458_);
lean_dec(v_a_3458_);
v___x_3460_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_3461_ = l_Lean_Expr_isConstOf(v___x_3459_, v___x_3460_);
if (v___x_3461_ == 0)
{
lean_object* v___x_3462_; uint8_t v___x_3463_; 
v___x_3462_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__10));
v___x_3463_ = l_Lean_Expr_isConstOf(v___x_3459_, v___x_3462_);
lean_dec_ref(v___x_3459_);
if (v___x_3463_ == 0)
{
lean_object* v___x_3464_; 
lean_inc_ref(v_body_3453_);
v___x_3464_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_body_3453_, v_a_3353_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3466_; uint8_t v___x_3467_; 
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_a_3465_);
lean_dec_ref_known(v___x_3464_, 1);
v___x_3466_ = l_Lean_Expr_cleanupAnnotations(v_a_3465_);
lean_dec(v_a_3465_);
v___x_3467_ = l_Lean_Expr_isConstOf(v___x_3466_, v___x_3460_);
if (v___x_3467_ == 0)
{
uint8_t v___x_3468_; 
v___x_3468_ = l_Lean_Expr_isConstOf(v___x_3466_, v___x_3462_);
lean_dec_ref(v___x_3466_);
if (v___x_3468_ == 0)
{
lean_object* v___x_3469_; 
lean_inc_ref(v_binderType_3452_);
v___x_3469_ = l_Lean_Meta_isProp(v_binderType_3452_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_);
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v_a_3470_; size_t v___x_3471_; size_t v___x_3472_; uint8_t v___x_3473_; 
v_a_3470_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_a_3470_);
lean_dec_ref_known(v___x_3469_, 1);
v___x_3471_ = lean_ptr_addr(v_binderType_3452_);
v___x_3472_ = lean_ptr_addr(v_body_3453_);
v___x_3473_ = lean_usize_dec_eq(v___x_3471_, v___x_3472_);
if (v___x_3473_ == 0)
{
lean_dec(v_a_3470_);
v___y_3358_ = v_a_3347_;
v___y_3359_ = v_a_3348_;
v___y_3360_ = v_a_3349_;
v___y_3361_ = v_a_3350_;
v___y_3362_ = v_a_3351_;
v___y_3363_ = v_a_3352_;
v___y_3364_ = v_a_3353_;
v___y_3365_ = v_a_3354_;
v___y_3366_ = v_a_3355_;
goto v___jp_3357_;
}
else
{
uint8_t v___x_3474_; 
v___x_3474_ = lean_unbox(v_a_3470_);
lean_dec(v_a_3470_);
if (v___x_3474_ == 0)
{
v___y_3358_ = v_a_3347_;
v___y_3359_ = v_a_3348_;
v___y_3360_ = v_a_3349_;
v___y_3361_ = v_a_3350_;
v___y_3362_ = v_a_3351_;
v___y_3363_ = v_a_3352_;
v___y_3364_ = v_a_3353_;
v___y_3365_ = v_a_3354_;
v___y_3366_ = v_a_3355_;
goto v___jp_3357_;
}
else
{
lean_object* v___x_3475_; 
lean_inc_ref(v_binderType_3452_);
lean_dec_ref_known(v_e_3346_, 3);
v___x_3475_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3350_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3486_; 
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3478_ = v___x_3475_;
v_isShared_3479_ = v_isSharedCheck_3486_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3475_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3486_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3484_; 
v___x_3480_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__2, &l_Lean_Meta_Grind_NormSym_simpForall___closed__2_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__2);
v___x_3481_ = l_Lean_Expr_app___override(v___x_3480_, v_binderType_3452_);
v___x_3482_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3482_, 0, v_a_3476_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
lean_ctor_set_uint8(v___x_3482_, sizeof(void*)*2, v___x_3456_);
lean_ctor_set_uint8(v___x_3482_, sizeof(void*)*2 + 1, v___x_3468_);
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 0, v___x_3482_);
v___x_3484_ = v___x_3478_;
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
lean_dec_ref(v_binderType_3452_);
v_a_3487_ = lean_ctor_get(v___x_3475_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___x_3475_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3475_);
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
}
}
else
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
lean_dec_ref_known(v_e_3346_, 3);
v_a_3495_ = lean_ctor_get(v___x_3469_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3497_ = v___x_3469_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3469_);
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
lean_object* v___x_3503_; 
lean_inc_ref(v_binderType_3452_);
lean_dec_ref_known(v_e_3346_, 3);
v___x_3503_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3350_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___x_3505_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3503_, 1);
lean_inc_ref(v_binderType_3452_);
v___x_3505_ = l_Lean_Meta_getLevel(v_binderType_3452_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3519_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3508_ = v___x_3505_;
v_isShared_3509_ = v_isSharedCheck_3519_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3505_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3519_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3517_; 
v___x_3510_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__4));
v___x_3511_ = lean_box(0);
v___x_3512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3512_, 0, v_a_3506_);
lean_ctor_set(v___x_3512_, 1, v___x_3511_);
v___x_3513_ = l_Lean_mkConst(v___x_3510_, v___x_3512_);
v___x_3514_ = l_Lean_Expr_app___override(v___x_3513_, v_binderType_3452_);
v___x_3515_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3515_, 0, v_a_3504_);
lean_ctor_set(v___x_3515_, 1, v___x_3514_);
lean_ctor_set_uint8(v___x_3515_, sizeof(void*)*2, v___x_3456_);
lean_ctor_set_uint8(v___x_3515_, sizeof(void*)*2 + 1, v___x_3467_);
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 0, v___x_3515_);
v___x_3517_ = v___x_3508_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3515_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec(v_a_3504_);
lean_dec_ref(v_binderType_3452_);
v_a_3520_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3505_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3505_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
else
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
lean_dec_ref(v_binderType_3452_);
v_a_3528_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_3503_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3503_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3528_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
}
else
{
lean_object* v___x_3536_; 
lean_dec_ref(v___x_3466_);
lean_inc_ref(v_binderType_3452_);
v___x_3536_ = l_Lean_Meta_isProp(v_binderType_3452_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; uint8_t v___x_3538_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3537_);
lean_dec_ref_known(v___x_3536_, 1);
v___x_3538_ = lean_unbox(v_a_3537_);
lean_dec(v_a_3537_);
if (v___x_3538_ == 0)
{
v___y_3358_ = v_a_3347_;
v___y_3359_ = v_a_3348_;
v___y_3360_ = v_a_3349_;
v___y_3361_ = v_a_3350_;
v___y_3362_ = v_a_3351_;
v___y_3363_ = v_a_3352_;
v___y_3364_ = v_a_3353_;
v___y_3365_ = v_a_3354_;
v___y_3366_ = v_a_3355_;
goto v___jp_3357_;
}
else
{
lean_object* v___x_3539_; 
lean_inc_ref_n(v_binderType_3452_, 2);
lean_dec_ref_known(v_e_3346_, 3);
v___x_3539_ = l_Lean_Meta_Sym_mkNotS(v_binderType_3452_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3550_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3542_ = v___x_3539_;
v_isShared_3543_ = v_isSharedCheck_3550_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3539_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3550_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3548_; 
v___x_3544_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__7, &l_Lean_Meta_Grind_NormSym_simpForall___closed__7_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__7);
v___x_3545_ = l_Lean_Expr_app___override(v___x_3544_, v_binderType_3452_);
v___x_3546_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3546_, 0, v_a_3540_);
lean_ctor_set(v___x_3546_, 1, v___x_3545_);
lean_ctor_set_uint8(v___x_3546_, sizeof(void*)*2, v___x_3463_);
lean_ctor_set_uint8(v___x_3546_, sizeof(void*)*2 + 1, v___x_3463_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 0, v___x_3546_);
v___x_3548_ = v___x_3542_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v___x_3546_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_dec_ref(v_binderType_3452_);
v_a_3551_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3539_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3539_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_dec_ref_known(v_e_3346_, 3);
v_a_3559_ = lean_ctor_get(v___x_3536_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3536_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3536_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3536_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_dec_ref_known(v_e_3346_, 3);
v_a_3567_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3464_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3464_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
else
{
lean_object* v___x_3575_; 
lean_inc_ref(v_body_3453_);
v___x_3575_ = l_Lean_Meta_isProp(v_body_3453_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3587_; 
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3578_ = v___x_3575_;
v_isShared_3579_ = v_isSharedCheck_3587_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3575_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3587_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
uint8_t v___x_3580_; 
v___x_3580_ = lean_unbox(v_a_3576_);
lean_dec(v_a_3576_);
if (v___x_3580_ == 0)
{
lean_del_object(v___x_3578_);
v___y_3358_ = v_a_3347_;
v___y_3359_ = v_a_3348_;
v___y_3360_ = v_a_3349_;
v___y_3361_ = v_a_3350_;
v___y_3362_ = v_a_3351_;
v___y_3363_ = v_a_3352_;
v___y_3364_ = v_a_3353_;
v___y_3365_ = v_a_3354_;
v___y_3366_ = v_a_3355_;
goto v___jp_3357_;
}
else
{
lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3585_; 
lean_inc_ref_n(v_body_3453_, 2);
lean_dec_ref_known(v_e_3346_, 3);
v___x_3581_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__10, &l_Lean_Meta_Grind_NormSym_simpForall___closed__10_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__10);
v___x_3582_ = l_Lean_Expr_app___override(v___x_3581_, v_body_3453_);
v___x_3583_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3583_, 0, v_body_3453_);
lean_ctor_set(v___x_3583_, 1, v___x_3582_);
lean_ctor_set_uint8(v___x_3583_, sizeof(void*)*2, v___x_3456_);
lean_ctor_set_uint8(v___x_3583_, sizeof(void*)*2 + 1, v___x_3461_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 0, v___x_3583_);
v___x_3585_ = v___x_3578_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3583_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec_ref_known(v_e_3346_, 3);
v_a_3588_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3575_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3575_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
}
else
{
lean_object* v___x_3596_; 
lean_dec_ref(v___x_3459_);
lean_inc_ref(v_body_3453_);
v___x_3596_ = l_Lean_Meta_isProp(v_body_3453_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; uint8_t v___x_3598_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc(v_a_3597_);
lean_dec_ref_known(v___x_3596_, 1);
v___x_3598_ = lean_unbox(v_a_3597_);
lean_dec(v_a_3597_);
if (v___x_3598_ == 0)
{
v___y_3358_ = v_a_3347_;
v___y_3359_ = v_a_3348_;
v___y_3360_ = v_a_3349_;
v___y_3361_ = v_a_3350_;
v___y_3362_ = v_a_3351_;
v___y_3363_ = v_a_3352_;
v___y_3364_ = v_a_3353_;
v___y_3365_ = v_a_3354_;
v___y_3366_ = v_a_3355_;
goto v___jp_3357_;
}
else
{
lean_object* v___x_3599_; 
lean_inc_ref(v_body_3453_);
lean_dec_ref_known(v_e_3346_, 3);
v___x_3599_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3350_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3610_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3602_ = v___x_3599_;
v_isShared_3603_ = v_isSharedCheck_3610_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3599_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3610_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3604_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__13, &l_Lean_Meta_Grind_NormSym_simpForall___closed__13_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__13);
v___x_3605_ = l_Lean_Expr_app___override(v___x_3604_, v_body_3453_);
v___x_3606_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3606_, 0, v_a_3600_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
lean_ctor_set_uint8(v___x_3606_, sizeof(void*)*2, v___x_3456_);
lean_ctor_set_uint8(v___x_3606_, sizeof(void*)*2 + 1, v___x_3455_);
if (v_isShared_3603_ == 0)
{
lean_ctor_set(v___x_3602_, 0, v___x_3606_);
v___x_3608_ = v___x_3602_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3606_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec_ref(v_body_3453_);
v_a_3611_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3599_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3599_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
lean_dec_ref_known(v_e_3346_, 3);
v_a_3619_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3596_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3596_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_dec_ref_known(v_e_3346_, 3);
v_a_3627_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3457_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3457_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
else
{
uint8_t v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = 0;
lean_inc_ref(v_binderType_3452_);
v___x_3636_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_3452_, v_a_3353_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; uint8_t v___x_3640_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_a_3637_);
lean_dec_ref_known(v___x_3636_, 1);
v___x_3638_ = l_Lean_Expr_cleanupAnnotations(v_a_3637_);
lean_dec(v_a_3637_);
v___x_3639_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__8));
v___x_3640_ = l_Lean_Expr_isConstOf(v___x_3638_, v___x_3639_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3641_; uint8_t v___x_3642_; 
v___x_3641_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__10));
v___x_3642_ = l_Lean_Expr_isConstOf(v___x_3638_, v___x_3641_);
lean_dec_ref(v___x_3638_);
if (v___x_3642_ == 0)
{
v___y_3358_ = v_a_3347_;
v___y_3359_ = v_a_3348_;
v___y_3360_ = v_a_3349_;
v___y_3361_ = v_a_3350_;
v___y_3362_ = v_a_3351_;
v___y_3363_ = v_a_3352_;
v___y_3364_ = v_a_3353_;
v___y_3365_ = v_a_3354_;
v___y_3366_ = v_a_3355_;
goto v___jp_3357_;
}
else
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3643_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpForall___closed__15));
v___x_3644_ = lean_box(0);
v___x_3645_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___redArg(v___x_3643_, v___x_3644_, v_a_3351_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_object* v_a_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
lean_inc(v_a_3646_);
lean_dec_ref_known(v___x_3645_, 1);
v___x_3647_ = lean_unsigned_to_nat(1u);
v___x_3648_ = lean_mk_empty_array_with_capacity(v___x_3647_);
v___x_3649_ = lean_array_push(v___x_3648_, v_a_3646_);
lean_inc_ref(v_body_3453_);
v___x_3650_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_body_3453_, v___x_3649_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v___x_3652_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc_n(v_a_3651_, 2);
lean_dec_ref_known(v___x_3650_, 1);
v___x_3652_ = l_Lean_Meta_isProp(v_a_3651_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3665_; 
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3655_ = v___x_3652_;
v_isShared_3656_ = v_isSharedCheck_3665_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3652_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3665_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
uint8_t v___x_3657_; 
v___x_3657_ = lean_unbox(v_a_3653_);
lean_dec(v_a_3653_);
if (v___x_3657_ == 0)
{
lean_del_object(v___x_3655_);
lean_dec(v_a_3651_);
v___y_3358_ = v_a_3347_;
v___y_3359_ = v_a_3348_;
v___y_3360_ = v_a_3349_;
v___y_3361_ = v_a_3350_;
v___y_3362_ = v_a_3351_;
v___y_3363_ = v_a_3352_;
v___y_3364_ = v_a_3353_;
v___y_3365_ = v_a_3354_;
v___y_3366_ = v_a_3355_;
goto v___jp_3357_;
}
else
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3663_; 
lean_inc_ref(v_body_3453_);
lean_inc_ref(v_binderType_3452_);
lean_inc(v_binderName_3451_);
lean_dec_ref_known(v_e_3346_, 3);
v___x_3658_ = l_Lean_mkLambda(v_binderName_3451_, v_binderInfo_3454_, v_binderType_3452_, v_body_3453_);
v___x_3659_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__18, &l_Lean_Meta_Grind_NormSym_simpForall___closed__18_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__18);
v___x_3660_ = l_Lean_Expr_app___override(v___x_3659_, v___x_3658_);
v___x_3661_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3661_, 0, v_a_3651_);
lean_ctor_set(v___x_3661_, 1, v___x_3660_);
lean_ctor_set_uint8(v___x_3661_, sizeof(void*)*2, v___x_3455_);
lean_ctor_set_uint8(v___x_3661_, sizeof(void*)*2 + 1, v___x_3635_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 0, v___x_3661_);
v___x_3663_ = v___x_3655_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3661_);
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
else
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
lean_dec(v_a_3651_);
lean_dec_ref_known(v_e_3346_, 3);
v_a_3666_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3668_ = v___x_3652_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3652_);
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
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
lean_dec_ref_known(v_e_3346_, 3);
v_a_3674_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3650_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3650_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
lean_dec_ref_known(v_e_3346_, 3);
v_a_3682_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3645_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3645_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
}
}
}
}
}
else
{
lean_object* v___x_3690_; lean_object* v___x_3691_; 
lean_dec_ref(v___x_3638_);
lean_inc_ref(v_body_3453_);
lean_inc_ref(v_binderType_3452_);
lean_inc(v_binderName_3451_);
v___x_3690_ = l_Lean_mkLambda(v_binderName_3451_, v_binderInfo_3454_, v_binderType_3452_, v_body_3453_);
lean_inc(v_a_3355_);
lean_inc_ref(v_a_3354_);
lean_inc(v_a_3353_);
lean_inc_ref(v_a_3352_);
lean_inc_ref(v___x_3690_);
v___x_3691_ = lean_infer_type(v___x_3690_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v_a_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v_a_3692_ = lean_ctor_get(v___x_3691_, 0);
lean_inc(v_a_3692_);
lean_dec_ref_known(v___x_3691_, 1);
v___x_3693_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__20, &l_Lean_Meta_Grind_NormSym_simpForall___closed__20_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__20);
lean_inc_ref(v_binderType_3452_);
lean_inc(v_binderName_3451_);
v___x_3694_ = l_Lean_mkForall(v_binderName_3451_, v_binderInfo_3454_, v_binderType_3452_, v___x_3693_);
v___x_3695_ = l_Lean_Meta_isExprDefEq(v_a_3692_, v___x_3694_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; uint8_t v___x_3697_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3696_);
lean_dec_ref_known(v___x_3695_, 1);
v___x_3697_ = lean_unbox(v_a_3696_);
lean_dec(v_a_3696_);
if (v___x_3697_ == 0)
{
lean_dec_ref(v___x_3690_);
v___y_3358_ = v_a_3347_;
v___y_3359_ = v_a_3348_;
v___y_3360_ = v_a_3349_;
v___y_3361_ = v_a_3350_;
v___y_3362_ = v_a_3351_;
v___y_3363_ = v_a_3352_;
v___y_3364_ = v_a_3353_;
v___y_3365_ = v_a_3354_;
v___y_3366_ = v_a_3355_;
goto v___jp_3357_;
}
else
{
lean_object* v___x_3698_; 
lean_dec_ref_known(v_e_3346_, 3);
v___x_3698_ = l_Lean_Meta_Sym_getTrueExpr___redArg(v_a_3350_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3709_; 
v_a_3699_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3701_ = v___x_3698_;
v_isShared_3702_ = v_isSharedCheck_3709_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3698_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3709_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3707_; 
v___x_3703_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpForall___closed__23, &l_Lean_Meta_Grind_NormSym_simpForall___closed__23_once, _init_l_Lean_Meta_Grind_NormSym_simpForall___closed__23);
v___x_3704_ = l_Lean_Expr_app___override(v___x_3703_, v___x_3690_);
v___x_3705_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3705_, 0, v_a_3699_);
lean_ctor_set(v___x_3705_, 1, v___x_3704_);
lean_ctor_set_uint8(v___x_3705_, sizeof(void*)*2, v___x_3455_);
lean_ctor_set_uint8(v___x_3705_, sizeof(void*)*2 + 1, v___x_3635_);
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 0, v___x_3705_);
v___x_3707_ = v___x_3701_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3705_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
else
{
lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3717_; 
lean_dec_ref(v___x_3690_);
v_a_3710_ = lean_ctor_get(v___x_3698_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3698_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3712_ = v___x_3698_;
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3698_);
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
lean_dec_ref(v___x_3690_);
lean_dec_ref_known(v_e_3346_, 3);
v_a_3718_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3720_ = v___x_3695_;
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3695_);
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
lean_object* v_a_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3733_; 
lean_dec_ref(v___x_3690_);
lean_dec_ref_known(v_e_3346_, 3);
v_a_3726_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3728_ = v___x_3691_;
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_a_3726_);
lean_dec(v___x_3691_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3731_; 
if (v_isShared_3729_ == 0)
{
v___x_3731_ = v___x_3728_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_a_3726_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
}
else
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
lean_dec_ref_known(v_e_3346_, 3);
v_a_3734_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3636_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3636_);
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
else
{
lean_object* v___x_3742_; lean_object* v___x_3743_; 
lean_dec_ref(v_e_3346_);
v___x_3742_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3742_);
return v___x_3743_;
}
v___jp_3357_:
{
lean_object* v___x_3367_; 
lean_inc_ref(v_e_3346_);
v___x_3367_ = l___private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_forallOr_x3f(v_e_3346_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3442_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3370_ = v___x_3367_;
v_isShared_3371_ = v_isSharedCheck_3442_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3367_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3442_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
if (lean_obj_tag(v_a_3368_) == 1)
{
lean_object* v_val_3372_; lean_object* v_fst_3373_; lean_object* v_snd_3374_; uint8_t v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3378_; 
lean_dec_ref(v_e_3346_);
v_val_3372_ = lean_ctor_get(v_a_3368_, 0);
lean_inc(v_val_3372_);
lean_dec_ref_known(v_a_3368_, 1);
v_fst_3373_ = lean_ctor_get(v_val_3372_, 0);
lean_inc(v_fst_3373_);
v_snd_3374_ = lean_ctor_get(v_val_3372_, 1);
lean_inc(v_snd_3374_);
lean_dec(v_val_3372_);
v___x_3375_ = 0;
v___x_3376_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3376_, 0, v_fst_3373_);
lean_ctor_set(v___x_3376_, 1, v_snd_3374_);
lean_ctor_set_uint8(v___x_3376_, sizeof(void*)*2, v___x_3375_);
lean_ctor_set_uint8(v___x_3376_, sizeof(void*)*2 + 1, v___x_3375_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v___x_3376_);
v___x_3378_ = v___x_3370_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3376_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
else
{
lean_object* v___x_3380_; 
lean_del_object(v___x_3370_);
lean_dec(v_a_3368_);
v___x_3380_ = l_Lean_Meta_Grind_forallImpAnd_x3f(v_e_3346_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3433_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3383_ = v___x_3380_;
v_isShared_3384_ = v_isSharedCheck_3433_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3380_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3433_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
if (lean_obj_tag(v_a_3381_) == 1)
{
lean_object* v_val_3385_; lean_object* v_snd_3386_; lean_object* v_fst_3387_; lean_object* v_fst_3388_; lean_object* v_snd_3389_; lean_object* v___x_3390_; 
lean_del_object(v___x_3383_);
v_val_3385_ = lean_ctor_get(v_a_3381_, 0);
lean_inc(v_val_3385_);
lean_dec_ref_known(v_a_3381_, 1);
v_snd_3386_ = lean_ctor_get(v_val_3385_, 1);
lean_inc(v_snd_3386_);
v_fst_3387_ = lean_ctor_get(v_val_3385_, 0);
lean_inc(v_fst_3387_);
lean_dec(v_val_3385_);
v_fst_3388_ = lean_ctor_get(v_snd_3386_, 0);
lean_inc(v_fst_3388_);
v_snd_3389_ = lean_ctor_get(v_snd_3386_, 1);
lean_inc(v_snd_3389_);
lean_dec(v_snd_3386_);
v___x_3390_ = l_Lean_Meta_Sym_shareCommonInc(v_fst_3387_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v_a_3391_; lean_object* v___x_3392_; 
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
lean_inc(v_a_3391_);
lean_dec_ref_known(v___x_3390_, 1);
v___x_3392_ = l_Lean_Meta_Sym_shareCommonInc(v_fst_3388_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
if (lean_obj_tag(v___x_3392_) == 0)
{
lean_object* v_a_3393_; lean_object* v___x_3394_; 
v_a_3393_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_a_3393_);
lean_dec_ref_known(v___x_3392_, 1);
v___x_3394_ = l_Lean_Meta_Sym_mkAndS(v_a_3391_, v_a_3393_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3404_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3397_ = v___x_3394_;
v_isShared_3398_ = v_isSharedCheck_3404_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3394_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3404_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
uint8_t v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3402_; 
v___x_3399_ = 0;
v___x_3400_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3400_, 0, v_a_3395_);
lean_ctor_set(v___x_3400_, 1, v_snd_3389_);
lean_ctor_set_uint8(v___x_3400_, sizeof(void*)*2, v___x_3399_);
lean_ctor_set_uint8(v___x_3400_, sizeof(void*)*2 + 1, v___x_3399_);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 0, v___x_3400_);
v___x_3402_ = v___x_3397_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v___x_3400_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
else
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
lean_dec(v_snd_3389_);
v_a_3405_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3407_ = v___x_3394_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3394_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3405_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_dec(v_a_3391_);
lean_dec(v_snd_3389_);
v_a_3413_ = lean_ctor_get(v___x_3392_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3392_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3392_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
else
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_dec(v_snd_3389_);
lean_dec(v_fst_3388_);
v_a_3421_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3390_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3390_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
else
{
lean_object* v___x_3429_; lean_object* v___x_3431_; 
lean_dec(v_a_3381_);
v___x_3429_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 0, v___x_3429_);
v___x_3431_ = v___x_3383_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3429_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
v_a_3434_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3380_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3380_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
}
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
lean_dec_ref(v_e_3346_);
v_a_3443_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v___x_3367_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3367_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpForall___boxed(lean_object* v_e_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l_Lean_Meta_Grind_NormSym_simpForall(v_e_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_);
lean_dec(v_a_3753_);
lean_dec_ref(v_a_3752_);
lean_dec(v_a_3751_);
lean_dec_ref(v_a_3750_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_a_3745_);
return v_res_3755_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__6(void){
_start:
{
lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3769_ = lean_box(0);
v___x_3770_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__5));
v___x_3771_ = l_Lean_mkConst(v___x_3770_, v___x_3769_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg(lean_object* v_e_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_){
_start:
{
lean_object* v___x_3801_; uint8_t v___x_3802_; 
v___x_3801_ = l_Lean_Expr_cleanupAnnotations(v_e_3787_);
v___x_3802_ = l_Lean_Expr_isApp(v___x_3801_);
if (v___x_3802_ == 0)
{
lean_dec_ref(v___x_3801_);
goto v___jp_3798_;
}
else
{
lean_object* v___x_3803_; uint8_t v___x_3804_; 
v___x_3803_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3801_);
v___x_3804_ = l_Lean_Expr_isApp(v___x_3803_);
if (v___x_3804_ == 0)
{
lean_dec_ref(v___x_3803_);
lean_dec_ref(v___x_3801_);
goto v___jp_3798_;
}
else
{
lean_object* v___x_3805_; lean_object* v___x_3806_; uint8_t v___x_3807_; 
v___x_3805_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3803_);
v___x_3806_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_etaReduce___closed__1));
v___x_3807_ = l_Lean_Expr_isConstOf(v___x_3805_, v___x_3806_);
if (v___x_3807_ == 0)
{
lean_dec_ref(v___x_3805_);
lean_dec_ref(v___x_3803_);
lean_dec_ref(v___x_3801_);
goto v___jp_3798_;
}
else
{
lean_object* v_arg_3808_; 
v_arg_3808_ = lean_ctor_get(v___x_3801_, 1);
lean_inc_ref(v_arg_3808_);
lean_dec_ref(v___x_3801_);
if (lean_obj_tag(v_arg_3808_) == 6)
{
lean_object* v_binderName_3809_; lean_object* v_body_3810_; lean_object* v_arg_3811_; lean_object* v_u_3812_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; uint8_t v___x_3897_; 
v_binderName_3809_ = lean_ctor_get(v_arg_3808_, 0);
lean_inc(v_binderName_3809_);
v_body_3810_ = lean_ctor_get(v_arg_3808_, 2);
lean_inc_ref(v_body_3810_);
lean_dec_ref_known(v_arg_3808_, 3);
v_arg_3811_ = lean_ctor_get(v___x_3803_, 1);
lean_inc_ref(v_arg_3811_);
lean_dec_ref(v___x_3803_);
v_u_3812_ = l_Lean_Expr_constLevels_x21(v___x_3805_);
v___x_3897_ = l_Lean_Expr_isApp(v_body_3810_);
if (v___x_3897_ == 0)
{
lean_dec(v_binderName_3809_);
lean_dec_ref(v___x_3805_);
v___y_3814_ = v_a_3788_;
v___y_3815_ = v_a_3789_;
v___y_3816_ = v_a_3790_;
v___y_3817_ = v_a_3791_;
v___y_3818_ = v_a_3792_;
v___y_3819_ = v_a_3793_;
goto v___jp_3813_;
}
else
{
lean_object* v___x_3898_; lean_object* v___x_3899_; uint8_t v___x_3900_; 
v___x_3898_ = l_Lean_Expr_getAppNumArgs(v_body_3810_);
v___x_3899_ = lean_unsigned_to_nat(2u);
v___x_3900_ = lean_nat_dec_eq(v___x_3898_, v___x_3899_);
lean_dec(v___x_3898_);
if (v___x_3900_ == 0)
{
lean_dec(v_binderName_3809_);
lean_dec_ref(v___x_3805_);
v___y_3814_ = v_a_3788_;
v___y_3815_ = v_a_3789_;
v___y_3816_ = v_a_3790_;
v___y_3817_ = v_a_3791_;
v___y_3818_ = v_a_3792_;
v___y_3819_ = v_a_3793_;
goto v___jp_3813_;
}
else
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = l_Lean_Expr_appFn_x21(v_body_3810_);
v___x_3902_ = l_Lean_Expr_appFn_x21(v___x_3901_);
if (lean_obj_tag(v___x_3902_) == 4)
{
lean_object* v_declName_3903_; lean_object* v___x_3904_; uint8_t v___x_3905_; 
v_declName_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_declName_3903_);
lean_dec_ref_known(v___x_3902_, 2);
v___x_3904_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__12));
v___x_3905_ = lean_name_eq(v_declName_3903_, v___x_3904_);
if (v___x_3905_ == 0)
{
lean_object* v___x_3906_; uint8_t v___x_3907_; 
v___x_3906_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_pushNot___closed__14));
v___x_3907_ = lean_name_eq(v_declName_3903_, v___x_3906_);
lean_dec(v_declName_3903_);
if (v___x_3907_ == 0)
{
lean_dec_ref(v___x_3901_);
lean_dec(v_binderName_3809_);
lean_dec_ref(v___x_3805_);
v___y_3814_ = v_a_3788_;
v___y_3815_ = v_a_3789_;
v___y_3816_ = v_a_3790_;
v___y_3817_ = v_a_3791_;
v___y_3818_ = v_a_3792_;
v___y_3819_ = v_a_3793_;
goto v___jp_3813_;
}
else
{
lean_object* v_b_3908_; lean_object* v_b_3909_; uint8_t v___x_3910_; 
v_b_3908_ = l_Lean_Expr_appArg_x21(v___x_3901_);
lean_dec_ref(v___x_3901_);
v_b_3909_ = l_Lean_Expr_appArg_x21(v_body_3810_);
v___x_3910_ = l_Lean_Expr_hasLooseBVars(v_b_3908_);
if (v___x_3910_ == 0)
{
uint8_t v___x_3911_; lean_object* v___x_3912_; 
lean_dec_ref(v_body_3810_);
v___x_3911_ = 0;
lean_inc_ref(v_arg_3811_);
v___x_3912_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_binderName_3809_, v___x_3911_, v_arg_3811_, v_b_3909_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; lean_object* v___x_3914_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc_n(v_a_3913_, 2);
lean_dec_ref_known(v___x_3912_, 1);
lean_inc_ref(v_arg_3811_);
v___x_3914_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___redArg(v___x_3805_, v_arg_3811_, v_a_3913_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_a_3915_; lean_object* v___x_3916_; 
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc(v_a_3915_);
lean_dec_ref_known(v___x_3914_, 1);
lean_inc_ref(v_b_3908_);
v___x_3916_ = l_Lean_Meta_Sym_mkAndS(v_b_3908_, v_a_3915_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3928_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3919_ = v___x_3916_;
v_isShared_3920_ = v_isSharedCheck_3928_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_dec(v___x_3916_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3928_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3926_; 
v___x_3921_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__8));
v___x_3922_ = l_Lean_mkConst(v___x_3921_, v_u_3812_);
v___x_3923_ = l_Lean_mkApp3(v___x_3922_, v_arg_3811_, v_a_3913_, v_b_3908_);
v___x_3924_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3924_, 0, v_a_3917_);
lean_ctor_set(v___x_3924_, 1, v___x_3923_);
lean_ctor_set_uint8(v___x_3924_, sizeof(void*)*2, v___x_3905_);
lean_ctor_set_uint8(v___x_3924_, sizeof(void*)*2 + 1, v___x_3905_);
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 0, v___x_3924_);
v___x_3926_ = v___x_3919_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3924_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
else
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3936_; 
lean_dec(v_a_3913_);
lean_dec_ref(v_b_3908_);
lean_dec(v_u_3812_);
lean_dec_ref(v_arg_3811_);
v_a_3929_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3931_ = v___x_3916_;
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3916_);
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
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
lean_dec(v_a_3913_);
lean_dec_ref(v_b_3908_);
lean_dec(v_u_3812_);
lean_dec_ref(v_arg_3811_);
v_a_3937_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3914_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3914_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
lean_dec_ref(v_b_3908_);
lean_dec(v_u_3812_);
lean_dec_ref(v_arg_3811_);
lean_dec_ref(v___x_3805_);
v_a_3945_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3947_ = v___x_3912_;
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3912_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
}
else
{
uint8_t v___x_3953_; 
v___x_3953_ = l_Lean_Expr_hasLooseBVars(v_b_3909_);
if (v___x_3953_ == 0)
{
uint8_t v___x_3954_; lean_object* v___x_3955_; 
lean_dec_ref(v_body_3810_);
v___x_3954_ = 0;
lean_inc_ref(v_arg_3811_);
v___x_3955_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_binderName_3809_, v___x_3954_, v_arg_3811_, v_b_3908_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_);
if (lean_obj_tag(v___x_3955_) == 0)
{
lean_object* v_a_3956_; lean_object* v___x_3957_; 
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
lean_inc_n(v_a_3956_, 2);
lean_dec_ref_known(v___x_3955_, 1);
lean_inc_ref(v_arg_3811_);
v___x_3957_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___redArg(v___x_3805_, v_arg_3811_, v_a_3956_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; lean_object* v___x_3959_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_a_3958_);
lean_dec_ref_known(v___x_3957_, 1);
lean_inc_ref(v_b_3909_);
v___x_3959_ = l_Lean_Meta_Sym_mkAndS(v_a_3958_, v_b_3909_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_);
if (lean_obj_tag(v___x_3959_) == 0)
{
lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3971_; 
v_a_3960_ = lean_ctor_get(v___x_3959_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3959_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3962_ = v___x_3959_;
v_isShared_3963_ = v_isSharedCheck_3971_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___x_3959_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3971_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3969_; 
v___x_3964_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__10));
v___x_3965_ = l_Lean_mkConst(v___x_3964_, v_u_3812_);
v___x_3966_ = l_Lean_mkApp3(v___x_3965_, v_arg_3811_, v_a_3956_, v_b_3909_);
v___x_3967_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3967_, 0, v_a_3960_);
lean_ctor_set(v___x_3967_, 1, v___x_3966_);
lean_ctor_set_uint8(v___x_3967_, sizeof(void*)*2, v___x_3905_);
lean_ctor_set_uint8(v___x_3967_, sizeof(void*)*2 + 1, v___x_3905_);
if (v_isShared_3963_ == 0)
{
lean_ctor_set(v___x_3962_, 0, v___x_3967_);
v___x_3969_ = v___x_3962_;
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
else
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3979_; 
lean_dec(v_a_3956_);
lean_dec_ref(v_b_3909_);
lean_dec(v_u_3812_);
lean_dec_ref(v_arg_3811_);
v_a_3972_ = lean_ctor_get(v___x_3959_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3959_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3974_ = v___x_3959_;
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3959_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3972_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_dec(v_a_3956_);
lean_dec_ref(v_b_3909_);
lean_dec(v_u_3812_);
lean_dec_ref(v_arg_3811_);
v_a_3980_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3957_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3957_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
else
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
lean_dec_ref(v_b_3909_);
lean_dec(v_u_3812_);
lean_dec_ref(v_arg_3811_);
lean_dec_ref(v___x_3805_);
v_a_3988_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3990_ = v___x_3955_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3955_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
}
else
{
lean_dec_ref(v_b_3909_);
lean_dec_ref(v_b_3908_);
lean_dec(v_binderName_3809_);
lean_dec_ref(v___x_3805_);
v___y_3814_ = v_a_3788_;
v___y_3815_ = v_a_3789_;
v___y_3816_ = v_a_3790_;
v___y_3817_ = v_a_3791_;
v___y_3818_ = v_a_3792_;
v___y_3819_ = v_a_3793_;
goto v___jp_3813_;
}
}
}
}
else
{
lean_object* v_pRaw_3996_; lean_object* v_qRaw_3997_; uint8_t v___x_3998_; lean_object* v___x_3999_; 
lean_dec(v_declName_3903_);
v_pRaw_3996_ = l_Lean_Expr_appArg_x21(v___x_3901_);
lean_dec_ref(v___x_3901_);
v_qRaw_3997_ = l_Lean_Expr_appArg_x21(v_body_3810_);
lean_dec_ref(v_body_3810_);
v___x_3998_ = 0;
lean_inc_ref(v_arg_3811_);
lean_inc(v_binderName_3809_);
v___x_3999_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_binderName_3809_, v___x_3998_, v_arg_3811_, v_pRaw_3996_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; lean_object* v___x_4001_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc(v_a_4000_);
lean_dec_ref_known(v___x_3999_, 1);
lean_inc_ref(v_arg_3811_);
v___x_4001_ = l_Lean_Meta_Sym_Internal_mkLambdaS___at___00Lean_Meta_Grind_NormSym_pushNot_spec__0___redArg(v_binderName_3809_, v___x_3998_, v_arg_3811_, v_qRaw_3997_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_object* v_a_4002_; lean_object* v___x_4003_; 
v_a_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc(v_a_4002_);
lean_dec_ref_known(v___x_4001_, 1);
lean_inc(v_a_4000_);
lean_inc_ref(v_arg_3811_);
lean_inc_ref(v___x_3805_);
v___x_4003_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___redArg(v___x_3805_, v_arg_3811_, v_a_4000_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v_a_4004_; lean_object* v___x_4005_; 
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc(v_a_4004_);
lean_dec_ref_known(v___x_4003_, 1);
lean_inc(v_a_4002_);
lean_inc_ref(v_arg_3811_);
v___x_4005_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Grind_NormSym_simpEq_spec__0_spec__0___redArg(v___x_3805_, v_arg_3811_, v_a_4002_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; lean_object* v___x_4007_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_a_4006_);
lean_dec_ref_known(v___x_4005_, 1);
v___x_4007_ = l_Lean_Meta_Sym_mkOrS(v_a_4004_, v_a_4006_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4020_; 
v_a_4008_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4010_ = v___x_4007_;
v_isShared_4011_ = v_isSharedCheck_4020_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_4007_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4020_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; uint8_t v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4018_; 
v___x_4012_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__12));
v___x_4013_ = l_Lean_mkConst(v___x_4012_, v_u_3812_);
v___x_4014_ = l_Lean_mkApp3(v___x_4013_, v_arg_3811_, v_a_4000_, v_a_4002_);
v___x_4015_ = 0;
v___x_4016_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_4016_, 0, v_a_4008_);
lean_ctor_set(v___x_4016_, 1, v___x_4014_);
lean_ctor_set_uint8(v___x_4016_, sizeof(void*)*2, v___x_4015_);
lean_ctor_set_uint8(v___x_4016_, sizeof(void*)*2 + 1, v___x_4015_);
if (v_isShared_4011_ == 0)
{
lean_ctor_set(v___x_4010_, 0, v___x_4016_);
v___x_4018_ = v___x_4010_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v___x_4016_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
else
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
lean_dec(v_a_4002_);
lean_dec(v_a_4000_);
lean_dec(v_u_3812_);
lean_dec_ref(v_arg_3811_);
v_a_4021_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4023_ = v___x_4007_;
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___x_4007_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4026_; 
if (v_isShared_4024_ == 0)
{
v___x_4026_ = v___x_4023_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4021_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
}
else
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
lean_dec(v_a_4004_);
lean_dec(v_a_4002_);
lean_dec(v_a_4000_);
lean_dec(v_u_3812_);
lean_dec_ref(v_arg_3811_);
v_a_4029_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_4005_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4005_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
else
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
lean_dec(v_a_4002_);
lean_dec(v_a_4000_);
lean_dec(v_u_3812_);
lean_dec_ref(v_arg_3811_);
lean_dec_ref(v___x_3805_);
v_a_4037_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___x_4003_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4003_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
lean_dec(v_a_4000_);
lean_dec(v_u_3812_);
lean_dec_ref(v_arg_3811_);
lean_dec_ref(v___x_3805_);
v_a_4045_ = lean_ctor_get(v___x_4001_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4001_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___x_4001_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___x_4001_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
else
{
lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4060_; 
lean_dec_ref(v_qRaw_3997_);
lean_dec(v_u_3812_);
lean_dec_ref(v_arg_3811_);
lean_dec(v_binderName_3809_);
lean_dec_ref(v___x_3805_);
v_a_4053_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4055_ = v___x_3999_;
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_3999_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4058_; 
if (v_isShared_4056_ == 0)
{
v___x_4058_ = v___x_4055_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4053_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
}
}
else
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
lean_dec_ref(v___x_3902_);
lean_dec_ref(v___x_3901_);
lean_dec(v_u_3812_);
lean_dec_ref(v_arg_3811_);
lean_dec_ref(v_body_3810_);
lean_dec(v_binderName_3809_);
lean_dec_ref(v___x_3805_);
v___x_4061_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_4062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4062_, 0, v___x_4061_);
return v___x_4062_;
}
}
}
v___jp_3813_:
{
uint8_t v___x_3820_; 
v___x_3820_ = l_Lean_Expr_hasLooseBVars(v_body_3810_);
if (v___x_3820_ == 0)
{
lean_object* v___x_3821_; 
lean_inc_ref(v_arg_3811_);
v___x_3821_ = l_Lean_Meta_isProp(v_arg_3811_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; uint8_t v___x_3823_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_a_3822_);
lean_dec_ref_known(v___x_3821_, 1);
v___x_3823_ = lean_unbox(v_a_3822_);
if (v___x_3823_ == 0)
{
lean_object* v___x_3824_; lean_object* v___x_3825_; 
v___x_3824_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__1));
lean_inc(v_u_3812_);
v___x_3825_ = l_Lean_Meta_Sym_Internal_mkConstS___at___00Lean_Meta_Grind_NormSym_simpDIte_spec__0___redArg(v___x_3824_, v_u_3812_, v___y_3815_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v_a_3826_; lean_object* v___x_3827_; 
v_a_3826_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_a_3826_);
lean_dec_ref_known(v___x_3825_, 1);
lean_inc_ref(v_arg_3811_);
v___x_3827_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Tactic_Grind_NormSymProcs_0__Lean_Meta_Grind_NormSym_etaReduce_go_spec__0___redArg(v_a_3826_, v_arg_3811_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_object* v_a_3828_; lean_object* v___x_3829_; 
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
lean_inc(v_a_3828_);
lean_dec_ref_known(v___x_3827_, 1);
v___x_3829_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_a_3828_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_a_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3844_; 
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3832_ = v___x_3829_;
v_isShared_3833_ = v_isSharedCheck_3844_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_a_3830_);
lean_dec(v___x_3829_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3844_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
if (lean_obj_tag(v_a_3830_) == 1)
{
lean_object* v_val_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; uint8_t v___x_3839_; uint8_t v___x_3840_; lean_object* v___x_3842_; 
v_val_3834_ = lean_ctor_get(v_a_3830_, 0);
lean_inc(v_val_3834_);
lean_dec_ref_known(v_a_3830_, 1);
v___x_3835_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__3));
v___x_3836_ = l_Lean_mkConst(v___x_3835_, v_u_3812_);
lean_inc_ref(v_body_3810_);
v___x_3837_ = l_Lean_mkApp3(v___x_3836_, v_arg_3811_, v_val_3834_, v_body_3810_);
v___x_3838_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3838_, 0, v_body_3810_);
lean_ctor_set(v___x_3838_, 1, v___x_3837_);
v___x_3839_ = lean_unbox(v_a_3822_);
lean_ctor_set_uint8(v___x_3838_, sizeof(void*)*2, v___x_3839_);
v___x_3840_ = lean_unbox(v_a_3822_);
lean_dec(v_a_3822_);
lean_ctor_set_uint8(v___x_3838_, sizeof(void*)*2 + 1, v___x_3840_);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 0, v___x_3838_);
v___x_3842_ = v___x_3832_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v___x_3838_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
else
{
lean_del_object(v___x_3832_);
lean_dec(v_a_3830_);
lean_dec(v_a_3822_);
lean_dec(v_u_3812_);
lean_dec_ref(v_arg_3811_);
lean_dec_ref(v_body_3810_);
goto v___jp_3795_;
}
}
}
else
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
lean_dec(v_a_3822_);
lean_dec(v_u_3812_);
lean_dec_ref(v_arg_3811_);
lean_dec_ref(v_body_3810_);
v_a_3845_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___x_3829_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3829_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
else
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
lean_dec(v_a_3822_);
lean_dec(v_u_3812_);
lean_dec_ref(v_arg_3811_);
lean_dec_ref(v_body_3810_);
v_a_3853_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3827_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3827_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
}
else
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3868_; 
lean_dec(v_a_3822_);
lean_dec(v_u_3812_);
lean_dec_ref(v_arg_3811_);
lean_dec_ref(v_body_3810_);
v_a_3861_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3863_ = v___x_3825_;
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3825_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3861_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
}
else
{
lean_object* v___x_3869_; 
lean_dec(v_a_3822_);
lean_dec(v_u_3812_);
lean_inc_ref(v_body_3810_);
lean_inc_ref(v_arg_3811_);
v___x_3869_ = l_Lean_Meta_Sym_mkAndS(v_arg_3811_, v_body_3810_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3880_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3869_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3872_ = v___x_3869_;
v_isShared_3873_ = v_isSharedCheck_3880_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3869_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3880_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3878_; 
v___x_3874_ = lean_obj_once(&l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__6, &l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__6_once, _init_l_Lean_Meta_Grind_NormSym_simpExists___redArg___closed__6);
v___x_3875_ = l_Lean_mkAppB(v___x_3874_, v_arg_3811_, v_body_3810_);
v___x_3876_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3876_, 0, v_a_3870_);
lean_ctor_set(v___x_3876_, 1, v___x_3875_);
lean_ctor_set_uint8(v___x_3876_, sizeof(void*)*2, v___x_3820_);
lean_ctor_set_uint8(v___x_3876_, sizeof(void*)*2 + 1, v___x_3820_);
if (v_isShared_3873_ == 0)
{
lean_ctor_set(v___x_3872_, 0, v___x_3876_);
v___x_3878_ = v___x_3872_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3876_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
else
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3888_; 
lean_dec_ref(v_arg_3811_);
lean_dec_ref(v_body_3810_);
v_a_3881_ = lean_ctor_get(v___x_3869_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3869_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3883_ = v___x_3869_;
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3869_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3886_; 
if (v_isShared_3884_ == 0)
{
v___x_3886_ = v___x_3883_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3881_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
}
else
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
lean_dec(v_u_3812_);
lean_dec_ref(v_arg_3811_);
lean_dec_ref(v_body_3810_);
v_a_3889_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3821_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3821_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
}
}
}
}
else
{
lean_dec(v_u_3812_);
lean_dec_ref(v_arg_3811_);
lean_dec_ref(v_body_3810_);
goto v___jp_3795_;
}
}
}
else
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
lean_dec_ref(v_arg_3808_);
lean_dec_ref(v___x_3805_);
lean_dec_ref(v___x_3803_);
v___x_4063_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_4064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4064_, 0, v___x_4063_);
return v___x_4064_;
}
}
}
}
v___jp_3795_:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3796_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3796_);
return v___x_3797_;
}
v___jp_3798_:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3799_ = ((lean_object*)(l_Lean_Meta_Grind_NormSym_eraseMData___redArg___closed__0));
v___x_3800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3799_);
return v___x_3800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists___redArg___boxed(lean_object* v_e_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_){
_start:
{
lean_object* v_res_4073_; 
v_res_4073_ = l_Lean_Meta_Grind_NormSym_simpExists___redArg(v_e_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_);
lean_dec(v_a_4071_);
lean_dec_ref(v_a_4070_);
lean_dec(v_a_4069_);
lean_dec_ref(v_a_4068_);
lean_dec(v_a_4067_);
lean_dec_ref(v_a_4066_);
lean_dec_ref(v_e_4065_);
return v_res_4073_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists(lean_object* v_e_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_){
_start:
{
lean_object* v___x_4085_; 
v___x_4085_ = l_Lean_Meta_Grind_NormSym_simpExists___redArg(v_e_4074_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_, v_a_4083_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormSym_simpExists___boxed(lean_object* v_e_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_){
_start:
{
lean_object* v_res_4097_; 
v_res_4097_ = l_Lean_Meta_Grind_NormSym_simpExists(v_e_4086_, v_a_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_, v_a_4093_, v_a_4094_, v_a_4095_);
lean_dec(v_a_4095_);
lean_dec_ref(v_a_4094_);
lean_dec(v_a_4093_);
lean_dec_ref(v_a_4092_);
lean_dec(v_a_4091_);
lean_dec_ref(v_a_4090_);
lean_dec(v_a_4089_);
lean_dec_ref(v_a_4088_);
lean_dec(v_a_4087_);
lean_dec_ref(v_e_4086_);
return v_res_4097_;
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

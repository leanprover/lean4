// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.Reduction
// Imports: public import Lean.Meta.Tactic.BVDecide.Normalize.Basic import Lean.Meta.Sym.Simp.Theorems import Lean.Meta.Sym.DSimp
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_evalGround___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___closed__0;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__0_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__0_value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__1_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__1_value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__2_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__2_value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__3_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__4_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5___boxed, .m_arity = 13, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__3_value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__5_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__5_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__4_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__7_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__8_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__9_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__10_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__10_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__9_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__10_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__11_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__12_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "  ==>  "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__14_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__15;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reductionPass"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(99, 173, 196, 173, 194, 157, 239, 250)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0___redArg(lean_object* v_declName_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_4_; lean_object* v_env_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = lean_st_ref_get(v___y_2_);
v_env_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_env_5_);
lean_dec(v___x_4_);
v___x_6_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_5_, v_declName_1_);
v___x_7_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0___redArg___boxed(lean_object* v_declName_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0___redArg(v_declName_8_, v___y_9_);
lean_dec(v___y_9_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0(lean_object* v_declName_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0___redArg(v_declName_12_, v___y_21_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0___boxed(lean_object* v_declName_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0(v_declName_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
lean_dec(v___y_31_);
lean_dec_ref(v___y_30_);
lean_dec(v___y_29_);
lean_dec_ref(v___y_28_);
lean_dec(v___y_27_);
lean_dec_ref(v___y_26_);
lean_dec(v___y_25_);
return v_res_35_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___closed__0(void){
_start:
{
lean_object* v___x_36_; lean_object* v_dummy_37_; 
v___x_36_ = lean_box(0);
v_dummy_37_ = l_Lean_Expr_sort___override(v___x_36_);
return v_dummy_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27(lean_object* v_e_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_){
_start:
{
lean_object* v_f_51_; 
v_f_51_ = l_Lean_Expr_getAppFn(v_e_40_);
if (lean_obj_tag(v_f_51_) == 4)
{
lean_object* v_declName_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v_a_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_99_; 
v_declName_52_ = lean_ctor_get(v_f_51_, 0);
lean_inc(v_declName_52_);
lean_dec_ref_known(v_f_51_, 2);
v___x_53_ = l_Lean_instInhabitedExpr;
v___x_54_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0___redArg(v_declName_52_, v_a_49_);
v_a_55_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_99_ == 0)
{
v___x_57_ = v___x_54_;
v_isShared_58_ = v_isSharedCheck_99_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_a_55_);
lean_dec(v___x_54_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_99_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
if (lean_obj_tag(v_a_55_) == 1)
{
lean_object* v_val_59_; lean_object* v_numParams_60_; lean_object* v_nargs_61_; lean_object* v_dummy_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v_val_59_ = lean_ctor_get(v_a_55_, 0);
lean_inc(v_val_59_);
lean_dec_ref_known(v_a_55_, 1);
v_numParams_60_ = lean_ctor_get(v_val_59_, 1);
lean_inc(v_numParams_60_);
lean_dec(v_val_59_);
v_nargs_61_ = l_Lean_Expr_getAppNumArgs(v_e_40_);
v_dummy_62_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___closed__0);
lean_inc(v_nargs_61_);
v___x_63_ = lean_mk_array(v_nargs_61_, v_dummy_62_);
v___x_64_ = lean_unsigned_to_nat(1u);
v___x_65_ = lean_nat_sub(v_nargs_61_, v___x_64_);
lean_dec(v_nargs_61_);
lean_inc_ref(v_e_40_);
v___x_66_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_40_, v___x_63_, v___x_65_);
v___x_67_ = lean_array_get_size(v___x_66_);
v___x_68_ = lean_nat_dec_lt(v_numParams_60_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_71_; 
lean_dec_ref(v___x_66_);
lean_dec(v_numParams_60_);
lean_dec_ref(v_e_40_);
v___x_69_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_69_, 0, v___x_68_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_69_);
v___x_71_ = v___x_57_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_69_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
else
{
lean_object* v___x_73_; lean_object* v___x_74_; 
lean_del_object(v___x_57_);
v___x_73_ = lean_array_get(v___x_53_, v___x_66_, v_numParams_60_);
lean_dec(v_numParams_60_);
lean_dec_ref(v___x_66_);
v___x_74_ = l_Lean_Meta_isConstructorApp(v___x_73_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_86_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_86_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_86_ == 0)
{
v___x_77_ = v___x_74_;
v_isShared_78_ = v_isSharedCheck_86_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_74_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_86_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
uint8_t v___x_79_; 
v___x_79_ = lean_unbox(v_a_75_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; uint8_t v___x_81_; lean_object* v___x_83_; 
lean_dec_ref(v_e_40_);
v___x_80_ = lean_alloc_ctor(0, 0, 1);
v___x_81_ = lean_unbox(v_a_75_);
lean_dec(v_a_75_);
lean_ctor_set_uint8(v___x_80_, 0, v___x_81_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_80_);
v___x_83_ = v___x_77_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_80_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
else
{
lean_object* v___x_85_; 
lean_del_object(v___x_77_);
lean_dec(v_a_75_);
v___x_85_ = l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(v_e_40_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
return v___x_85_;
}
}
}
else
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_94_; 
lean_dec_ref(v_e_40_);
v_a_87_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_94_ == 0)
{
v___x_89_ = v___x_74_;
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_74_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_94_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_92_; 
if (v_isShared_90_ == 0)
{
v___x_92_ = v___x_89_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_a_87_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
}
else
{
lean_object* v___x_95_; lean_object* v___x_97_; 
lean_dec(v_a_55_);
lean_dec_ref(v_e_40_);
v___x_95_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___closed__1));
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_95_);
v___x_97_ = v___x_57_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_95_);
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
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec_ref(v_f_51_);
lean_dec_ref(v_e_40_);
v___x_100_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___closed__1));
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___boxed(lean_object* v_e_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27(v_e_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___lam__0(lean_object* v_x_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v___x_127_; 
lean_inc(v___y_121_);
lean_inc_ref(v___y_120_);
lean_inc(v___y_119_);
lean_inc_ref(v___y_118_);
lean_inc(v___y_117_);
lean_inc(v___y_116_);
lean_inc_ref(v___y_115_);
v___x_127_ = lean_apply_12(v_x_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, lean_box(0));
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___lam__0___boxed(lean_object* v_x_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___lam__0(v_x_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg(lean_object* v_mvarId_142_, lean_object* v_x_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v___f_156_; lean_object* v___x_157_; 
lean_inc(v___y_150_);
lean_inc_ref(v___y_149_);
lean_inc(v___y_148_);
lean_inc_ref(v___y_147_);
lean_inc(v___y_146_);
lean_inc(v___y_145_);
lean_inc_ref(v___y_144_);
v___f_156_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_156_, 0, v_x_143_);
lean_closure_set(v___f_156_, 1, v___y_144_);
lean_closure_set(v___f_156_, 2, v___y_145_);
lean_closure_set(v___f_156_, 3, v___y_146_);
lean_closure_set(v___f_156_, 4, v___y_147_);
lean_closure_set(v___f_156_, 5, v___y_148_);
lean_closure_set(v___f_156_, 6, v___y_149_);
lean_closure_set(v___f_156_, 7, v___y_150_);
v___x_157_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_142_, v___f_156_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
if (lean_obj_tag(v___x_157_) == 0)
{
return v___x_157_;
}
else
{
lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_165_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_165_ == 0)
{
v___x_160_ = v___x_157_;
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_163_; 
if (v_isShared_161_ == 0)
{
v___x_163_ = v___x_160_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_a_158_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___boxed(lean_object* v_mvarId_166_, lean_object* v_x_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg(v_mvarId_166_, v_x_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2(lean_object* v_00_u03b1_181_, lean_object* v_mvarId_182_, lean_object* v_x_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg(v_mvarId_182_, v_x_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___boxed(lean_object* v_00_u03b1_197_, lean_object* v_mvarId_198_, lean_object* v_x_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2(v_00_u03b1_197_, v_mvarId_198_, v_x_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0(lean_object* v_x_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v___y_214_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
if (lean_obj_tag(v_a_226_) == 0)
{
uint8_t v_done_227_; 
v_done_227_ = lean_ctor_get_uint8(v_a_226_, 0);
lean_dec_ref_known(v_a_226_, 0);
if (v_done_227_ == 0)
{
lean_object* v___x_228_; 
lean_dec_ref_known(v___x_225_, 1);
v___x_228_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27(v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
return v___x_228_;
}
else
{
lean_dec_ref(v___y_214_);
return v___x_225_;
}
}
else
{
uint8_t v_done_229_; 
lean_dec_ref(v___y_214_);
v_done_229_ = lean_ctor_get_uint8(v_a_226_, sizeof(void*)*1);
if (v_done_229_ == 0)
{
lean_object* v_e_x27_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_248_; 
lean_dec_ref_known(v___x_225_, 1);
v_e_x27_230_ = lean_ctor_get(v_a_226_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v_a_226_);
if (v_isSharedCheck_248_ == 0)
{
v___x_232_ = v_a_226_;
v_isShared_233_ = v_isSharedCheck_248_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_e_x27_230_);
lean_dec(v_a_226_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_248_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; 
lean_inc_ref(v_e_x27_230_);
v___x_234_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27(v_e_x27_230_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
if (lean_obj_tag(v_a_235_) == 0)
{
lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_246_; 
lean_inc_ref(v_a_235_);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; 
v_unused_247_ = lean_ctor_get(v___x_234_, 0);
lean_dec(v_unused_247_);
v___x_237_ = v___x_234_;
v_isShared_238_ = v_isSharedCheck_246_;
goto v_resetjp_236_;
}
else
{
lean_dec(v___x_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_246_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
uint8_t v_done_239_; lean_object* v___x_241_; 
v_done_239_ = lean_ctor_get_uint8(v_a_235_, 0);
lean_dec_ref_known(v_a_235_, 0);
if (v_isShared_233_ == 0)
{
v___x_241_ = v___x_232_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_e_x27_230_);
v___x_241_ = v_reuseFailAlloc_245_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_243_; 
lean_ctor_set_uint8(v___x_241_, sizeof(void*)*1, v_done_239_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v___x_241_);
v___x_243_ = v___x_237_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_241_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
else
{
lean_del_object(v___x_232_);
lean_dec_ref(v_e_x27_230_);
return v___x_234_;
}
}
else
{
lean_del_object(v___x_232_);
lean_dec_ref(v_e_x27_230_);
return v___x_234_;
}
}
}
else
{
lean_dec_ref_known(v_a_226_, 1);
return v___x_225_;
}
}
}
else
{
lean_dec_ref(v___y_214_);
return v___x_225_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0___boxed(lean_object* v_x_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0(v_x_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3(lean_object* v___f_262_, lean_object* v_x_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_box(0);
lean_inc_ref(v___y_264_);
v___x_276_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v___y_264_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
if (lean_obj_tag(v_a_277_) == 0)
{
uint8_t v_done_278_; 
v_done_278_ = lean_ctor_get_uint8(v_a_277_, 0);
lean_dec_ref_known(v_a_277_, 0);
if (v_done_278_ == 0)
{
lean_object* v___x_279_; 
lean_dec_ref_known(v___x_276_, 1);
lean_inc(v___y_273_);
lean_inc_ref(v___y_272_);
lean_inc(v___y_271_);
lean_inc_ref(v___y_270_);
lean_inc(v___y_269_);
lean_inc_ref(v___y_268_);
lean_inc(v___y_267_);
lean_inc_ref(v___y_266_);
lean_inc(v___y_265_);
v___x_279_ = lean_apply_12(v___f_262_, v___x_275_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, lean_box(0));
return v___x_279_;
}
else
{
lean_dec_ref(v___y_264_);
lean_dec_ref(v___f_262_);
return v___x_276_;
}
}
else
{
uint8_t v_done_280_; 
lean_dec_ref(v___y_264_);
v_done_280_ = lean_ctor_get_uint8(v_a_277_, sizeof(void*)*1);
if (v_done_280_ == 0)
{
lean_object* v_e_x27_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_299_; 
lean_dec_ref_known(v___x_276_, 1);
v_e_x27_281_ = lean_ctor_get(v_a_277_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v_a_277_);
if (v_isSharedCheck_299_ == 0)
{
v___x_283_ = v_a_277_;
v_isShared_284_ = v_isSharedCheck_299_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_e_x27_281_);
lean_dec(v_a_277_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_299_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; 
lean_inc(v___y_273_);
lean_inc_ref(v___y_272_);
lean_inc(v___y_271_);
lean_inc_ref(v___y_270_);
lean_inc(v___y_269_);
lean_inc_ref(v___y_268_);
lean_inc(v___y_267_);
lean_inc_ref(v___y_266_);
lean_inc(v___y_265_);
lean_inc_ref(v_e_x27_281_);
v___x_285_ = lean_apply_12(v___f_262_, v___x_275_, v_e_x27_281_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, lean_box(0));
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_a_286_);
if (lean_obj_tag(v_a_286_) == 0)
{
lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_297_; 
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; 
v_unused_298_ = lean_ctor_get(v___x_285_, 0);
lean_dec(v_unused_298_);
v___x_288_ = v___x_285_;
v_isShared_289_ = v_isSharedCheck_297_;
goto v_resetjp_287_;
}
else
{
lean_dec(v___x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_297_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
uint8_t v_done_290_; lean_object* v___x_292_; 
v_done_290_ = lean_ctor_get_uint8(v_a_286_, 0);
lean_dec_ref_known(v_a_286_, 0);
if (v_isShared_284_ == 0)
{
v___x_292_ = v___x_283_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_e_x27_281_);
v___x_292_ = v_reuseFailAlloc_296_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_294_; 
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*1, v_done_290_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_292_);
v___x_294_ = v___x_288_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_286_, 1);
lean_del_object(v___x_283_);
lean_dec_ref(v_e_x27_281_);
return v___x_285_;
}
}
else
{
lean_del_object(v___x_283_);
lean_dec_ref(v_e_x27_281_);
return v___x_285_;
}
}
}
else
{
lean_dec_ref_known(v_a_277_, 1);
lean_dec_ref(v___f_262_);
return v___x_276_;
}
}
}
else
{
lean_dec_ref(v___y_264_);
lean_dec_ref(v___f_262_);
return v___x_276_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3___boxed(lean_object* v___f_300_, lean_object* v_x_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3(v___f_300_, v_x_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1(lean_object* v___f_314_, lean_object* v_x_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_box(0);
lean_inc_ref(v___y_316_);
v___x_328_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_316_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_a_329_);
if (lean_obj_tag(v_a_329_) == 0)
{
uint8_t v_done_330_; 
v_done_330_ = lean_ctor_get_uint8(v_a_329_, 0);
lean_dec_ref_known(v_a_329_, 0);
if (v_done_330_ == 0)
{
lean_object* v___x_331_; 
lean_dec_ref_known(v___x_328_, 1);
lean_inc(v___y_325_);
lean_inc_ref(v___y_324_);
lean_inc(v___y_323_);
lean_inc_ref(v___y_322_);
lean_inc(v___y_321_);
lean_inc_ref(v___y_320_);
lean_inc(v___y_319_);
lean_inc_ref(v___y_318_);
lean_inc(v___y_317_);
v___x_331_ = lean_apply_12(v___f_314_, v___x_327_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, lean_box(0));
return v___x_331_;
}
else
{
lean_dec_ref(v___y_316_);
lean_dec_ref(v___f_314_);
return v___x_328_;
}
}
else
{
uint8_t v_done_332_; 
lean_dec_ref(v___y_316_);
v_done_332_ = lean_ctor_get_uint8(v_a_329_, sizeof(void*)*1);
if (v_done_332_ == 0)
{
lean_object* v_e_x27_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_351_; 
lean_dec_ref_known(v___x_328_, 1);
v_e_x27_333_ = lean_ctor_get(v_a_329_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v_a_329_);
if (v_isSharedCheck_351_ == 0)
{
v___x_335_ = v_a_329_;
v_isShared_336_ = v_isSharedCheck_351_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_e_x27_333_);
lean_dec(v_a_329_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_351_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; 
lean_inc(v___y_325_);
lean_inc_ref(v___y_324_);
lean_inc(v___y_323_);
lean_inc_ref(v___y_322_);
lean_inc(v___y_321_);
lean_inc_ref(v___y_320_);
lean_inc(v___y_319_);
lean_inc_ref(v___y_318_);
lean_inc(v___y_317_);
lean_inc_ref(v_e_x27_333_);
v___x_337_ = lean_apply_12(v___f_314_, v___x_327_, v_e_x27_333_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, lean_box(0));
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
if (lean_obj_tag(v_a_338_) == 0)
{
lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_349_; 
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_349_ == 0)
{
lean_object* v_unused_350_; 
v_unused_350_ = lean_ctor_get(v___x_337_, 0);
lean_dec(v_unused_350_);
v___x_340_ = v___x_337_;
v_isShared_341_ = v_isSharedCheck_349_;
goto v_resetjp_339_;
}
else
{
lean_dec(v___x_337_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_349_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
uint8_t v_done_342_; lean_object* v___x_344_; 
v_done_342_ = lean_ctor_get_uint8(v_a_338_, 0);
lean_dec_ref_known(v_a_338_, 0);
if (v_isShared_336_ == 0)
{
v___x_344_ = v___x_335_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_e_x27_333_);
v___x_344_ = v_reuseFailAlloc_348_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_346_; 
lean_ctor_set_uint8(v___x_344_, sizeof(void*)*1, v_done_342_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_344_);
v___x_346_ = v___x_340_;
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
}
else
{
lean_dec_ref_known(v_a_338_, 1);
lean_del_object(v___x_335_);
lean_dec_ref(v_e_x27_333_);
return v___x_337_;
}
}
else
{
lean_del_object(v___x_335_);
lean_dec_ref(v_e_x27_333_);
return v___x_337_;
}
}
}
else
{
lean_dec_ref_known(v_a_329_, 1);
lean_dec_ref(v___f_314_);
return v___x_328_;
}
}
}
else
{
lean_dec_ref(v___y_316_);
lean_dec_ref(v___f_314_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1___boxed(lean_object* v___f_352_, lean_object* v_x_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1(v___f_352_, v_x_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7(uint8_t v___x_366_, lean_object* v___f_367_, lean_object* v_____r_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; lean_object* v_caches_382_; lean_object* v_typeAnalysis_383_; lean_object* v_target_384_; lean_object* v_hypotheses_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_395_; 
v___x_381_ = lean_st_ref_take(v___y_370_);
v_caches_382_ = lean_ctor_get(v___x_381_, 0);
v_typeAnalysis_383_ = lean_ctor_get(v___x_381_, 1);
v_target_384_ = lean_ctor_get(v___x_381_, 2);
v_hypotheses_385_ = lean_ctor_get(v___x_381_, 3);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_395_ == 0)
{
v___x_387_ = v___x_381_;
v_isShared_388_ = v_isSharedCheck_395_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_hypotheses_385_);
lean_inc(v_target_384_);
lean_inc(v_typeAnalysis_383_);
lean_inc(v_caches_382_);
lean_dec(v___x_381_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_395_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_389_ = lean_box(0);
if (v_isShared_388_ == 0)
{
v___x_391_ = v___x_387_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_caches_382_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_typeAnalysis_383_);
lean_ctor_set(v_reuseFailAlloc_394_, 2, v_target_384_);
lean_ctor_set(v_reuseFailAlloc_394_, 3, v_hypotheses_385_);
v___x_391_ = v_reuseFailAlloc_394_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
lean_ctor_set_uint8(v___x_391_, sizeof(void*)*4, v___x_366_);
v___x_392_ = lean_st_ref_put(v___y_370_, v___x_391_);
lean_inc(v___y_379_);
lean_inc_ref(v___y_378_);
lean_inc(v___y_377_);
lean_inc_ref(v___y_376_);
lean_inc(v___y_375_);
lean_inc_ref(v___y_374_);
lean_inc(v___y_373_);
lean_inc_ref(v___y_372_);
lean_inc(v___y_371_);
lean_inc(v___y_370_);
lean_inc_ref(v___y_369_);
v___x_393_ = lean_apply_13(v___f_367_, v___x_389_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, lean_box(0));
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7___boxed(lean_object* v___x_396_, lean_object* v___f_397_, lean_object* v_____r_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
uint8_t v___x_11565__boxed_411_; lean_object* v_res_412_; 
v___x_11565__boxed_411_ = lean_unbox(v___x_396_);
v_res_412_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7(v___x_11565__boxed_411_, v___f_397_, v_____r_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0(lean_object* v_msgData_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v___x_419_; lean_object* v_env_420_; uint8_t v___x_421_; lean_object* v_env_422_; lean_object* v___x_423_; lean_object* v_toCold_424_; lean_object* v_mctx_425_; lean_object* v_lctx_426_; lean_object* v_options_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_419_ = lean_st_ref_get(v___y_417_);
v_env_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc_ref(v_env_420_);
lean_dec(v___x_419_);
v___x_421_ = 0;
v_env_422_ = l_Lean_Environment_setRecordingDeps(v_env_420_, v___x_421_);
v___x_423_ = lean_st_ref_get(v___y_415_);
v_toCold_424_ = lean_ctor_get(v___y_416_, 0);
v_mctx_425_ = lean_ctor_get(v___x_423_, 0);
lean_inc_ref(v_mctx_425_);
lean_dec(v___x_423_);
v_lctx_426_ = lean_ctor_get(v___y_414_, 2);
v_options_427_ = lean_ctor_get(v_toCold_424_, 2);
lean_inc_ref(v_options_427_);
lean_inc_ref(v_lctx_426_);
v___x_428_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_428_, 0, v_env_422_);
lean_ctor_set(v___x_428_, 1, v_mctx_425_);
lean_ctor_set(v___x_428_, 2, v_lctx_426_);
lean_ctor_set(v___x_428_, 3, v_options_427_);
v___x_429_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v_msgData_413_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0___boxed(lean_object* v_msgData_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0(v_msgData_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_437_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_438_; double v___x_439_; 
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_float_of_nat(v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(lean_object* v_cls_443_, lean_object* v_msg_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_ref_450_; lean_object* v___x_451_; lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_497_; 
v_ref_450_ = lean_ctor_get(v___y_447_, 2);
v___x_451_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0(v_msg_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
v_a_452_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_497_ == 0)
{
v___x_454_ = v___x_451_;
v_isShared_455_ = v_isSharedCheck_497_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_451_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_497_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; lean_object* v_traceState_457_; lean_object* v_env_458_; lean_object* v_nextMacroScope_459_; lean_object* v_ngen_460_; lean_object* v_auxDeclNGen_461_; lean_object* v_cache_462_; lean_object* v_recordedDeps_463_; lean_object* v_messages_464_; lean_object* v_infoState_465_; lean_object* v_snapshotTasks_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_496_; 
v___x_456_ = lean_st_ref_take(v___y_448_);
v_traceState_457_ = lean_ctor_get(v___x_456_, 4);
v_env_458_ = lean_ctor_get(v___x_456_, 0);
v_nextMacroScope_459_ = lean_ctor_get(v___x_456_, 1);
v_ngen_460_ = lean_ctor_get(v___x_456_, 2);
v_auxDeclNGen_461_ = lean_ctor_get(v___x_456_, 3);
v_cache_462_ = lean_ctor_get(v___x_456_, 5);
v_recordedDeps_463_ = lean_ctor_get(v___x_456_, 6);
v_messages_464_ = lean_ctor_get(v___x_456_, 7);
v_infoState_465_ = lean_ctor_get(v___x_456_, 8);
v_snapshotTasks_466_ = lean_ctor_get(v___x_456_, 9);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_496_ == 0)
{
v___x_468_ = v___x_456_;
v_isShared_469_ = v_isSharedCheck_496_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_snapshotTasks_466_);
lean_inc(v_infoState_465_);
lean_inc(v_messages_464_);
lean_inc(v_recordedDeps_463_);
lean_inc(v_cache_462_);
lean_inc(v_traceState_457_);
lean_inc(v_auxDeclNGen_461_);
lean_inc(v_ngen_460_);
lean_inc(v_nextMacroScope_459_);
lean_inc(v_env_458_);
lean_dec(v___x_456_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_496_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
uint64_t v_tid_470_; lean_object* v_traces_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_495_; 
v_tid_470_ = lean_ctor_get_uint64(v_traceState_457_, sizeof(void*)*1);
v_traces_471_ = lean_ctor_get(v_traceState_457_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v_traceState_457_);
if (v_isSharedCheck_495_ == 0)
{
v___x_473_ = v_traceState_457_;
v_isShared_474_ = v_isSharedCheck_495_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_traces_471_);
lean_dec(v_traceState_457_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_495_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v___x_476_; double v___x_477_; uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_475_ = lean_box(0);
v___x_476_ = lean_box(0);
v___x_477_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0);
v___x_478_ = 0;
v___x_479_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__1));
v___x_480_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_480_, 0, v_cls_443_);
lean_ctor_set(v___x_480_, 1, v___x_476_);
lean_ctor_set(v___x_480_, 2, v___x_479_);
lean_ctor_set_float(v___x_480_, sizeof(void*)*3, v___x_477_);
lean_ctor_set_float(v___x_480_, sizeof(void*)*3 + 8, v___x_477_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*3 + 16, v___x_478_);
v___x_481_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__2));
v___x_482_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_482_, 0, v___x_480_);
lean_ctor_set(v___x_482_, 1, v_a_452_);
lean_ctor_set(v___x_482_, 2, v___x_481_);
lean_inc(v_ref_450_);
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v_ref_450_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
v___x_484_ = l_Lean_PersistentArray_push___redArg(v_traces_471_, v___x_483_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_484_);
v___x_486_ = v___x_473_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_484_);
lean_ctor_set_uint64(v_reuseFailAlloc_494_, sizeof(void*)*1, v_tid_470_);
v___x_486_ = v_reuseFailAlloc_494_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_488_; 
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 4, v___x_486_);
v___x_488_ = v___x_468_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_env_458_);
lean_ctor_set(v_reuseFailAlloc_493_, 1, v_nextMacroScope_459_);
lean_ctor_set(v_reuseFailAlloc_493_, 2, v_ngen_460_);
lean_ctor_set(v_reuseFailAlloc_493_, 3, v_auxDeclNGen_461_);
lean_ctor_set(v_reuseFailAlloc_493_, 4, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_493_, 5, v_cache_462_);
lean_ctor_set(v_reuseFailAlloc_493_, 6, v_recordedDeps_463_);
lean_ctor_set(v_reuseFailAlloc_493_, 7, v_messages_464_);
lean_ctor_set(v_reuseFailAlloc_493_, 8, v_infoState_465_);
lean_ctor_set(v_reuseFailAlloc_493_, 9, v_snapshotTasks_466_);
v___x_488_ = v_reuseFailAlloc_493_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_489_ = lean_st_ref_put(v___y_448_, v___x_488_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_475_);
v___x_491_ = v___x_454_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_475_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___boxed(lean_object* v_cls_498_, lean_object* v_msg_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(v_cls_498_, v_msg_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4(lean_object* v_x_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___closed__1));
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4___boxed(lean_object* v_x_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4(v_x_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v_x_519_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2(lean_object* v___f_531_, lean_object* v_x_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_box(0);
lean_inc_ref(v___y_533_);
v___x_545_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_533_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
if (lean_obj_tag(v_a_546_) == 0)
{
uint8_t v_done_547_; 
v_done_547_ = lean_ctor_get_uint8(v_a_546_, 0);
lean_dec_ref_known(v_a_546_, 0);
if (v_done_547_ == 0)
{
lean_object* v___x_548_; 
lean_dec_ref_known(v___x_545_, 1);
lean_inc(v___y_542_);
lean_inc_ref(v___y_541_);
lean_inc(v___y_540_);
lean_inc_ref(v___y_539_);
lean_inc(v___y_538_);
lean_inc_ref(v___y_537_);
lean_inc(v___y_536_);
lean_inc_ref(v___y_535_);
lean_inc(v___y_534_);
v___x_548_ = lean_apply_12(v___f_531_, v___x_544_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, lean_box(0));
return v___x_548_;
}
else
{
lean_dec_ref(v___y_533_);
lean_dec_ref(v___f_531_);
return v___x_545_;
}
}
else
{
uint8_t v_done_549_; 
lean_dec_ref(v___y_533_);
v_done_549_ = lean_ctor_get_uint8(v_a_546_, sizeof(void*)*1);
if (v_done_549_ == 0)
{
lean_object* v_e_x27_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_568_; 
lean_dec_ref_known(v___x_545_, 1);
v_e_x27_550_ = lean_ctor_get(v_a_546_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v_a_546_);
if (v_isSharedCheck_568_ == 0)
{
v___x_552_ = v_a_546_;
v_isShared_553_ = v_isSharedCheck_568_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_e_x27_550_);
lean_dec(v_a_546_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_568_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; 
lean_inc(v___y_542_);
lean_inc_ref(v___y_541_);
lean_inc(v___y_540_);
lean_inc_ref(v___y_539_);
lean_inc(v___y_538_);
lean_inc_ref(v___y_537_);
lean_inc(v___y_536_);
lean_inc_ref(v___y_535_);
lean_inc(v___y_534_);
lean_inc_ref(v_e_x27_550_);
v___x_554_ = lean_apply_12(v___f_531_, v___x_544_, v_e_x27_550_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, lean_box(0));
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
if (lean_obj_tag(v_a_555_) == 0)
{
lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_566_; 
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; 
v_unused_567_ = lean_ctor_get(v___x_554_, 0);
lean_dec(v_unused_567_);
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_566_;
goto v_resetjp_556_;
}
else
{
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_566_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
uint8_t v_done_559_; lean_object* v___x_561_; 
v_done_559_ = lean_ctor_get_uint8(v_a_555_, 0);
lean_dec_ref_known(v_a_555_, 0);
if (v_isShared_553_ == 0)
{
v___x_561_ = v___x_552_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_e_x27_550_);
v___x_561_ = v_reuseFailAlloc_565_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_563_; 
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*1, v_done_559_);
if (v_isShared_558_ == 0)
{
lean_ctor_set(v___x_557_, 0, v___x_561_);
v___x_563_ = v___x_557_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_555_, 1);
lean_del_object(v___x_552_);
lean_dec_ref(v_e_x27_550_);
return v___x_554_;
}
}
else
{
lean_del_object(v___x_552_);
lean_dec_ref(v_e_x27_550_);
return v___x_554_;
}
}
}
else
{
lean_dec_ref_known(v_a_546_, 1);
lean_dec_ref(v___f_531_);
return v___x_545_;
}
}
}
else
{
lean_dec_ref(v___y_533_);
lean_dec_ref(v___f_531_);
return v___x_545_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2___boxed(lean_object* v___f_569_, lean_object* v_x_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2(v___f_569_, v_x_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6(lean_object* v_snd_583_, lean_object* v_a_584_, lean_object* v___x_585_, lean_object* v_____r_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_599_ = lean_array_push(v_snd_583_, v_a_584_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_585_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6___boxed(lean_object* v_snd_603_, lean_object* v_a_604_, lean_object* v___x_605_, lean_object* v_____r_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6(v_snd_603_, v_a_604_, v___x_605_, v_____r_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5(lean_object* v___x_620_, lean_object* v___f_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_box(0);
lean_inc_ref(v___y_622_);
v___x_634_ = l_Lean_Meta_Sym_DSimp_evalGround___redArg(v___x_620_, v___y_622_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
if (lean_obj_tag(v_a_635_) == 0)
{
uint8_t v_done_636_; 
v_done_636_ = lean_ctor_get_uint8(v_a_635_, 0);
lean_dec_ref_known(v_a_635_, 0);
if (v_done_636_ == 0)
{
lean_object* v___x_637_; 
lean_dec_ref_known(v___x_634_, 1);
v___x_637_ = lean_apply_12(v___f_621_, v___x_633_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, lean_box(0));
return v___x_637_;
}
else
{
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec_ref(v___f_621_);
return v___x_634_;
}
}
else
{
uint8_t v_done_638_; 
lean_dec_ref(v___y_622_);
v_done_638_ = lean_ctor_get_uint8(v_a_635_, sizeof(void*)*1);
if (v_done_638_ == 0)
{
lean_object* v_e_x27_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_657_; 
lean_dec_ref_known(v___x_634_, 1);
v_e_x27_639_ = lean_ctor_get(v_a_635_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v_a_635_);
if (v_isSharedCheck_657_ == 0)
{
v___x_641_ = v_a_635_;
v_isShared_642_ = v_isSharedCheck_657_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_e_x27_639_);
lean_dec(v_a_635_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_657_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; 
lean_inc_ref(v_e_x27_639_);
v___x_643_ = lean_apply_12(v___f_621_, v___x_633_, v_e_x27_639_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, lean_box(0));
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_644_);
if (lean_obj_tag(v_a_644_) == 0)
{
lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_655_; 
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_655_ == 0)
{
lean_object* v_unused_656_; 
v_unused_656_ = lean_ctor_get(v___x_643_, 0);
lean_dec(v_unused_656_);
v___x_646_ = v___x_643_;
v_isShared_647_ = v_isSharedCheck_655_;
goto v_resetjp_645_;
}
else
{
lean_dec(v___x_643_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_655_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
uint8_t v_done_648_; lean_object* v___x_650_; 
v_done_648_ = lean_ctor_get_uint8(v_a_644_, 0);
lean_dec_ref_known(v_a_644_, 0);
if (v_isShared_642_ == 0)
{
v___x_650_ = v___x_641_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_e_x27_639_);
v___x_650_ = v_reuseFailAlloc_654_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v___x_652_; 
lean_ctor_set_uint8(v___x_650_, sizeof(void*)*1, v_done_648_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_650_);
v___x_652_ = v___x_646_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_644_, 1);
lean_del_object(v___x_641_);
lean_dec_ref(v_e_x27_639_);
return v___x_643_;
}
}
else
{
lean_del_object(v___x_641_);
lean_dec_ref(v_e_x27_639_);
return v___x_643_;
}
}
}
else
{
lean_dec_ref_known(v_a_635_, 1);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___f_621_);
return v___x_634_;
}
}
}
else
{
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec_ref(v___f_621_);
return v___x_634_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5___boxed(lean_object* v___x_658_, lean_object* v___f_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5(v___x_658_, v___f_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___x_658_);
return v_res_671_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__10));
v___x_697_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__12));
v___x_698_ = l_Lean_Name_append(v___x_697_, v___x_696_);
return v___x_698_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__15(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__14));
v___x_701_ = l_Lean_stringToMessageData(v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg(lean_object* v_upperBound_702_, lean_object* v___x_703_, lean_object* v_config_704_, lean_object* v_a_705_, lean_object* v_b_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v___y_720_; uint8_t v___x_742_; 
v___x_742_ = lean_nat_dec_lt(v_a_705_, v_upperBound_702_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
lean_dec(v_a_705_);
lean_dec_ref(v_config_704_);
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v_b_706_);
return v___x_743_;
}
else
{
lean_object* v_snd_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_818_; 
v_snd_744_ = lean_ctor_get(v_b_706_, 1);
v_isSharedCheck_818_ = !lean_is_exclusive(v_b_706_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; 
v_unused_819_ = lean_ctor_get(v_b_706_, 0);
lean_dec(v_unused_819_);
v___x_746_ = v_b_706_;
v_isShared_747_ = v_isSharedCheck_818_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_snd_744_);
lean_dec(v_b_706_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_818_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
uint8_t v___x_748_; lean_object* v_methods_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_748_ = 1;
v_methods_749_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__6));
v___x_750_ = lean_box(0);
v___x_751_ = lean_array_fget_borrowed(v___x_703_, v_a_705_);
lean_inc(v___x_751_);
lean_inc_ref(v_config_704_);
v___x_752_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v___x_748_, v_methods_749_, v_config_704_, v___x_751_, v___y_708_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v_type_754_; lean_object* v_value_755_; uint8_t v___x_756_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_753_);
lean_dec_ref_known(v___x_752_, 1);
v_type_754_ = lean_ctor_get(v_a_753_, 1);
v_value_755_ = lean_ctor_get(v_a_753_, 2);
lean_inc_ref(v_type_754_);
v___x_756_ = l_Lean_Expr_isFalse(v_type_754_);
if (v___x_756_ == 0)
{
lean_object* v_type_757_; lean_object* v___f_758_; uint8_t v___x_759_; 
lean_del_object(v___x_746_);
v_type_757_ = lean_ctor_get(v___x_751_, 1);
lean_inc(v_a_753_);
lean_inc(v_snd_744_);
v___f_758_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6___boxed), 16, 3);
lean_closure_set(v___f_758_, 0, v_snd_744_);
lean_closure_set(v___f_758_, 1, v_a_753_);
lean_closure_set(v___f_758_, 2, v___x_750_);
v___x_759_ = lean_expr_eqv(v_type_757_, v_type_754_);
if (v___x_759_ == 0)
{
lean_object* v_toCold_760_; lean_object* v_options_761_; lean_object* v_inheritedTraceOptions_762_; uint8_t v_hasTrace_763_; 
lean_inc_ref(v_type_754_);
lean_dec(v_a_753_);
lean_dec(v_snd_744_);
v_toCold_760_ = lean_ctor_get(v___y_716_, 0);
v_options_761_ = lean_ctor_get(v_toCold_760_, 2);
v_inheritedTraceOptions_762_ = lean_ctor_get(v_toCold_760_, 11);
v_hasTrace_763_ = lean_ctor_get_uint8(v_options_761_, sizeof(void*)*1);
if (v_hasTrace_763_ == 0)
{
lean_dec_ref(v_type_754_);
goto v___jp_764_;
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_767_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__10));
v___x_768_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13);
v___x_769_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_762_, v_options_761_, v___x_768_);
if (v___x_769_ == 0)
{
lean_dec_ref(v_type_754_);
goto v___jp_764_;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
lean_inc_ref(v_type_757_);
v___x_770_ = l_Lean_MessageData_ofExpr(v_type_757_);
v___x_771_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__15);
v___x_772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = l_Lean_MessageData_ofExpr(v_type_754_);
v___x_774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_772_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(v___x_767_, v___x_774_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_777_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
v___x_777_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7(v___x_742_, v___f_758_, v_a_776_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
v___y_720_ = v___x_777_;
goto v___jp_719_;
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec_ref(v___f_758_);
lean_dec(v_a_705_);
lean_dec_ref(v_config_704_);
v_a_778_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_775_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_775_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
v___jp_764_:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = lean_box(0);
v___x_766_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7(v___x_742_, v___f_758_, v___x_765_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
v___y_720_ = v___x_766_;
goto v___jp_719_;
}
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; 
lean_dec_ref(v___f_758_);
v___x_786_ = lean_box(0);
v___x_787_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6(v_snd_744_, v_a_753_, v___x_750_, v___x_786_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
v___y_720_ = v___x_787_;
goto v___jp_719_;
}
}
else
{
lean_object* v___x_788_; 
lean_inc_ref(v_value_755_);
lean_dec(v_a_753_);
lean_dec(v_a_705_);
lean_dec_ref(v_config_704_);
v___x_788_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_755_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_800_; 
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_800_ == 0)
{
lean_object* v_unused_801_; 
v_unused_801_ = lean_ctor_get(v___x_788_, 0);
lean_dec(v_unused_801_);
v___x_790_ = v___x_788_;
v_isShared_791_ = v_isSharedCheck_800_;
goto v_resetjp_789_;
}
else
{
lean_dec(v___x_788_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_800_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_792_ = lean_box(v___x_742_);
v___x_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_793_);
v___x_795_ = v___x_746_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_snd_744_);
v___x_795_ = v_reuseFailAlloc_799_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_797_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_795_);
v___x_797_ = v___x_790_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
else
{
lean_object* v_a_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_809_; 
lean_del_object(v___x_746_);
lean_dec(v_snd_744_);
v_a_802_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_809_ == 0)
{
v___x_804_ = v___x_788_;
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_a_802_);
lean_dec(v___x_788_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_809_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_807_; 
if (v_isShared_805_ == 0)
{
v___x_807_ = v___x_804_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_del_object(v___x_746_);
lean_dec(v_snd_744_);
lean_dec(v_a_705_);
lean_dec_ref(v_config_704_);
v_a_810_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_752_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_752_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
v___jp_719_:
{
if (lean_obj_tag(v___y_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_733_; 
v_a_721_ = lean_ctor_get(v___y_720_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___y_720_);
if (v_isSharedCheck_733_ == 0)
{
v___x_723_ = v___y_720_;
v_isShared_724_ = v_isSharedCheck_733_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___y_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_733_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
if (lean_obj_tag(v_a_721_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; 
lean_dec(v_a_705_);
lean_dec_ref(v_config_704_);
v_a_725_ = lean_ctor_get(v_a_721_, 0);
lean_inc(v_a_725_);
lean_dec_ref_known(v_a_721_, 1);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v_a_725_);
v___x_727_ = v___x_723_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_a_725_);
v___x_727_ = v_reuseFailAlloc_728_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
return v___x_727_;
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
lean_del_object(v___x_723_);
v_a_729_ = lean_ctor_get(v_a_721_, 0);
lean_inc(v_a_729_);
lean_dec_ref_known(v_a_721_, 1);
v___x_730_ = lean_unsigned_to_nat(1u);
v___x_731_ = lean_nat_add(v_a_705_, v___x_730_);
lean_dec(v_a_705_);
v_a_705_ = v___x_731_;
v_b_706_ = v_a_729_;
goto _start;
}
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec(v_a_705_);
lean_dec_ref(v_config_704_);
v_a_734_ = lean_ctor_get(v___y_720_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___y_720_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___y_720_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___y_720_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_820_ = _args[0];
lean_object* v___x_821_ = _args[1];
lean_object* v_config_822_ = _args[2];
lean_object* v_a_823_ = _args[3];
lean_object* v_b_824_ = _args[4];
lean_object* v___y_825_ = _args[5];
lean_object* v___y_826_ = _args[6];
lean_object* v___y_827_ = _args[7];
lean_object* v___y_828_ = _args[8];
lean_object* v___y_829_ = _args[9];
lean_object* v___y_830_ = _args[10];
lean_object* v___y_831_ = _args[11];
lean_object* v___y_832_ = _args[12];
lean_object* v___y_833_ = _args[13];
lean_object* v___y_834_ = _args[14];
lean_object* v___y_835_ = _args[15];
lean_object* v___y_836_ = _args[16];
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg(v_upperBound_820_, v___x_821_, v_config_822_, v_a_823_, v_b_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec_ref(v___x_821_);
lean_dec(v_upperBound_820_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0(lean_object* v_config_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v___x_851_; lean_object* v_hypotheses_852_; lean_object* v___x_853_; lean_object* v_newHyps_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_851_ = lean_st_ref_get(v___y_840_);
v_hypotheses_852_ = lean_ctor_get(v___x_851_, 3);
lean_inc_ref(v_hypotheses_852_);
lean_dec(v___x_851_);
v___x_853_ = lean_array_get_size(v_hypotheses_852_);
v_newHyps_854_ = lean_mk_empty_array_with_capacity(v___x_853_);
v___x_855_ = lean_unsigned_to_nat(0u);
v___x_856_ = lean_box(0);
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
lean_ctor_set(v___x_857_, 1, v_newHyps_854_);
v___x_858_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg(v___x_853_, v_hypotheses_852_, v_config_838_, v___x_855_, v___x_857_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec_ref(v_hypotheses_852_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_888_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_888_ == 0)
{
v___x_861_ = v___x_858_;
v_isShared_862_ = v_isSharedCheck_888_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_888_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v_fst_863_; 
v_fst_863_ = lean_ctor_get(v_a_859_, 0);
if (lean_obj_tag(v_fst_863_) == 0)
{
lean_object* v_snd_864_; lean_object* v___x_865_; lean_object* v_caches_866_; lean_object* v_typeAnalysis_867_; lean_object* v_target_868_; uint8_t v_didChange_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_882_; 
v_snd_864_ = lean_ctor_get(v_a_859_, 1);
lean_inc(v_snd_864_);
lean_dec(v_a_859_);
v___x_865_ = lean_st_ref_take(v___y_840_);
v_caches_866_ = lean_ctor_get(v___x_865_, 0);
v_typeAnalysis_867_ = lean_ctor_get(v___x_865_, 1);
v_target_868_ = lean_ctor_get(v___x_865_, 2);
v_didChange_869_ = lean_ctor_get_uint8(v___x_865_, sizeof(void*)*4);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_882_ == 0)
{
lean_object* v_unused_883_; 
v_unused_883_ = lean_ctor_get(v___x_865_, 3);
lean_dec(v_unused_883_);
v___x_871_ = v___x_865_;
v_isShared_872_ = v_isSharedCheck_882_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_target_868_);
lean_inc(v_typeAnalysis_867_);
lean_inc(v_caches_866_);
lean_dec(v___x_865_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_882_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 3, v_snd_864_);
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_caches_866_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_typeAnalysis_867_);
lean_ctor_set(v_reuseFailAlloc_881_, 2, v_target_868_);
lean_ctor_set(v_reuseFailAlloc_881_, 3, v_snd_864_);
lean_ctor_set_uint8(v_reuseFailAlloc_881_, sizeof(void*)*4, v_didChange_869_);
v___x_874_ = v_reuseFailAlloc_881_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
lean_object* v___x_875_; uint8_t v___x_876_; lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_875_ = lean_st_ref_put(v___y_840_, v___x_874_);
v___x_876_ = 0;
v___x_877_ = lean_box(v___x_876_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_877_);
v___x_879_ = v___x_861_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
else
{
lean_object* v_val_884_; lean_object* v___x_886_; 
lean_inc_ref(v_fst_863_);
lean_dec(v_a_859_);
v_val_884_ = lean_ctor_get(v_fst_863_, 0);
lean_inc(v_val_884_);
lean_dec_ref_known(v_fst_863_, 1);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v_val_884_);
v___x_886_ = v___x_861_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_val_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
v_a_889_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_858_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_858_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0___boxed(lean_object* v_config_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0(v_config_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1(lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_config_923_; lean_object* v_maxSteps_924_; uint8_t v___x_925_; lean_object* v_config_926_; lean_object* v___f_927_; lean_object* v___x_928_; lean_object* v_target_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_config_923_ = lean_ctor_get(v___y_911_, 0);
v_maxSteps_924_ = lean_ctor_get(v_config_923_, 1);
v___x_925_ = 1;
lean_inc(v_maxSteps_924_);
v_config_926_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_config_926_, 0, v_maxSteps_924_);
lean_ctor_set_uint8(v_config_926_, sizeof(void*)*1, v___x_925_);
v___f_927_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0___boxed), 13, 1);
lean_closure_set(v___f_927_, 0, v_config_926_);
v___x_928_ = lean_st_ref_get(v___y_912_);
v_target_929_ = lean_ctor_get(v___x_928_, 2);
lean_inc_ref(v_target_929_);
lean_dec(v___x_928_);
v___x_930_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_929_);
lean_dec_ref(v_target_929_);
v___x_931_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg(v___x_930_, v___f_927_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1___boxed(lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1(v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0(lean_object* v_cls_953_, lean_object* v_msg_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(v_cls_953_, v_msg_954_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___boxed(lean_object* v_cls_968_, lean_object* v_msg_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0(v_cls_968_, v_msg_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1(lean_object* v_upperBound_983_, lean_object* v___x_984_, lean_object* v_config_985_, lean_object* v_inst_986_, lean_object* v_R_987_, lean_object* v_a_988_, lean_object* v_b_989_, lean_object* v_c_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg(v_upperBound_983_, v___x_984_, v_config_985_, v_a_988_, v_b_989_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_1004_ = _args[0];
lean_object* v___x_1005_ = _args[1];
lean_object* v_config_1006_ = _args[2];
lean_object* v_inst_1007_ = _args[3];
lean_object* v_R_1008_ = _args[4];
lean_object* v_a_1009_ = _args[5];
lean_object* v_b_1010_ = _args[6];
lean_object* v_c_1011_ = _args[7];
lean_object* v___y_1012_ = _args[8];
lean_object* v___y_1013_ = _args[9];
lean_object* v___y_1014_ = _args[10];
lean_object* v___y_1015_ = _args[11];
lean_object* v___y_1016_ = _args[12];
lean_object* v___y_1017_ = _args[13];
lean_object* v___y_1018_ = _args[14];
lean_object* v___y_1019_ = _args[15];
lean_object* v___y_1020_ = _args[16];
lean_object* v___y_1021_ = _args[17];
lean_object* v___y_1022_ = _args[18];
lean_object* v___y_1023_ = _args[19];
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1(v_upperBound_1004_, v___x_1005_, v_config_1006_, v_inst_1007_, v_R_1008_, v_a_1009_, v_b_1010_, v_c_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec_ref(v___x_1005_);
lean_dec(v_upperBound_1004_);
return v_res_1024_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(builtin);
}
#ifdef __cplusplus
}
#endif

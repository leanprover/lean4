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
uint8_t lean_expr_eqv(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__0_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__1_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__1_value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__2_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__2_value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__3_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__3_value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__4_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5___boxed, .m_arity = 13, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__4_value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__5_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__5_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__0_value)}};
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0(lean_object* v_x_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___closed__1));
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0___boxed(lean_object* v_x_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0(v_x_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v_x_226_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3(lean_object* v___f_238_, lean_object* v_x_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_box(0);
lean_inc_ref(v___y_240_);
v___x_252_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_240_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
if (lean_obj_tag(v_a_253_) == 0)
{
uint8_t v_done_254_; 
v_done_254_ = lean_ctor_get_uint8(v_a_253_, 0);
lean_dec_ref_known(v_a_253_, 0);
if (v_done_254_ == 0)
{
lean_object* v___x_255_; 
lean_dec_ref_known(v___x_252_, 1);
lean_inc(v___y_249_);
lean_inc_ref(v___y_248_);
lean_inc(v___y_247_);
lean_inc_ref(v___y_246_);
lean_inc(v___y_245_);
lean_inc_ref(v___y_244_);
lean_inc(v___y_243_);
lean_inc_ref(v___y_242_);
lean_inc(v___y_241_);
v___x_255_ = lean_apply_12(v___f_238_, v___x_251_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, lean_box(0));
return v___x_255_;
}
else
{
lean_dec_ref(v___y_240_);
lean_dec_ref(v___f_238_);
return v___x_252_;
}
}
else
{
uint8_t v_done_256_; 
lean_dec_ref(v___y_240_);
v_done_256_ = lean_ctor_get_uint8(v_a_253_, sizeof(void*)*1);
if (v_done_256_ == 0)
{
lean_object* v_e_x27_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_275_; 
lean_dec_ref_known(v___x_252_, 1);
v_e_x27_257_ = lean_ctor_get(v_a_253_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v_a_253_);
if (v_isSharedCheck_275_ == 0)
{
v___x_259_ = v_a_253_;
v_isShared_260_ = v_isSharedCheck_275_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_e_x27_257_);
lean_dec(v_a_253_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_275_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; 
lean_inc(v___y_249_);
lean_inc_ref(v___y_248_);
lean_inc(v___y_247_);
lean_inc_ref(v___y_246_);
lean_inc(v___y_245_);
lean_inc_ref(v___y_244_);
lean_inc(v___y_243_);
lean_inc_ref(v___y_242_);
lean_inc(v___y_241_);
lean_inc_ref(v_e_x27_257_);
v___x_261_ = lean_apply_12(v___f_238_, v___x_251_, v_e_x27_257_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, lean_box(0));
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
if (lean_obj_tag(v_a_262_) == 0)
{
lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_273_; 
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; 
v_unused_274_ = lean_ctor_get(v___x_261_, 0);
lean_dec(v_unused_274_);
v___x_264_ = v___x_261_;
v_isShared_265_ = v_isSharedCheck_273_;
goto v_resetjp_263_;
}
else
{
lean_dec(v___x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_273_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
uint8_t v_done_266_; lean_object* v___x_268_; 
v_done_266_ = lean_ctor_get_uint8(v_a_262_, 0);
lean_dec_ref_known(v_a_262_, 0);
if (v_isShared_260_ == 0)
{
v___x_268_ = v___x_259_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_e_x27_257_);
v___x_268_ = v_reuseFailAlloc_272_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_270_; 
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*1, v_done_266_);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 0, v___x_268_);
v___x_270_ = v___x_264_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_262_, 1);
lean_del_object(v___x_259_);
lean_dec_ref(v_e_x27_257_);
return v___x_261_;
}
}
else
{
lean_del_object(v___x_259_);
lean_dec_ref(v_e_x27_257_);
return v___x_261_;
}
}
}
else
{
lean_dec_ref_known(v_a_253_, 1);
lean_dec_ref(v___f_238_);
return v___x_252_;
}
}
}
else
{
lean_dec_ref(v___y_240_);
lean_dec_ref(v___f_238_);
return v___x_252_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3___boxed(lean_object* v___f_276_, lean_object* v_x_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3(v___f_276_, v_x_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1(lean_object* v_x_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v___y_291_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_303_);
if (lean_obj_tag(v_a_303_) == 0)
{
uint8_t v_done_304_; 
v_done_304_ = lean_ctor_get_uint8(v_a_303_, 0);
lean_dec_ref_known(v_a_303_, 0);
if (v_done_304_ == 0)
{
lean_object* v___x_305_; 
lean_dec_ref_known(v___x_302_, 1);
v___x_305_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27(v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
return v___x_305_;
}
else
{
lean_dec_ref(v___y_291_);
return v___x_302_;
}
}
else
{
uint8_t v_done_306_; 
lean_dec_ref(v___y_291_);
v_done_306_ = lean_ctor_get_uint8(v_a_303_, sizeof(void*)*1);
if (v_done_306_ == 0)
{
lean_object* v_e_x27_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_325_; 
lean_dec_ref_known(v___x_302_, 1);
v_e_x27_307_ = lean_ctor_get(v_a_303_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v_a_303_);
if (v_isSharedCheck_325_ == 0)
{
v___x_309_ = v_a_303_;
v_isShared_310_ = v_isSharedCheck_325_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_e_x27_307_);
lean_dec(v_a_303_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_325_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; 
lean_inc_ref(v_e_x27_307_);
v___x_311_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27(v_e_x27_307_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
if (lean_obj_tag(v_a_312_) == 0)
{
lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_323_; 
lean_inc_ref(v_a_312_);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_323_ == 0)
{
lean_object* v_unused_324_; 
v_unused_324_ = lean_ctor_get(v___x_311_, 0);
lean_dec(v_unused_324_);
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_323_;
goto v_resetjp_313_;
}
else
{
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_323_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
uint8_t v_done_316_; lean_object* v___x_318_; 
v_done_316_ = lean_ctor_get_uint8(v_a_312_, 0);
lean_dec_ref_known(v_a_312_, 0);
if (v_isShared_310_ == 0)
{
v___x_318_ = v___x_309_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_e_x27_307_);
v___x_318_ = v_reuseFailAlloc_322_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_320_; 
lean_ctor_set_uint8(v___x_318_, sizeof(void*)*1, v_done_316_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_318_);
v___x_320_ = v___x_314_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
else
{
lean_del_object(v___x_309_);
lean_dec_ref(v_e_x27_307_);
return v___x_311_;
}
}
else
{
lean_del_object(v___x_309_);
lean_dec_ref(v_e_x27_307_);
return v___x_311_;
}
}
}
else
{
lean_dec_ref_known(v_a_303_, 1);
return v___x_302_;
}
}
}
else
{
lean_dec_ref(v___y_291_);
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1___boxed(lean_object* v_x_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1(v_x_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7(uint8_t v___x_339_, lean_object* v___f_340_, lean_object* v_____r_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___x_354_; lean_object* v_caches_355_; lean_object* v_typeAnalysis_356_; lean_object* v_target_357_; lean_object* v_hypotheses_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_368_; 
v___x_354_ = lean_st_ref_take(v___y_343_);
v_caches_355_ = lean_ctor_get(v___x_354_, 0);
v_typeAnalysis_356_ = lean_ctor_get(v___x_354_, 1);
v_target_357_ = lean_ctor_get(v___x_354_, 2);
v_hypotheses_358_ = lean_ctor_get(v___x_354_, 3);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_368_ == 0)
{
v___x_360_ = v___x_354_;
v_isShared_361_ = v_isSharedCheck_368_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_hypotheses_358_);
lean_inc(v_target_357_);
lean_inc(v_typeAnalysis_356_);
lean_inc(v_caches_355_);
lean_dec(v___x_354_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_368_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_362_ = lean_box(0);
if (v_isShared_361_ == 0)
{
v___x_364_ = v___x_360_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_caches_355_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_typeAnalysis_356_);
lean_ctor_set(v_reuseFailAlloc_367_, 2, v_target_357_);
lean_ctor_set(v_reuseFailAlloc_367_, 3, v_hypotheses_358_);
v___x_364_ = v_reuseFailAlloc_367_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_ctor_set_uint8(v___x_364_, sizeof(void*)*4, v___x_339_);
v___x_365_ = lean_st_ref_put(v___y_343_, v___x_364_);
lean_inc(v___y_352_);
lean_inc_ref(v___y_351_);
lean_inc(v___y_350_);
lean_inc_ref(v___y_349_);
lean_inc(v___y_348_);
lean_inc_ref(v___y_347_);
lean_inc(v___y_346_);
lean_inc_ref(v___y_345_);
lean_inc(v___y_344_);
lean_inc(v___y_343_);
lean_inc_ref(v___y_342_);
v___x_366_ = lean_apply_13(v___f_340_, v___x_362_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, lean_box(0));
return v___x_366_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7___boxed(lean_object* v___x_369_, lean_object* v___f_370_, lean_object* v_____r_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
uint8_t v___x_11520__boxed_384_; lean_object* v_res_385_; 
v___x_11520__boxed_384_ = lean_unbox(v___x_369_);
v_res_385_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7(v___x_11520__boxed_384_, v___f_370_, v_____r_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0(lean_object* v_msgData_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___x_392_; lean_object* v_env_393_; uint8_t v___x_394_; lean_object* v_env_395_; lean_object* v___x_396_; lean_object* v_toCold_397_; lean_object* v_mctx_398_; lean_object* v_lctx_399_; lean_object* v_options_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_392_ = lean_st_ref_get(v___y_390_);
v_env_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc_ref(v_env_393_);
lean_dec(v___x_392_);
v___x_394_ = 0;
v_env_395_ = l_Lean_Environment_setRecordingDeps(v_env_393_, v___x_394_);
v___x_396_ = lean_st_ref_get(v___y_388_);
v_toCold_397_ = lean_ctor_get(v___y_389_, 0);
v_mctx_398_ = lean_ctor_get(v___x_396_, 0);
lean_inc_ref(v_mctx_398_);
lean_dec(v___x_396_);
v_lctx_399_ = lean_ctor_get(v___y_387_, 2);
v_options_400_ = lean_ctor_get(v_toCold_397_, 2);
lean_inc_ref(v_options_400_);
lean_inc_ref(v_lctx_399_);
v___x_401_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_401_, 0, v_env_395_);
lean_ctor_set(v___x_401_, 1, v_mctx_398_);
lean_ctor_set(v___x_401_, 2, v_lctx_399_);
lean_ctor_set(v___x_401_, 3, v_options_400_);
v___x_402_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v_msgData_386_);
v___x_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0___boxed(lean_object* v_msgData_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0(v_msgData_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
return v_res_410_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_411_; double v___x_412_; 
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_float_of_nat(v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(lean_object* v_cls_416_, lean_object* v_msg_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_ref_423_; lean_object* v___x_424_; lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_470_; 
v_ref_423_ = lean_ctor_get(v___y_420_, 2);
v___x_424_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0(v_msg_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
v_a_425_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_470_ == 0)
{
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_470_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_470_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; lean_object* v_traceState_430_; lean_object* v_env_431_; lean_object* v_nextMacroScope_432_; lean_object* v_ngen_433_; lean_object* v_auxDeclNGen_434_; lean_object* v_cache_435_; lean_object* v_recordedDeps_436_; lean_object* v_messages_437_; lean_object* v_infoState_438_; lean_object* v_snapshotTasks_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_469_; 
v___x_429_ = lean_st_ref_take(v___y_421_);
v_traceState_430_ = lean_ctor_get(v___x_429_, 4);
v_env_431_ = lean_ctor_get(v___x_429_, 0);
v_nextMacroScope_432_ = lean_ctor_get(v___x_429_, 1);
v_ngen_433_ = lean_ctor_get(v___x_429_, 2);
v_auxDeclNGen_434_ = lean_ctor_get(v___x_429_, 3);
v_cache_435_ = lean_ctor_get(v___x_429_, 5);
v_recordedDeps_436_ = lean_ctor_get(v___x_429_, 6);
v_messages_437_ = lean_ctor_get(v___x_429_, 7);
v_infoState_438_ = lean_ctor_get(v___x_429_, 8);
v_snapshotTasks_439_ = lean_ctor_get(v___x_429_, 9);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_469_ == 0)
{
v___x_441_ = v___x_429_;
v_isShared_442_ = v_isSharedCheck_469_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_snapshotTasks_439_);
lean_inc(v_infoState_438_);
lean_inc(v_messages_437_);
lean_inc(v_recordedDeps_436_);
lean_inc(v_cache_435_);
lean_inc(v_traceState_430_);
lean_inc(v_auxDeclNGen_434_);
lean_inc(v_ngen_433_);
lean_inc(v_nextMacroScope_432_);
lean_inc(v_env_431_);
lean_dec(v___x_429_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_469_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
uint64_t v_tid_443_; lean_object* v_traces_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_468_; 
v_tid_443_ = lean_ctor_get_uint64(v_traceState_430_, sizeof(void*)*1);
v_traces_444_ = lean_ctor_get(v_traceState_430_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v_traceState_430_);
if (v_isSharedCheck_468_ == 0)
{
v___x_446_ = v_traceState_430_;
v_isShared_447_ = v_isSharedCheck_468_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_traces_444_);
lean_dec(v_traceState_430_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_468_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v___x_449_; double v___x_450_; uint8_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_448_ = lean_box(0);
v___x_449_ = lean_box(0);
v___x_450_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0);
v___x_451_ = 0;
v___x_452_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__1));
v___x_453_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_453_, 0, v_cls_416_);
lean_ctor_set(v___x_453_, 1, v___x_449_);
lean_ctor_set(v___x_453_, 2, v___x_452_);
lean_ctor_set_float(v___x_453_, sizeof(void*)*3, v___x_450_);
lean_ctor_set_float(v___x_453_, sizeof(void*)*3 + 8, v___x_450_);
lean_ctor_set_uint8(v___x_453_, sizeof(void*)*3 + 16, v___x_451_);
v___x_454_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__2));
v___x_455_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_455_, 0, v___x_453_);
lean_ctor_set(v___x_455_, 1, v_a_425_);
lean_ctor_set(v___x_455_, 2, v___x_454_);
lean_inc(v_ref_423_);
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v_ref_423_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
v___x_457_ = l_Lean_PersistentArray_push___redArg(v_traces_444_, v___x_456_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_457_);
v___x_459_ = v___x_446_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_457_);
lean_ctor_set_uint64(v_reuseFailAlloc_467_, sizeof(void*)*1, v_tid_443_);
v___x_459_ = v_reuseFailAlloc_467_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_461_; 
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 4, v___x_459_);
v___x_461_ = v___x_441_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_env_431_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_nextMacroScope_432_);
lean_ctor_set(v_reuseFailAlloc_466_, 2, v_ngen_433_);
lean_ctor_set(v_reuseFailAlloc_466_, 3, v_auxDeclNGen_434_);
lean_ctor_set(v_reuseFailAlloc_466_, 4, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_466_, 5, v_cache_435_);
lean_ctor_set(v_reuseFailAlloc_466_, 6, v_recordedDeps_436_);
lean_ctor_set(v_reuseFailAlloc_466_, 7, v_messages_437_);
lean_ctor_set(v_reuseFailAlloc_466_, 8, v_infoState_438_);
lean_ctor_set(v_reuseFailAlloc_466_, 9, v_snapshotTasks_439_);
v___x_461_ = v_reuseFailAlloc_466_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; lean_object* v___x_464_; 
v___x_462_ = lean_st_ref_put(v___y_421_, v___x_461_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_448_);
v___x_464_ = v___x_427_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_448_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___boxed(lean_object* v_cls_471_, lean_object* v_msg_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(v_cls_471_, v_msg_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4(lean_object* v___f_479_, lean_object* v_x_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_box(0);
lean_inc_ref(v___y_481_);
v___x_493_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v___y_481_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
if (lean_obj_tag(v_a_494_) == 0)
{
uint8_t v_done_495_; 
v_done_495_ = lean_ctor_get_uint8(v_a_494_, 0);
lean_dec_ref_known(v_a_494_, 0);
if (v_done_495_ == 0)
{
lean_object* v___x_496_; 
lean_dec_ref_known(v___x_493_, 1);
lean_inc(v___y_490_);
lean_inc_ref(v___y_489_);
lean_inc(v___y_488_);
lean_inc_ref(v___y_487_);
lean_inc(v___y_486_);
lean_inc_ref(v___y_485_);
lean_inc(v___y_484_);
lean_inc_ref(v___y_483_);
lean_inc(v___y_482_);
v___x_496_ = lean_apply_12(v___f_479_, v___x_492_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, lean_box(0));
return v___x_496_;
}
else
{
lean_dec_ref(v___y_481_);
lean_dec_ref(v___f_479_);
return v___x_493_;
}
}
else
{
uint8_t v_done_497_; 
lean_dec_ref(v___y_481_);
v_done_497_ = lean_ctor_get_uint8(v_a_494_, sizeof(void*)*1);
if (v_done_497_ == 0)
{
lean_object* v_e_x27_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_516_; 
lean_dec_ref_known(v___x_493_, 1);
v_e_x27_498_ = lean_ctor_get(v_a_494_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v_a_494_);
if (v_isSharedCheck_516_ == 0)
{
v___x_500_ = v_a_494_;
v_isShared_501_ = v_isSharedCheck_516_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_e_x27_498_);
lean_dec(v_a_494_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_516_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; 
lean_inc(v___y_490_);
lean_inc_ref(v___y_489_);
lean_inc(v___y_488_);
lean_inc_ref(v___y_487_);
lean_inc(v___y_486_);
lean_inc_ref(v___y_485_);
lean_inc(v___y_484_);
lean_inc_ref(v___y_483_);
lean_inc(v___y_482_);
lean_inc_ref(v_e_x27_498_);
v___x_502_ = lean_apply_12(v___f_479_, v___x_492_, v_e_x27_498_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, lean_box(0));
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
if (lean_obj_tag(v_a_503_) == 0)
{
lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_514_; 
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; 
v_unused_515_ = lean_ctor_get(v___x_502_, 0);
lean_dec(v_unused_515_);
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_514_;
goto v_resetjp_504_;
}
else
{
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_514_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
uint8_t v_done_507_; lean_object* v___x_509_; 
v_done_507_ = lean_ctor_get_uint8(v_a_503_, 0);
lean_dec_ref_known(v_a_503_, 0);
if (v_isShared_501_ == 0)
{
v___x_509_ = v___x_500_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_e_x27_498_);
v___x_509_ = v_reuseFailAlloc_513_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_511_; 
lean_ctor_set_uint8(v___x_509_, sizeof(void*)*1, v_done_507_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_509_);
v___x_511_ = v___x_505_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_503_, 1);
lean_del_object(v___x_500_);
lean_dec_ref(v_e_x27_498_);
return v___x_502_;
}
}
else
{
lean_del_object(v___x_500_);
lean_dec_ref(v_e_x27_498_);
return v___x_502_;
}
}
}
else
{
lean_dec_ref_known(v_a_494_, 1);
lean_dec_ref(v___f_479_);
return v___x_493_;
}
}
}
else
{
lean_dec_ref(v___y_481_);
lean_dec_ref(v___f_479_);
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4___boxed(lean_object* v___f_517_, lean_object* v_x_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4(v___f_517_, v_x_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2(lean_object* v___f_531_, lean_object* v_x_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_box(0);
lean_inc_ref(v___y_533_);
v___x_545_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_533_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
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
lean_object* v_snd_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_820_; 
v_snd_744_ = lean_ctor_get(v_b_706_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v_b_706_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; 
v_unused_821_ = lean_ctor_get(v_b_706_, 0);
lean_dec(v_unused_821_);
v___x_746_ = v_b_706_;
v_isShared_747_ = v_isSharedCheck_820_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_snd_744_);
lean_dec(v_b_706_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_820_;
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
lean_object* v_type_757_; lean_object* v___f_758_; uint8_t v___x_787_; 
lean_del_object(v___x_746_);
v_type_757_ = lean_ctor_get(v___x_751_, 1);
lean_inc(v_a_753_);
lean_inc(v_snd_744_);
v___f_758_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6___boxed), 16, 3);
lean_closure_set(v___f_758_, 0, v_snd_744_);
lean_closure_set(v___f_758_, 1, v_a_753_);
lean_closure_set(v___f_758_, 2, v___x_750_);
v___x_787_ = lean_expr_eqv(v_type_757_, v_type_754_);
if (v___x_787_ == 0)
{
lean_inc_ref(v_type_754_);
lean_dec(v_a_753_);
lean_dec(v_snd_744_);
goto v___jp_762_;
}
else
{
if (v___x_756_ == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; 
lean_dec_ref(v___f_758_);
v___x_788_ = lean_box(0);
v___x_789_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6(v_snd_744_, v_a_753_, v___x_750_, v___x_788_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
v___y_720_ = v___x_789_;
goto v___jp_719_;
}
else
{
lean_inc_ref(v_type_754_);
lean_dec(v_a_753_);
lean_dec(v_snd_744_);
goto v___jp_762_;
}
}
v___jp_759_:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_box(0);
v___x_761_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7(v___x_742_, v___f_758_, v___x_760_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
v___y_720_ = v___x_761_;
goto v___jp_719_;
}
v___jp_762_:
{
lean_object* v_toCold_763_; lean_object* v_options_764_; uint8_t v_hasTrace_765_; 
v_toCold_763_ = lean_ctor_get(v___y_716_, 0);
v_options_764_ = lean_ctor_get(v_toCold_763_, 2);
v_hasTrace_765_ = lean_ctor_get_uint8(v_options_764_, sizeof(void*)*1);
if (v_hasTrace_765_ == 0)
{
lean_dec_ref(v_type_754_);
goto v___jp_759_;
}
else
{
lean_object* v_inheritedTraceOptions_766_; lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v_inheritedTraceOptions_766_ = lean_ctor_get(v_toCold_763_, 11);
v___x_767_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__10));
v___x_768_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13);
v___x_769_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_766_, v_options_764_, v___x_768_);
if (v___x_769_ == 0)
{
lean_dec_ref(v_type_754_);
goto v___jp_759_;
}
else
{
lean_object* v_type_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_type_770_ = lean_ctor_get(v___x_751_, 1);
lean_inc_ref(v_type_770_);
v___x_771_ = l_Lean_MessageData_ofExpr(v_type_770_);
v___x_772_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__15);
v___x_773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_771_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = l_Lean_MessageData_ofExpr(v_type_754_);
v___x_775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_773_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v___x_776_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(v___x_767_, v___x_775_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_778_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref_known(v___x_776_, 1);
v___x_778_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7(v___x_742_, v___f_758_, v_a_777_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
v___y_720_ = v___x_778_;
goto v___jp_719_;
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec_ref(v___f_758_);
lean_dec(v_a_705_);
lean_dec_ref(v_config_704_);
v_a_779_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_776_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_776_);
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
}
}
else
{
lean_object* v___x_790_; 
lean_inc_ref(v_value_755_);
lean_dec(v_a_753_);
lean_dec(v_a_705_);
lean_dec_ref(v_config_704_);
v___x_790_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_755_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_802_; 
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v___x_790_, 0);
lean_dec(v_unused_803_);
v___x_792_ = v___x_790_;
v_isShared_793_ = v_isSharedCheck_802_;
goto v_resetjp_791_;
}
else
{
lean_dec(v___x_790_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_802_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_797_; 
v___x_794_ = lean_box(v___x_742_);
v___x_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_795_);
v___x_797_ = v___x_746_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_snd_744_);
v___x_797_ = v_reuseFailAlloc_801_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___x_799_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 0, v___x_797_);
v___x_799_ = v___x_792_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_del_object(v___x_746_);
lean_dec(v_snd_744_);
v_a_804_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_790_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_790_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_del_object(v___x_746_);
lean_dec(v_snd_744_);
lean_dec(v_a_705_);
lean_dec_ref(v_config_704_);
v_a_812_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_752_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_752_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
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
lean_object* v_upperBound_822_ = _args[0];
lean_object* v___x_823_ = _args[1];
lean_object* v_config_824_ = _args[2];
lean_object* v_a_825_ = _args[3];
lean_object* v_b_826_ = _args[4];
lean_object* v___y_827_ = _args[5];
lean_object* v___y_828_ = _args[6];
lean_object* v___y_829_ = _args[7];
lean_object* v___y_830_ = _args[8];
lean_object* v___y_831_ = _args[9];
lean_object* v___y_832_ = _args[10];
lean_object* v___y_833_ = _args[11];
lean_object* v___y_834_ = _args[12];
lean_object* v___y_835_ = _args[13];
lean_object* v___y_836_ = _args[14];
lean_object* v___y_837_ = _args[15];
lean_object* v___y_838_ = _args[16];
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg(v_upperBound_822_, v___x_823_, v_config_824_, v_a_825_, v_b_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec_ref(v___x_823_);
lean_dec(v_upperBound_822_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0(lean_object* v_config_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v___x_853_; lean_object* v_hypotheses_854_; lean_object* v___x_855_; lean_object* v_newHyps_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_853_ = lean_st_ref_get(v___y_842_);
v_hypotheses_854_ = lean_ctor_get(v___x_853_, 3);
lean_inc_ref(v_hypotheses_854_);
lean_dec(v___x_853_);
v___x_855_ = lean_array_get_size(v_hypotheses_854_);
v_newHyps_856_ = lean_mk_empty_array_with_capacity(v___x_855_);
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_box(0);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v_newHyps_856_);
v___x_860_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg(v___x_855_, v_hypotheses_854_, v_config_840_, v___x_857_, v___x_859_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec_ref(v_hypotheses_854_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_890_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_890_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_890_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_890_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v_fst_865_; 
v_fst_865_ = lean_ctor_get(v_a_861_, 0);
if (lean_obj_tag(v_fst_865_) == 0)
{
lean_object* v_snd_866_; lean_object* v___x_867_; lean_object* v_caches_868_; lean_object* v_typeAnalysis_869_; lean_object* v_target_870_; uint8_t v_didChange_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_884_; 
v_snd_866_ = lean_ctor_get(v_a_861_, 1);
lean_inc(v_snd_866_);
lean_dec(v_a_861_);
v___x_867_ = lean_st_ref_take(v___y_842_);
v_caches_868_ = lean_ctor_get(v___x_867_, 0);
v_typeAnalysis_869_ = lean_ctor_get(v___x_867_, 1);
v_target_870_ = lean_ctor_get(v___x_867_, 2);
v_didChange_871_ = lean_ctor_get_uint8(v___x_867_, sizeof(void*)*4);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; 
v_unused_885_ = lean_ctor_get(v___x_867_, 3);
lean_dec(v_unused_885_);
v___x_873_ = v___x_867_;
v_isShared_874_ = v_isSharedCheck_884_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_target_870_);
lean_inc(v_typeAnalysis_869_);
lean_inc(v_caches_868_);
lean_dec(v___x_867_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_884_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 3, v_snd_866_);
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_caches_868_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v_typeAnalysis_869_);
lean_ctor_set(v_reuseFailAlloc_883_, 2, v_target_870_);
lean_ctor_set(v_reuseFailAlloc_883_, 3, v_snd_866_);
lean_ctor_set_uint8(v_reuseFailAlloc_883_, sizeof(void*)*4, v_didChange_871_);
v___x_876_ = v_reuseFailAlloc_883_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; uint8_t v___x_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_877_ = lean_st_ref_put(v___y_842_, v___x_876_);
v___x_878_ = 0;
v___x_879_ = lean_box(v___x_878_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v___x_879_);
v___x_881_ = v___x_863_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_879_);
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
lean_object* v_val_886_; lean_object* v___x_888_; 
lean_inc_ref(v_fst_865_);
lean_dec(v_a_861_);
v_val_886_ = lean_ctor_get(v_fst_865_, 0);
lean_inc(v_val_886_);
lean_dec_ref_known(v_fst_865_, 1);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v_val_886_);
v___x_888_ = v___x_863_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_val_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
v_a_891_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_860_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_860_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0___boxed(lean_object* v_config_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0(v_config_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1(lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_config_925_; lean_object* v_maxSteps_926_; uint8_t v___x_927_; lean_object* v_config_928_; lean_object* v___f_929_; lean_object* v___x_930_; lean_object* v_target_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v_config_925_ = lean_ctor_get(v___y_913_, 0);
v_maxSteps_926_ = lean_ctor_get(v_config_925_, 1);
v___x_927_ = 1;
lean_inc(v_maxSteps_926_);
v_config_928_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_config_928_, 0, v_maxSteps_926_);
lean_ctor_set_uint8(v_config_928_, sizeof(void*)*1, v___x_927_);
v___f_929_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0___boxed), 13, 1);
lean_closure_set(v___f_929_, 0, v_config_928_);
v___x_930_ = lean_st_ref_get(v___y_914_);
v_target_931_ = lean_ctor_get(v___x_930_, 2);
lean_inc_ref(v_target_931_);
lean_dec(v___x_930_);
v___x_932_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_931_);
lean_dec_ref(v_target_931_);
v___x_933_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg(v___x_932_, v___f_929_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1___boxed(lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1(v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0(lean_object* v_cls_955_, lean_object* v_msg_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(v_cls_955_, v_msg_956_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___boxed(lean_object* v_cls_970_, lean_object* v_msg_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0(v_cls_970_, v_msg_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1(lean_object* v_upperBound_985_, lean_object* v___x_986_, lean_object* v_config_987_, lean_object* v_inst_988_, lean_object* v_R_989_, lean_object* v_a_990_, lean_object* v_b_991_, lean_object* v_c_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg(v_upperBound_985_, v___x_986_, v_config_987_, v_a_990_, v_b_991_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_1006_ = _args[0];
lean_object* v___x_1007_ = _args[1];
lean_object* v_config_1008_ = _args[2];
lean_object* v_inst_1009_ = _args[3];
lean_object* v_R_1010_ = _args[4];
lean_object* v_a_1011_ = _args[5];
lean_object* v_b_1012_ = _args[6];
lean_object* v_c_1013_ = _args[7];
lean_object* v___y_1014_ = _args[8];
lean_object* v___y_1015_ = _args[9];
lean_object* v___y_1016_ = _args[10];
lean_object* v___y_1017_ = _args[11];
lean_object* v___y_1018_ = _args[12];
lean_object* v___y_1019_ = _args[13];
lean_object* v___y_1020_ = _args[14];
lean_object* v___y_1021_ = _args[15];
lean_object* v___y_1022_ = _args[16];
lean_object* v___y_1023_ = _args[17];
lean_object* v___y_1024_ = _args[18];
lean_object* v___y_1025_ = _args[19];
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1(v_upperBound_1006_, v___x_1007_, v_config_1008_, v_inst_1009_, v_R_1010_, v_a_1011_, v_b_1012_, v_c_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec_ref(v___x_1007_);
lean_dec(v_upperBound_1006_);
return v_res_1026_;
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

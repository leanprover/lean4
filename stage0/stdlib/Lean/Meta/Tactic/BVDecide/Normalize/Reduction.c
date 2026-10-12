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
lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0___redArg(lean_object* v_declName_1_, lean_object* v___y_2_){
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
LEAN_EXPORT void l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_8_;
v_res_8_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0___redArg(v_declName_1_, v___y_2_);
stack->m_obj
 = v_res_8_;
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0___redArg___boxed(lean_object* v_declName_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0___redArg(v_declName_9_, v___y_10_);
lean_dec(v___y_10_);
return v_res_12_;
}
}
lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0(lean_object* v_declName_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0___redArg(v_declName_13_, v___y_22_);
return v___x_24_;
}
}
LEAN_EXPORT void l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_13_ = stack[0].m_obj;
lean_object* v___y_14_ = stack[1].m_obj;
lean_object* v___y_15_ = stack[2].m_obj;
lean_object* v___y_16_ = stack[3].m_obj;
lean_object* v___y_17_ = stack[4].m_obj;
lean_object* v___y_18_ = stack[5].m_obj;
lean_object* v___y_19_ = stack[6].m_obj;
lean_object* v___y_20_ = stack[7].m_obj;
lean_object* v___y_21_ = stack[8].m_obj;
lean_object* v___y_22_ = stack[9].m_obj;
lean_object* v_res_25_;
v_res_25_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0(v_declName_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_);
stack->m_obj
 = v_res_25_;
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0___boxed(lean_object* v_declName_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0(v_declName_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___closed__0(void){
_start:
{
lean_object* v___x_38_; lean_object* v_dummy_39_; 
v___x_38_ = lean_box(0);
v_dummy_39_ = l_Lean_Expr_sort___override(v___x_38_);
return v_dummy_39_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27(lean_object* v_e_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_f_53_; 
v_f_53_ = l_Lean_Expr_getAppFn(v_e_42_);
if (lean_obj_tag(v_f_53_) == 4)
{
lean_object* v_declName_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v_a_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_101_; 
v_declName_54_ = lean_ctor_get(v_f_53_, 0);
lean_inc(v_declName_54_);
lean_dec_ref_known(v_f_53_, 2);
v___x_55_ = l_Lean_instInhabitedExpr;
v___x_56_ = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_spec__0___redArg(v_declName_54_, v_a_51_);
v_a_57_ = lean_ctor_get(v___x_56_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_101_ == 0)
{
v___x_59_ = v___x_56_;
v_isShared_60_ = v_isSharedCheck_101_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_a_57_);
lean_dec(v___x_56_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_101_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
if (lean_obj_tag(v_a_57_) == 1)
{
lean_object* v_val_61_; lean_object* v_numParams_62_; lean_object* v_nargs_63_; lean_object* v_dummy_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v_val_61_ = lean_ctor_get(v_a_57_, 0);
lean_inc(v_val_61_);
lean_dec_ref_known(v_a_57_, 1);
v_numParams_62_ = lean_ctor_get(v_val_61_, 1);
lean_inc(v_numParams_62_);
lean_dec(v_val_61_);
v_nargs_63_ = l_Lean_Expr_getAppNumArgs(v_e_42_);
v_dummy_64_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___closed__0);
lean_inc(v_nargs_63_);
v___x_65_ = lean_mk_array(v_nargs_63_, v_dummy_64_);
v___x_66_ = lean_unsigned_to_nat(1u);
v___x_67_ = lean_nat_sub(v_nargs_63_, v___x_66_);
lean_dec(v_nargs_63_);
lean_inc_ref(v_e_42_);
v___x_68_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_42_, v___x_65_, v___x_67_);
v___x_69_ = lean_array_get_size(v___x_68_);
v___x_70_ = lean_nat_dec_lt(v_numParams_62_, v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; lean_object* v___x_73_; 
lean_dec_ref(v___x_68_);
lean_dec(v_numParams_62_);
lean_dec_ref(v_e_42_);
v___x_71_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_71_, 0, v___x_70_);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 0, v___x_71_);
v___x_73_ = v___x_59_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_del_object(v___x_59_);
v___x_75_ = lean_array_get(v___x_55_, v___x_68_, v_numParams_62_);
lean_dec(v_numParams_62_);
lean_dec_ref(v___x_68_);
v___x_76_ = l_Lean_Meta_isConstructorApp(v___x_75_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_88_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_88_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_88_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_88_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
uint8_t v___x_81_; 
v___x_81_ = lean_unbox(v_a_77_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; uint8_t v___x_83_; lean_object* v___x_85_; 
lean_dec_ref(v_e_42_);
v___x_82_ = lean_alloc_ctor(0, 0, 1);
v___x_83_ = lean_unbox(v_a_77_);
lean_dec(v_a_77_);
lean_ctor_set_uint8(v___x_82_, 0, v___x_83_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_82_);
v___x_85_ = v___x_79_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_82_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
else
{
lean_object* v___x_87_; 
lean_del_object(v___x_79_);
lean_dec(v_a_77_);
v___x_87_ = l_Lean_Meta_Sym_DSimp_dsimpProj___redArg(v_e_42_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
return v___x_87_;
}
}
}
else
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
lean_dec_ref(v_e_42_);
v_a_89_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_96_ == 0)
{
v___x_91_ = v___x_76_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_76_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_89_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
}
else
{
lean_object* v___x_97_; lean_object* v___x_99_; 
lean_dec(v_a_57_);
lean_dec_ref(v_e_42_);
v___x_97_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___closed__1));
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 0, v___x_97_);
v___x_99_ = v___x_59_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_97_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; 
lean_dec_ref(v_f_53_);
lean_dec_ref(v_e_42_);
v___x_102_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___closed__1));
v___x_103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
return v___x_103_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_42_ = stack[0].m_obj;
lean_object* v_a_43_ = stack[1].m_obj;
lean_object* v_a_44_ = stack[2].m_obj;
lean_object* v_a_45_ = stack[3].m_obj;
lean_object* v_a_46_ = stack[4].m_obj;
lean_object* v_a_47_ = stack[5].m_obj;
lean_object* v_a_48_ = stack[6].m_obj;
lean_object* v_a_49_ = stack[7].m_obj;
lean_object* v_a_50_ = stack[8].m_obj;
lean_object* v_a_51_ = stack[9].m_obj;
lean_object* v_res_104_;
v_res_104_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27(v_e_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
stack->m_obj
 = v_res_104_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___boxed(lean_object* v_e_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27(v_e_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec(v_a_108_);
lean_dec_ref(v_a_107_);
lean_dec(v_a_106_);
return v_res_116_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___lam__0(lean_object* v_x_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___x_130_; 
lean_inc(v___y_124_);
lean_inc_ref(v___y_123_);
lean_inc(v___y_122_);
lean_inc_ref(v___y_121_);
lean_inc(v___y_120_);
lean_inc(v___y_119_);
lean_inc_ref(v___y_118_);
v___x_130_ = lean_apply_12(v_x_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, lean_box(0));
return v___x_130_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_117_ = stack[0].m_obj;
lean_object* v___y_118_ = stack[1].m_obj;
lean_object* v___y_119_ = stack[2].m_obj;
lean_object* v___y_120_ = stack[3].m_obj;
lean_object* v___y_121_ = stack[4].m_obj;
lean_object* v___y_122_ = stack[5].m_obj;
lean_object* v___y_123_ = stack[6].m_obj;
lean_object* v___y_124_ = stack[7].m_obj;
lean_object* v___y_125_ = stack[8].m_obj;
lean_object* v___y_126_ = stack[9].m_obj;
lean_object* v___y_127_ = stack[10].m_obj;
lean_object* v___y_128_ = stack[11].m_obj;
lean_object* v_res_131_;
v_res_131_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___lam__0(v_x_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
stack->m_obj
 = v_res_131_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___lam__0___boxed(lean_object* v_x_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___lam__0(v_x_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
return v_res_145_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg(lean_object* v_mvarId_146_, lean_object* v_x_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v___f_160_; lean_object* v___x_161_; 
lean_inc(v___y_154_);
lean_inc_ref(v___y_153_);
lean_inc(v___y_152_);
lean_inc_ref(v___y_151_);
lean_inc(v___y_150_);
lean_inc(v___y_149_);
lean_inc_ref(v___y_148_);
v___f_160_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_160_, 0, v_x_147_);
lean_closure_set(v___f_160_, 1, v___y_148_);
lean_closure_set(v___f_160_, 2, v___y_149_);
lean_closure_set(v___f_160_, 3, v___y_150_);
lean_closure_set(v___f_160_, 4, v___y_151_);
lean_closure_set(v___f_160_, 5, v___y_152_);
lean_closure_set(v___f_160_, 6, v___y_153_);
lean_closure_set(v___f_160_, 7, v___y_154_);
v___x_161_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_146_, v___f_160_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
if (lean_obj_tag(v___x_161_) == 0)
{
return v___x_161_;
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_146_ = stack[0].m_obj;
lean_object* v_x_147_ = stack[1].m_obj;
lean_object* v___y_148_ = stack[2].m_obj;
lean_object* v___y_149_ = stack[3].m_obj;
lean_object* v___y_150_ = stack[4].m_obj;
lean_object* v___y_151_ = stack[5].m_obj;
lean_object* v___y_152_ = stack[6].m_obj;
lean_object* v___y_153_ = stack[7].m_obj;
lean_object* v___y_154_ = stack[8].m_obj;
lean_object* v___y_155_ = stack[9].m_obj;
lean_object* v___y_156_ = stack[10].m_obj;
lean_object* v___y_157_ = stack[11].m_obj;
lean_object* v___y_158_ = stack[12].m_obj;
lean_object* v_res_170_;
v_res_170_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg(v_mvarId_146_, v_x_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
stack->m_obj
 = v_res_170_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg___boxed(lean_object* v_mvarId_171_, lean_object* v_x_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg(v_mvarId_171_, v_x_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_);
lean_dec(v___y_183_);
lean_dec_ref(v___y_182_);
lean_dec(v___y_181_);
lean_dec_ref(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
return v_res_185_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2(lean_object* v_00_u03b1_186_, lean_object* v_mvarId_187_, lean_object* v_x_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg(v_mvarId_187_, v_x_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
return v___x_201_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_187_ = stack[1].m_obj;
lean_object* v_x_188_ = stack[2].m_obj;
lean_object* v___y_189_ = stack[3].m_obj;
lean_object* v___y_190_ = stack[4].m_obj;
lean_object* v___y_191_ = stack[5].m_obj;
lean_object* v___y_192_ = stack[6].m_obj;
lean_object* v___y_193_ = stack[7].m_obj;
lean_object* v___y_194_ = stack[8].m_obj;
lean_object* v___y_195_ = stack[9].m_obj;
lean_object* v___y_196_ = stack[10].m_obj;
lean_object* v___y_197_ = stack[11].m_obj;
lean_object* v___y_198_ = stack[12].m_obj;
lean_object* v___y_199_ = stack[13].m_obj;
lean_object* v_res_202_;
v_res_202_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2(lean_box(0), v_mvarId_187_, v_x_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
stack->m_obj
 = v_res_202_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___boxed(lean_object* v_00_u03b1_203_, lean_object* v_mvarId_204_, lean_object* v_x_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2(v_00_u03b1_203_, v_mvarId_204_, v_x_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
return v_res_218_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0(lean_object* v_x_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27___closed__1));
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_219_ = stack[0].m_obj;
lean_object* v___y_220_ = stack[1].m_obj;
lean_object* v___y_221_ = stack[2].m_obj;
lean_object* v___y_222_ = stack[3].m_obj;
lean_object* v___y_223_ = stack[4].m_obj;
lean_object* v___y_224_ = stack[5].m_obj;
lean_object* v___y_225_ = stack[6].m_obj;
lean_object* v___y_226_ = stack[7].m_obj;
lean_object* v___y_227_ = stack[8].m_obj;
lean_object* v___y_228_ = stack[9].m_obj;
lean_object* v_res_232_;
v_res_232_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0(v_x_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0___boxed(lean_object* v_x_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__0(v_x_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v_x_233_);
return v_res_244_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3(lean_object* v___f_245_, lean_object* v_x_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_box(0);
lean_inc_ref(v___y_247_);
v___x_259_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_247_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; 
v_a_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_a_260_);
if (lean_obj_tag(v_a_260_) == 0)
{
uint8_t v_done_261_; 
v_done_261_ = lean_ctor_get_uint8(v_a_260_, 0);
lean_dec_ref_known(v_a_260_, 0);
if (v_done_261_ == 0)
{
lean_object* v___x_262_; 
lean_dec_ref_known(v___x_259_, 1);
lean_inc(v___y_256_);
lean_inc_ref(v___y_255_);
lean_inc(v___y_254_);
lean_inc_ref(v___y_253_);
lean_inc(v___y_252_);
lean_inc_ref(v___y_251_);
lean_inc(v___y_250_);
lean_inc_ref(v___y_249_);
lean_inc(v___y_248_);
v___x_262_ = lean_apply_12(v___f_245_, v___x_258_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, lean_box(0));
return v___x_262_;
}
else
{
lean_dec_ref(v___y_247_);
lean_dec_ref(v___f_245_);
return v___x_259_;
}
}
else
{
uint8_t v_done_263_; 
lean_dec_ref(v___y_247_);
v_done_263_ = lean_ctor_get_uint8(v_a_260_, sizeof(void*)*1);
if (v_done_263_ == 0)
{
lean_object* v_e_x27_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_282_; 
lean_dec_ref_known(v___x_259_, 1);
v_e_x27_264_ = lean_ctor_get(v_a_260_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v_a_260_);
if (v_isSharedCheck_282_ == 0)
{
v___x_266_ = v_a_260_;
v_isShared_267_ = v_isSharedCheck_282_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_e_x27_264_);
lean_dec(v_a_260_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_282_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; 
lean_inc(v___y_256_);
lean_inc_ref(v___y_255_);
lean_inc(v___y_254_);
lean_inc_ref(v___y_253_);
lean_inc(v___y_252_);
lean_inc_ref(v___y_251_);
lean_inc(v___y_250_);
lean_inc_ref(v___y_249_);
lean_inc(v___y_248_);
lean_inc_ref(v_e_x27_264_);
v___x_268_ = lean_apply_12(v___f_245_, v___x_258_, v_e_x27_264_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, lean_box(0));
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_a_269_);
if (lean_obj_tag(v_a_269_) == 0)
{
lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_280_; 
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; 
v_unused_281_ = lean_ctor_get(v___x_268_, 0);
lean_dec(v_unused_281_);
v___x_271_ = v___x_268_;
v_isShared_272_ = v_isSharedCheck_280_;
goto v_resetjp_270_;
}
else
{
lean_dec(v___x_268_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_280_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
uint8_t v_done_273_; lean_object* v___x_275_; 
v_done_273_ = lean_ctor_get_uint8(v_a_269_, 0);
lean_dec_ref_known(v_a_269_, 0);
if (v_isShared_267_ == 0)
{
v___x_275_ = v___x_266_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_e_x27_264_);
v___x_275_ = v_reuseFailAlloc_279_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_277_; 
lean_ctor_set_uint8(v___x_275_, sizeof(void*)*1, v_done_273_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v___x_275_);
v___x_277_ = v___x_271_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_269_, 1);
lean_del_object(v___x_266_);
lean_dec_ref(v_e_x27_264_);
return v___x_268_;
}
}
else
{
lean_del_object(v___x_266_);
lean_dec_ref(v_e_x27_264_);
return v___x_268_;
}
}
}
else
{
lean_dec_ref_known(v_a_260_, 1);
lean_dec_ref(v___f_245_);
return v___x_259_;
}
}
}
else
{
lean_dec_ref(v___y_247_);
lean_dec_ref(v___f_245_);
return v___x_259_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_245_ = stack[0].m_obj;
lean_object* v_x_246_ = stack[1].m_obj;
lean_object* v___y_247_ = stack[2].m_obj;
lean_object* v___y_248_ = stack[3].m_obj;
lean_object* v___y_249_ = stack[4].m_obj;
lean_object* v___y_250_ = stack[5].m_obj;
lean_object* v___y_251_ = stack[6].m_obj;
lean_object* v___y_252_ = stack[7].m_obj;
lean_object* v___y_253_ = stack[8].m_obj;
lean_object* v___y_254_ = stack[9].m_obj;
lean_object* v___y_255_ = stack[10].m_obj;
lean_object* v___y_256_ = stack[11].m_obj;
lean_object* v_res_283_;
v_res_283_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3(v___f_245_, v_x_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_);
stack->m_obj
 = v_res_283_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3___boxed(lean_object* v___f_284_, lean_object* v_x_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__3(v___f_284_, v_x_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
return v_res_297_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1(lean_object* v_x_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(v___y_299_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
lean_inc(v_a_311_);
if (lean_obj_tag(v_a_311_) == 0)
{
uint8_t v_done_312_; 
v_done_312_ = lean_ctor_get_uint8(v_a_311_, 0);
lean_dec_ref_known(v_a_311_, 0);
if (v_done_312_ == 0)
{
lean_object* v___x_313_; 
lean_dec_ref_known(v___x_310_, 1);
v___x_313_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27(v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
return v___x_313_;
}
else
{
lean_dec_ref(v___y_299_);
return v___x_310_;
}
}
else
{
uint8_t v_done_314_; 
lean_dec_ref(v___y_299_);
v_done_314_ = lean_ctor_get_uint8(v_a_311_, sizeof(void*)*1);
if (v_done_314_ == 0)
{
lean_object* v_e_x27_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_333_; 
lean_dec_ref_known(v___x_310_, 1);
v_e_x27_315_ = lean_ctor_get(v_a_311_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v_a_311_);
if (v_isSharedCheck_333_ == 0)
{
v___x_317_ = v_a_311_;
v_isShared_318_ = v_isSharedCheck_333_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_e_x27_315_);
lean_dec(v_a_311_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_333_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; 
lean_inc_ref(v_e_x27_315_);
v___x_319_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Reduction_0__Lean_Meta_Tactic_BVDecide_Normalize_dsimpProj_x27(v_e_x27_315_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
if (lean_obj_tag(v_a_320_) == 0)
{
lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_331_; 
lean_inc_ref(v_a_320_);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; 
v_unused_332_ = lean_ctor_get(v___x_319_, 0);
lean_dec(v_unused_332_);
v___x_322_ = v___x_319_;
v_isShared_323_ = v_isSharedCheck_331_;
goto v_resetjp_321_;
}
else
{
lean_dec(v___x_319_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_331_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
uint8_t v_done_324_; lean_object* v___x_326_; 
v_done_324_ = lean_ctor_get_uint8(v_a_320_, 0);
lean_dec_ref_known(v_a_320_, 0);
if (v_isShared_318_ == 0)
{
v___x_326_ = v___x_317_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_e_x27_315_);
v___x_326_ = v_reuseFailAlloc_330_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_328_; 
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*1, v_done_324_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_326_);
v___x_328_ = v___x_322_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
else
{
lean_del_object(v___x_317_);
lean_dec_ref(v_e_x27_315_);
return v___x_319_;
}
}
else
{
lean_del_object(v___x_317_);
lean_dec_ref(v_e_x27_315_);
return v___x_319_;
}
}
}
else
{
lean_dec_ref_known(v_a_311_, 1);
return v___x_310_;
}
}
}
else
{
lean_dec_ref(v___y_299_);
return v___x_310_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_298_ = stack[0].m_obj;
lean_object* v___y_299_ = stack[1].m_obj;
lean_object* v___y_300_ = stack[2].m_obj;
lean_object* v___y_301_ = stack[3].m_obj;
lean_object* v___y_302_ = stack[4].m_obj;
lean_object* v___y_303_ = stack[5].m_obj;
lean_object* v___y_304_ = stack[6].m_obj;
lean_object* v___y_305_ = stack[7].m_obj;
lean_object* v___y_306_ = stack[8].m_obj;
lean_object* v___y_307_ = stack[9].m_obj;
lean_object* v___y_308_ = stack[10].m_obj;
lean_object* v_res_334_;
v_res_334_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1(v_x_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
stack->m_obj
 = v_res_334_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1___boxed(lean_object* v_x_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__1(v_x_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
return v_res_347_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7(uint8_t v___x_348_, lean_object* v___f_349_, lean_object* v_____r_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; lean_object* v_caches_364_; lean_object* v_typeAnalysis_365_; lean_object* v_target_366_; lean_object* v_hypotheses_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_377_; 
v___x_363_ = lean_st_ref_take(v___y_352_);
v_caches_364_ = lean_ctor_get(v___x_363_, 0);
v_typeAnalysis_365_ = lean_ctor_get(v___x_363_, 1);
v_target_366_ = lean_ctor_get(v___x_363_, 2);
v_hypotheses_367_ = lean_ctor_get(v___x_363_, 3);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_377_ == 0)
{
v___x_369_ = v___x_363_;
v_isShared_370_ = v_isSharedCheck_377_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_hypotheses_367_);
lean_inc(v_target_366_);
lean_inc(v_typeAnalysis_365_);
lean_inc(v_caches_364_);
lean_dec(v___x_363_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_377_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_371_ = lean_box(0);
if (v_isShared_370_ == 0)
{
v___x_373_ = v___x_369_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_caches_364_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_typeAnalysis_365_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_target_366_);
lean_ctor_set(v_reuseFailAlloc_376_, 3, v_hypotheses_367_);
v___x_373_ = v_reuseFailAlloc_376_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
lean_ctor_set_uint8(v___x_373_, sizeof(void*)*4, v___x_348_);
v___x_374_ = lean_st_ref_put(v___y_352_, v___x_373_);
lean_inc(v___y_361_);
lean_inc_ref(v___y_360_);
lean_inc(v___y_359_);
lean_inc_ref(v___y_358_);
lean_inc(v___y_357_);
lean_inc_ref(v___y_356_);
lean_inc(v___y_355_);
lean_inc_ref(v___y_354_);
lean_inc(v___y_353_);
lean_inc(v___y_352_);
lean_inc_ref(v___y_351_);
v___x_375_ = lean_apply_13(v___f_349_, v___x_371_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, lean_box(0));
return v___x_375_;
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_348_ = stack[0].m_num;
lean_object* v___f_349_ = stack[1].m_obj;
lean_object* v_____r_350_ = stack[2].m_obj;
lean_object* v___y_351_ = stack[3].m_obj;
lean_object* v___y_352_ = stack[4].m_obj;
lean_object* v___y_353_ = stack[5].m_obj;
lean_object* v___y_354_ = stack[6].m_obj;
lean_object* v___y_355_ = stack[7].m_obj;
lean_object* v___y_356_ = stack[8].m_obj;
lean_object* v___y_357_ = stack[9].m_obj;
lean_object* v___y_358_ = stack[10].m_obj;
lean_object* v___y_359_ = stack[11].m_obj;
lean_object* v___y_360_ = stack[12].m_obj;
lean_object* v___y_361_ = stack[13].m_obj;
lean_object* v_res_378_;
v_res_378_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7(v___x_348_, v___f_349_, v_____r_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
stack->m_obj
 = v_res_378_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7___boxed(lean_object* v___x_379_, lean_object* v___f_380_, lean_object* v_____r_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
uint8_t v___x_11727__boxed_394_; lean_object* v_res_395_; 
v___x_11727__boxed_394_ = lean_unbox(v___x_379_);
v_res_395_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7(v___x_11727__boxed_394_, v___f_380_, v_____r_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
return v_res_395_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0(lean_object* v_msgData_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; lean_object* v_env_403_; uint8_t v___x_404_; lean_object* v_env_405_; lean_object* v___x_406_; lean_object* v_toCold_407_; lean_object* v_mctx_408_; lean_object* v_lctx_409_; lean_object* v_options_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_402_ = lean_st_ref_get(v___y_400_);
v_env_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc_ref(v_env_403_);
lean_dec(v___x_402_);
v___x_404_ = 0;
v_env_405_ = l_Lean_Environment_setRecordingDeps(v_env_403_, v___x_404_);
v___x_406_ = lean_st_ref_get(v___y_398_);
v_toCold_407_ = lean_ctor_get(v___y_399_, 0);
v_mctx_408_ = lean_ctor_get(v___x_406_, 0);
lean_inc_ref(v_mctx_408_);
lean_dec(v___x_406_);
v_lctx_409_ = lean_ctor_get(v___y_397_, 2);
v_options_410_ = lean_ctor_get(v_toCold_407_, 2);
lean_inc_ref(v_options_410_);
lean_inc_ref(v_lctx_409_);
v___x_411_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_411_, 0, v_env_405_);
lean_ctor_set(v___x_411_, 1, v_mctx_408_);
lean_ctor_set(v___x_411_, 2, v_lctx_409_);
lean_ctor_set(v___x_411_, 3, v_options_410_);
v___x_412_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_411_);
lean_ctor_set(v___x_412_, 1, v_msgData_396_);
v___x_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_396_ = stack[0].m_obj;
lean_object* v___y_397_ = stack[1].m_obj;
lean_object* v___y_398_ = stack[2].m_obj;
lean_object* v___y_399_ = stack[3].m_obj;
lean_object* v___y_400_ = stack[4].m_obj;
lean_object* v_res_414_;
v_res_414_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0(v_msgData_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
stack->m_obj
 = v_res_414_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0___boxed(lean_object* v_msgData_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0(v_msgData_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
return v_res_421_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_422_; double v___x_423_; 
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = lean_float_of_nat(v___x_422_);
return v___x_423_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(lean_object* v_cls_427_, lean_object* v_msg_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_ref_434_; lean_object* v___x_435_; lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_481_; 
v_ref_434_ = lean_ctor_get(v___y_431_, 2);
v___x_435_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0(v_msg_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
v_a_436_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_481_ == 0)
{
v___x_438_ = v___x_435_;
v_isShared_439_ = v_isSharedCheck_481_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_481_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v_traceState_441_; lean_object* v_env_442_; lean_object* v_nextMacroScope_443_; lean_object* v_ngen_444_; lean_object* v_auxDeclNGen_445_; lean_object* v_cache_446_; lean_object* v_recordedDeps_447_; lean_object* v_messages_448_; lean_object* v_infoState_449_; lean_object* v_snapshotTasks_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_480_; 
v___x_440_ = lean_st_ref_take(v___y_432_);
v_traceState_441_ = lean_ctor_get(v___x_440_, 4);
v_env_442_ = lean_ctor_get(v___x_440_, 0);
v_nextMacroScope_443_ = lean_ctor_get(v___x_440_, 1);
v_ngen_444_ = lean_ctor_get(v___x_440_, 2);
v_auxDeclNGen_445_ = lean_ctor_get(v___x_440_, 3);
v_cache_446_ = lean_ctor_get(v___x_440_, 5);
v_recordedDeps_447_ = lean_ctor_get(v___x_440_, 6);
v_messages_448_ = lean_ctor_get(v___x_440_, 7);
v_infoState_449_ = lean_ctor_get(v___x_440_, 8);
v_snapshotTasks_450_ = lean_ctor_get(v___x_440_, 9);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_440_);
if (v_isSharedCheck_480_ == 0)
{
v___x_452_ = v___x_440_;
v_isShared_453_ = v_isSharedCheck_480_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_snapshotTasks_450_);
lean_inc(v_infoState_449_);
lean_inc(v_messages_448_);
lean_inc(v_recordedDeps_447_);
lean_inc(v_cache_446_);
lean_inc(v_traceState_441_);
lean_inc(v_auxDeclNGen_445_);
lean_inc(v_ngen_444_);
lean_inc(v_nextMacroScope_443_);
lean_inc(v_env_442_);
lean_dec(v___x_440_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_480_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
uint64_t v_tid_454_; lean_object* v_traces_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_479_; 
v_tid_454_ = lean_ctor_get_uint64(v_traceState_441_, sizeof(void*)*1);
v_traces_455_ = lean_ctor_get(v_traceState_441_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v_traceState_441_);
if (v_isSharedCheck_479_ == 0)
{
v___x_457_ = v_traceState_441_;
v_isShared_458_ = v_isSharedCheck_479_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_traces_455_);
lean_dec(v_traceState_441_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_479_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_460_; double v___x_461_; uint8_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_459_ = lean_box(0);
v___x_460_ = lean_box(0);
v___x_461_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0);
v___x_462_ = 0;
v___x_463_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__1));
v___x_464_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_464_, 0, v_cls_427_);
lean_ctor_set(v___x_464_, 1, v___x_460_);
lean_ctor_set(v___x_464_, 2, v___x_463_);
lean_ctor_set_float(v___x_464_, sizeof(void*)*3, v___x_461_);
lean_ctor_set_float(v___x_464_, sizeof(void*)*3 + 8, v___x_461_);
lean_ctor_set_uint8(v___x_464_, sizeof(void*)*3 + 16, v___x_462_);
v___x_465_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__2));
v___x_466_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_466_, 0, v___x_464_);
lean_ctor_set(v___x_466_, 1, v_a_436_);
lean_ctor_set(v___x_466_, 2, v___x_465_);
lean_inc(v_ref_434_);
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v_ref_434_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
v___x_468_ = l_Lean_PersistentArray_push___redArg(v_traces_455_, v___x_467_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_468_);
v___x_470_ = v___x_457_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_468_);
lean_ctor_set_uint64(v_reuseFailAlloc_478_, sizeof(void*)*1, v_tid_454_);
v___x_470_ = v_reuseFailAlloc_478_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
lean_object* v___x_472_; 
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 4, v___x_470_);
v___x_472_ = v___x_452_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_env_442_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_nextMacroScope_443_);
lean_ctor_set(v_reuseFailAlloc_477_, 2, v_ngen_444_);
lean_ctor_set(v_reuseFailAlloc_477_, 3, v_auxDeclNGen_445_);
lean_ctor_set(v_reuseFailAlloc_477_, 4, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_477_, 5, v_cache_446_);
lean_ctor_set(v_reuseFailAlloc_477_, 6, v_recordedDeps_447_);
lean_ctor_set(v_reuseFailAlloc_477_, 7, v_messages_448_);
lean_ctor_set(v_reuseFailAlloc_477_, 8, v_infoState_449_);
lean_ctor_set(v_reuseFailAlloc_477_, 9, v_snapshotTasks_450_);
v___x_472_ = v_reuseFailAlloc_477_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_473_ = lean_st_ref_put(v___y_432_, v___x_472_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_459_);
v___x_475_ = v___x_438_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_459_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_427_ = stack[0].m_obj;
lean_object* v_msg_428_ = stack[1].m_obj;
lean_object* v___y_429_ = stack[2].m_obj;
lean_object* v___y_430_ = stack[3].m_obj;
lean_object* v___y_431_ = stack[4].m_obj;
lean_object* v___y_432_ = stack[5].m_obj;
lean_object* v_res_482_;
v_res_482_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(v_cls_427_, v_msg_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
stack->m_obj
 = v_res_482_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___boxed(lean_object* v_cls_483_, lean_object* v_msg_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(v_cls_483_, v_msg_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
return v_res_490_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4(lean_object* v___f_491_, lean_object* v_x_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_box(0);
lean_inc_ref(v___y_493_);
v___x_505_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v___y_493_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
if (lean_obj_tag(v_a_506_) == 0)
{
uint8_t v_done_507_; 
v_done_507_ = lean_ctor_get_uint8(v_a_506_, 0);
lean_dec_ref_known(v_a_506_, 0);
if (v_done_507_ == 0)
{
lean_object* v___x_508_; 
lean_dec_ref_known(v___x_505_, 1);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc(v___y_498_);
lean_inc_ref(v___y_497_);
lean_inc(v___y_496_);
lean_inc_ref(v___y_495_);
lean_inc(v___y_494_);
v___x_508_ = lean_apply_12(v___f_491_, v___x_504_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, lean_box(0));
return v___x_508_;
}
else
{
lean_dec_ref(v___y_493_);
lean_dec_ref(v___f_491_);
return v___x_505_;
}
}
else
{
uint8_t v_done_509_; 
lean_dec_ref(v___y_493_);
v_done_509_ = lean_ctor_get_uint8(v_a_506_, sizeof(void*)*1);
if (v_done_509_ == 0)
{
lean_object* v_e_x27_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_528_; 
lean_dec_ref_known(v___x_505_, 1);
v_e_x27_510_ = lean_ctor_get(v_a_506_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v_a_506_);
if (v_isSharedCheck_528_ == 0)
{
v___x_512_ = v_a_506_;
v_isShared_513_ = v_isSharedCheck_528_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_e_x27_510_);
lean_dec(v_a_506_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_528_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; 
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc(v___y_498_);
lean_inc_ref(v___y_497_);
lean_inc(v___y_496_);
lean_inc_ref(v___y_495_);
lean_inc(v___y_494_);
lean_inc_ref(v_e_x27_510_);
v___x_514_ = lean_apply_12(v___f_491_, v___x_504_, v_e_x27_510_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, lean_box(0));
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
if (lean_obj_tag(v_a_515_) == 0)
{
lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_526_; 
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_526_ == 0)
{
lean_object* v_unused_527_; 
v_unused_527_ = lean_ctor_get(v___x_514_, 0);
lean_dec(v_unused_527_);
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_526_;
goto v_resetjp_516_;
}
else
{
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_526_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
uint8_t v_done_519_; lean_object* v___x_521_; 
v_done_519_ = lean_ctor_get_uint8(v_a_515_, 0);
lean_dec_ref_known(v_a_515_, 0);
if (v_isShared_513_ == 0)
{
v___x_521_ = v___x_512_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_e_x27_510_);
v___x_521_ = v_reuseFailAlloc_525_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_523_; 
lean_ctor_set_uint8(v___x_521_, sizeof(void*)*1, v_done_519_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_521_);
v___x_523_ = v___x_517_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_515_, 1);
lean_del_object(v___x_512_);
lean_dec_ref(v_e_x27_510_);
return v___x_514_;
}
}
else
{
lean_del_object(v___x_512_);
lean_dec_ref(v_e_x27_510_);
return v___x_514_;
}
}
}
else
{
lean_dec_ref_known(v_a_506_, 1);
lean_dec_ref(v___f_491_);
return v___x_505_;
}
}
}
else
{
lean_dec_ref(v___y_493_);
lean_dec_ref(v___f_491_);
return v___x_505_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_491_ = stack[0].m_obj;
lean_object* v_x_492_ = stack[1].m_obj;
lean_object* v___y_493_ = stack[2].m_obj;
lean_object* v___y_494_ = stack[3].m_obj;
lean_object* v___y_495_ = stack[4].m_obj;
lean_object* v___y_496_ = stack[5].m_obj;
lean_object* v___y_497_ = stack[6].m_obj;
lean_object* v___y_498_ = stack[7].m_obj;
lean_object* v___y_499_ = stack[8].m_obj;
lean_object* v___y_500_ = stack[9].m_obj;
lean_object* v___y_501_ = stack[10].m_obj;
lean_object* v___y_502_ = stack[11].m_obj;
lean_object* v_res_529_;
v_res_529_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4(v___f_491_, v_x_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
stack->m_obj
 = v_res_529_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4___boxed(lean_object* v___f_530_, lean_object* v_x_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4(v___f_530_, v_x_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
return v_res_543_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2(lean_object* v___f_544_, lean_object* v_x_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_box(0);
lean_inc_ref(v___y_546_);
v___x_558_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_546_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
if (lean_obj_tag(v_a_559_) == 0)
{
uint8_t v_done_560_; 
v_done_560_ = lean_ctor_get_uint8(v_a_559_, 0);
lean_dec_ref_known(v_a_559_, 0);
if (v_done_560_ == 0)
{
lean_object* v___x_561_; 
lean_dec_ref_known(v___x_558_, 1);
lean_inc(v___y_555_);
lean_inc_ref(v___y_554_);
lean_inc(v___y_553_);
lean_inc_ref(v___y_552_);
lean_inc(v___y_551_);
lean_inc_ref(v___y_550_);
lean_inc(v___y_549_);
lean_inc_ref(v___y_548_);
lean_inc(v___y_547_);
v___x_561_ = lean_apply_12(v___f_544_, v___x_557_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, lean_box(0));
return v___x_561_;
}
else
{
lean_dec_ref(v___y_546_);
lean_dec_ref(v___f_544_);
return v___x_558_;
}
}
else
{
uint8_t v_done_562_; 
lean_dec_ref(v___y_546_);
v_done_562_ = lean_ctor_get_uint8(v_a_559_, sizeof(void*)*1);
if (v_done_562_ == 0)
{
lean_object* v_e_x27_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_581_; 
lean_dec_ref_known(v___x_558_, 1);
v_e_x27_563_ = lean_ctor_get(v_a_559_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v_a_559_);
if (v_isSharedCheck_581_ == 0)
{
v___x_565_ = v_a_559_;
v_isShared_566_ = v_isSharedCheck_581_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_e_x27_563_);
lean_dec(v_a_559_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_581_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; 
lean_inc(v___y_555_);
lean_inc_ref(v___y_554_);
lean_inc(v___y_553_);
lean_inc_ref(v___y_552_);
lean_inc(v___y_551_);
lean_inc_ref(v___y_550_);
lean_inc(v___y_549_);
lean_inc_ref(v___y_548_);
lean_inc(v___y_547_);
lean_inc_ref(v_e_x27_563_);
v___x_567_ = lean_apply_12(v___f_544_, v___x_557_, v_e_x27_563_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, lean_box(0));
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_a_568_);
if (lean_obj_tag(v_a_568_) == 0)
{
lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_579_; 
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_579_ == 0)
{
lean_object* v_unused_580_; 
v_unused_580_ = lean_ctor_get(v___x_567_, 0);
lean_dec(v_unused_580_);
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_579_;
goto v_resetjp_569_;
}
else
{
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_579_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
uint8_t v_done_572_; lean_object* v___x_574_; 
v_done_572_ = lean_ctor_get_uint8(v_a_568_, 0);
lean_dec_ref_known(v_a_568_, 0);
if (v_isShared_566_ == 0)
{
v___x_574_ = v___x_565_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_e_x27_563_);
v___x_574_ = v_reuseFailAlloc_578_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_576_; 
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*1, v_done_572_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_574_);
v___x_576_ = v___x_570_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_568_, 1);
lean_del_object(v___x_565_);
lean_dec_ref(v_e_x27_563_);
return v___x_567_;
}
}
else
{
lean_del_object(v___x_565_);
lean_dec_ref(v_e_x27_563_);
return v___x_567_;
}
}
}
else
{
lean_dec_ref_known(v_a_559_, 1);
lean_dec_ref(v___f_544_);
return v___x_558_;
}
}
}
else
{
lean_dec_ref(v___y_546_);
lean_dec_ref(v___f_544_);
return v___x_558_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_544_ = stack[0].m_obj;
lean_object* v_x_545_ = stack[1].m_obj;
lean_object* v___y_546_ = stack[2].m_obj;
lean_object* v___y_547_ = stack[3].m_obj;
lean_object* v___y_548_ = stack[4].m_obj;
lean_object* v___y_549_ = stack[5].m_obj;
lean_object* v___y_550_ = stack[6].m_obj;
lean_object* v___y_551_ = stack[7].m_obj;
lean_object* v___y_552_ = stack[8].m_obj;
lean_object* v___y_553_ = stack[9].m_obj;
lean_object* v___y_554_ = stack[10].m_obj;
lean_object* v___y_555_ = stack[11].m_obj;
lean_object* v_res_582_;
v_res_582_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2(v___f_544_, v_x_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
stack->m_obj
 = v_res_582_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2___boxed(lean_object* v___f_583_, lean_object* v_x_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2(v___f_583_, v_x_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
return v_res_596_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6(lean_object* v_snd_597_, lean_object* v_a_598_, lean_object* v___x_599_, lean_object* v_____r_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_613_ = lean_array_push(v_snd_597_, v_a_598_);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_599_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
v___x_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
return v___x_616_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_597_ = stack[0].m_obj;
lean_object* v_a_598_ = stack[1].m_obj;
lean_object* v___x_599_ = stack[2].m_obj;
lean_object* v_____r_600_ = stack[3].m_obj;
lean_object* v___y_601_ = stack[4].m_obj;
lean_object* v___y_602_ = stack[5].m_obj;
lean_object* v___y_603_ = stack[6].m_obj;
lean_object* v___y_604_ = stack[7].m_obj;
lean_object* v___y_605_ = stack[8].m_obj;
lean_object* v___y_606_ = stack[9].m_obj;
lean_object* v___y_607_ = stack[10].m_obj;
lean_object* v___y_608_ = stack[11].m_obj;
lean_object* v___y_609_ = stack[12].m_obj;
lean_object* v___y_610_ = stack[13].m_obj;
lean_object* v___y_611_ = stack[14].m_obj;
lean_object* v_res_617_;
v_res_617_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6(v_snd_597_, v_a_598_, v___x_599_, v_____r_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
stack->m_obj
 = v_res_617_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6___boxed(lean_object* v_snd_618_, lean_object* v_a_619_, lean_object* v___x_620_, lean_object* v_____r_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6(v_snd_618_, v_a_619_, v___x_620_, v_____r_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
return v_res_634_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5(lean_object* v___x_635_, lean_object* v___f_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_box(0);
lean_inc_ref(v___y_637_);
v___x_649_ = l_Lean_Meta_Sym_DSimp_evalGround___redArg(v___x_635_, v___y_637_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
if (lean_obj_tag(v_a_650_) == 0)
{
uint8_t v_done_651_; 
v_done_651_ = lean_ctor_get_uint8(v_a_650_, 0);
lean_dec_ref_known(v_a_650_, 0);
if (v_done_651_ == 0)
{
lean_object* v___x_652_; 
lean_dec_ref_known(v___x_649_, 1);
v___x_652_ = lean_apply_12(v___f_636_, v___x_648_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, lean_box(0));
return v___x_652_;
}
else
{
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec_ref(v___f_636_);
return v___x_649_;
}
}
else
{
uint8_t v_done_653_; 
lean_dec_ref(v___y_637_);
v_done_653_ = lean_ctor_get_uint8(v_a_650_, sizeof(void*)*1);
if (v_done_653_ == 0)
{
lean_object* v_e_x27_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_672_; 
lean_dec_ref_known(v___x_649_, 1);
v_e_x27_654_ = lean_ctor_get(v_a_650_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v_a_650_);
if (v_isSharedCheck_672_ == 0)
{
v___x_656_ = v_a_650_;
v_isShared_657_ = v_isSharedCheck_672_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_e_x27_654_);
lean_dec(v_a_650_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_672_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; 
lean_inc_ref(v_e_x27_654_);
v___x_658_ = lean_apply_12(v___f_636_, v___x_648_, v_e_x27_654_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, lean_box(0));
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
if (lean_obj_tag(v_a_659_) == 0)
{
lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_670_; 
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; 
v_unused_671_ = lean_ctor_get(v___x_658_, 0);
lean_dec(v_unused_671_);
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_670_;
goto v_resetjp_660_;
}
else
{
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_670_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
uint8_t v_done_663_; lean_object* v___x_665_; 
v_done_663_ = lean_ctor_get_uint8(v_a_659_, 0);
lean_dec_ref_known(v_a_659_, 0);
if (v_isShared_657_ == 0)
{
v___x_665_ = v___x_656_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_e_x27_654_);
v___x_665_ = v_reuseFailAlloc_669_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_667_; 
lean_ctor_set_uint8(v___x_665_, sizeof(void*)*1, v_done_663_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_665_);
v___x_667_ = v___x_661_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_659_, 1);
lean_del_object(v___x_656_);
lean_dec_ref(v_e_x27_654_);
return v___x_658_;
}
}
else
{
lean_del_object(v___x_656_);
lean_dec_ref(v_e_x27_654_);
return v___x_658_;
}
}
}
else
{
lean_dec_ref_known(v_a_650_, 1);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___f_636_);
return v___x_649_;
}
}
}
else
{
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec_ref(v___f_636_);
return v___x_649_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_635_ = stack[0].m_obj;
lean_object* v___f_636_ = stack[1].m_obj;
lean_object* v___y_637_ = stack[2].m_obj;
lean_object* v___y_638_ = stack[3].m_obj;
lean_object* v___y_639_ = stack[4].m_obj;
lean_object* v___y_640_ = stack[5].m_obj;
lean_object* v___y_641_ = stack[6].m_obj;
lean_object* v___y_642_ = stack[7].m_obj;
lean_object* v___y_643_ = stack[8].m_obj;
lean_object* v___y_644_ = stack[9].m_obj;
lean_object* v___y_645_ = stack[10].m_obj;
lean_object* v___y_646_ = stack[11].m_obj;
lean_object* v_res_673_;
v_res_673_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5(v___x_635_, v___f_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
stack->m_obj
 = v_res_673_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5___boxed(lean_object* v___x_674_, lean_object* v___f_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5(v___x_674_, v___f_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___x_674_);
return v_res_687_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_712_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__10));
v___x_713_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__12));
v___x_714_ = l_Lean_Name_append(v___x_713_, v___x_712_);
return v___x_714_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__15(void){
_start:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__14));
v___x_717_ = l_Lean_stringToMessageData(v___x_716_);
return v___x_717_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg(lean_object* v_upperBound_718_, lean_object* v___x_719_, lean_object* v_config_720_, lean_object* v_a_721_, lean_object* v_b_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___y_736_; uint8_t v___x_758_; 
v___x_758_ = lean_nat_dec_lt(v_a_721_, v_upperBound_718_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; 
lean_dec(v_a_721_);
lean_dec_ref(v_config_720_);
v___x_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_759_, 0, v_b_722_);
return v___x_759_;
}
else
{
lean_object* v_snd_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_836_; 
v_snd_760_ = lean_ctor_get(v_b_722_, 1);
v_isSharedCheck_836_ = !lean_is_exclusive(v_b_722_);
if (v_isSharedCheck_836_ == 0)
{
lean_object* v_unused_837_; 
v_unused_837_ = lean_ctor_get(v_b_722_, 0);
lean_dec(v_unused_837_);
v___x_762_ = v_b_722_;
v_isShared_763_ = v_isSharedCheck_836_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_snd_760_);
lean_dec(v_b_722_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_836_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
uint8_t v___x_764_; lean_object* v_methods_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_764_ = 1;
v_methods_765_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__6));
v___x_766_ = lean_box(0);
v___x_767_ = lean_array_fget_borrowed(v___x_719_, v_a_721_);
lean_inc(v___x_767_);
lean_inc_ref(v_config_720_);
v___x_768_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v___x_764_, v_methods_765_, v_config_720_, v___x_767_, v___y_724_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v_type_770_; lean_object* v_value_771_; uint8_t v___x_772_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
v_type_770_ = lean_ctor_get(v_a_769_, 1);
v_value_771_ = lean_ctor_get(v_a_769_, 2);
lean_inc_ref(v_type_770_);
v___x_772_ = l_Lean_Expr_isFalse(v_type_770_);
if (v___x_772_ == 0)
{
lean_object* v_type_773_; lean_object* v___f_774_; uint8_t v___x_803_; 
lean_del_object(v___x_762_);
v_type_773_ = lean_ctor_get(v___x_767_, 1);
lean_inc(v_a_769_);
lean_inc(v_snd_760_);
v___f_774_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6___boxed), 16, 3);
lean_closure_set(v___f_774_, 0, v_snd_760_);
lean_closure_set(v___f_774_, 1, v_a_769_);
lean_closure_set(v___f_774_, 2, v___x_766_);
v___x_803_ = lean_expr_eqv(v_type_773_, v_type_770_);
if (v___x_803_ == 0)
{
lean_inc_ref(v_type_770_);
lean_dec(v_a_769_);
lean_dec(v_snd_760_);
goto v___jp_778_;
}
else
{
if (v___x_772_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; 
lean_dec_ref(v___f_774_);
v___x_804_ = lean_box(0);
v___x_805_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6(v_snd_760_, v_a_769_, v___x_766_, v___x_804_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
v___y_736_ = v___x_805_;
goto v___jp_735_;
}
else
{
lean_inc_ref(v_type_770_);
lean_dec(v_a_769_);
lean_dec(v_snd_760_);
goto v___jp_778_;
}
}
v___jp_775_:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_box(0);
v___x_777_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7(v___x_758_, v___f_774_, v___x_776_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
v___y_736_ = v___x_777_;
goto v___jp_735_;
}
v___jp_778_:
{
lean_object* v_toCold_779_; lean_object* v_options_780_; uint8_t v_hasTrace_781_; 
v_toCold_779_ = lean_ctor_get(v___y_732_, 0);
v_options_780_ = lean_ctor_get(v_toCold_779_, 2);
v_hasTrace_781_ = lean_ctor_get_uint8(v_options_780_, sizeof(void*)*1);
if (v_hasTrace_781_ == 0)
{
lean_dec_ref(v_type_770_);
goto v___jp_775_;
}
else
{
lean_object* v_inheritedTraceOptions_782_; lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v_inheritedTraceOptions_782_ = lean_ctor_get(v_toCold_779_, 11);
v___x_783_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__10));
v___x_784_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13);
v___x_785_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_782_, v_options_780_, v___x_784_);
if (v___x_785_ == 0)
{
lean_dec_ref(v_type_770_);
goto v___jp_775_;
}
else
{
lean_object* v_type_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_type_786_ = lean_ctor_get(v___x_767_, 1);
lean_inc_ref(v_type_786_);
v___x_787_ = l_Lean_MessageData_ofExpr(v_type_786_);
v___x_788_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__15);
v___x_789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_787_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = l_Lean_MessageData_ofExpr(v_type_770_);
v___x_791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_789_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(v___x_783_, v___x_791_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_792_, 1);
v___x_794_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7(v___x_758_, v___f_774_, v_a_793_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
v___y_736_ = v___x_794_;
goto v___jp_735_;
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref(v___f_774_);
lean_dec(v_a_721_);
lean_dec_ref(v_config_720_);
v_a_795_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_792_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_792_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_806_; 
lean_inc_ref(v_value_771_);
lean_dec(v_a_769_);
lean_dec(v_a_721_);
lean_dec_ref(v_config_720_);
v___x_806_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_771_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_818_; 
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; 
v_unused_819_ = lean_ctor_get(v___x_806_, 0);
lean_dec(v_unused_819_);
v___x_808_ = v___x_806_;
v_isShared_809_ = v_isSharedCheck_818_;
goto v_resetjp_807_;
}
else
{
lean_dec(v___x_806_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_818_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_810_ = lean_box(v___x_758_);
v___x_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v___x_811_);
v___x_813_ = v___x_762_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_snd_760_);
v___x_813_ = v_reuseFailAlloc_817_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_815_; 
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 0, v___x_813_);
v___x_815_ = v___x_808_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
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
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_del_object(v___x_762_);
lean_dec(v_snd_760_);
v_a_820_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_806_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_806_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_del_object(v___x_762_);
lean_dec(v_snd_760_);
lean_dec(v_a_721_);
lean_dec_ref(v_config_720_);
v_a_828_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_768_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_768_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
v___jp_735_:
{
if (lean_obj_tag(v___y_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_749_; 
v_a_737_ = lean_ctor_get(v___y_736_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___y_736_);
if (v_isSharedCheck_749_ == 0)
{
v___x_739_ = v___y_736_;
v_isShared_740_ = v_isSharedCheck_749_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___y_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_749_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
if (lean_obj_tag(v_a_737_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_743_; 
lean_dec(v_a_721_);
lean_dec_ref(v_config_720_);
v_a_741_ = lean_ctor_get(v_a_737_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v_a_737_, 1);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v_a_741_);
v___x_743_ = v___x_739_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
lean_del_object(v___x_739_);
v_a_745_ = lean_ctor_get(v_a_737_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v_a_737_, 1);
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = lean_nat_add(v_a_721_, v___x_746_);
lean_dec(v_a_721_);
v_a_721_ = v___x_747_;
v_b_722_ = v_a_745_;
goto _start;
}
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec(v_a_721_);
lean_dec_ref(v_config_720_);
v_a_750_ = lean_ctor_get(v___y_736_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___y_736_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___y_736_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___y_736_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_718_ = stack[0].m_obj;
lean_object* v___x_719_ = stack[1].m_obj;
lean_object* v_config_720_ = stack[2].m_obj;
lean_object* v_a_721_ = stack[3].m_obj;
lean_object* v_b_722_ = stack[4].m_obj;
lean_object* v___y_723_ = stack[5].m_obj;
lean_object* v___y_724_ = stack[6].m_obj;
lean_object* v___y_725_ = stack[7].m_obj;
lean_object* v___y_726_ = stack[8].m_obj;
lean_object* v___y_727_ = stack[9].m_obj;
lean_object* v___y_728_ = stack[10].m_obj;
lean_object* v___y_729_ = stack[11].m_obj;
lean_object* v___y_730_ = stack[12].m_obj;
lean_object* v___y_731_ = stack[13].m_obj;
lean_object* v___y_732_ = stack[14].m_obj;
lean_object* v___y_733_ = stack[15].m_obj;
lean_object* v_res_838_;
v_res_838_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg(v_upperBound_718_, v___x_719_, v_config_720_, v_a_721_, v_b_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_);
stack->m_obj
 = v_res_838_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_839_ = _args[0];
lean_object* v___x_840_ = _args[1];
lean_object* v_config_841_ = _args[2];
lean_object* v_a_842_ = _args[3];
lean_object* v_b_843_ = _args[4];
lean_object* v___y_844_ = _args[5];
lean_object* v___y_845_ = _args[6];
lean_object* v___y_846_ = _args[7];
lean_object* v___y_847_ = _args[8];
lean_object* v___y_848_ = _args[9];
lean_object* v___y_849_ = _args[10];
lean_object* v___y_850_ = _args[11];
lean_object* v___y_851_ = _args[12];
lean_object* v___y_852_ = _args[13];
lean_object* v___y_853_ = _args[14];
lean_object* v___y_854_ = _args[15];
lean_object* v___y_855_ = _args[16];
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg(v_upperBound_839_, v___x_840_, v_config_841_, v_a_842_, v_b_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec_ref(v___x_840_);
lean_dec(v_upperBound_839_);
return v_res_856_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0(lean_object* v_config_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_870_; lean_object* v_hypotheses_871_; lean_object* v___x_872_; lean_object* v_newHyps_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_870_ = lean_st_ref_get(v___y_859_);
v_hypotheses_871_ = lean_ctor_get(v___x_870_, 3);
lean_inc_ref(v_hypotheses_871_);
lean_dec(v___x_870_);
v___x_872_ = lean_array_get_size(v_hypotheses_871_);
v_newHyps_873_ = lean_mk_empty_array_with_capacity(v___x_872_);
v___x_874_ = lean_unsigned_to_nat(0u);
v___x_875_ = lean_box(0);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v_newHyps_873_);
v___x_877_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg(v___x_872_, v_hypotheses_871_, v_config_857_, v___x_874_, v___x_876_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec_ref(v_hypotheses_871_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_907_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_907_ == 0)
{
v___x_880_ = v___x_877_;
v_isShared_881_ = v_isSharedCheck_907_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_877_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_907_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v_fst_882_; 
v_fst_882_ = lean_ctor_get(v_a_878_, 0);
if (lean_obj_tag(v_fst_882_) == 0)
{
lean_object* v_snd_883_; lean_object* v___x_884_; lean_object* v_caches_885_; lean_object* v_typeAnalysis_886_; lean_object* v_target_887_; uint8_t v_didChange_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_901_; 
v_snd_883_ = lean_ctor_get(v_a_878_, 1);
lean_inc(v_snd_883_);
lean_dec(v_a_878_);
v___x_884_ = lean_st_ref_take(v___y_859_);
v_caches_885_ = lean_ctor_get(v___x_884_, 0);
v_typeAnalysis_886_ = lean_ctor_get(v___x_884_, 1);
v_target_887_ = lean_ctor_get(v___x_884_, 2);
v_didChange_888_ = lean_ctor_get_uint8(v___x_884_, sizeof(void*)*4);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_901_ == 0)
{
lean_object* v_unused_902_; 
v_unused_902_ = lean_ctor_get(v___x_884_, 3);
lean_dec(v_unused_902_);
v___x_890_ = v___x_884_;
v_isShared_891_ = v_isSharedCheck_901_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_target_887_);
lean_inc(v_typeAnalysis_886_);
lean_inc(v_caches_885_);
lean_dec(v___x_884_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_901_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 3, v_snd_883_);
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_caches_885_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_typeAnalysis_886_);
lean_ctor_set(v_reuseFailAlloc_900_, 2, v_target_887_);
lean_ctor_set(v_reuseFailAlloc_900_, 3, v_snd_883_);
lean_ctor_set_uint8(v_reuseFailAlloc_900_, sizeof(void*)*4, v_didChange_888_);
v___x_893_ = v_reuseFailAlloc_900_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_894_; uint8_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_898_; 
v___x_894_ = lean_st_ref_put(v___y_859_, v___x_893_);
v___x_895_ = 0;
v___x_896_ = lean_box(v___x_895_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_896_);
v___x_898_ = v___x_880_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
lean_object* v_val_903_; lean_object* v___x_905_; 
lean_inc_ref(v_fst_882_);
lean_dec(v_a_878_);
v_val_903_ = lean_ctor_get(v_fst_882_, 0);
lean_inc(v_val_903_);
lean_dec_ref_known(v_fst_882_, 1);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v_val_903_);
v___x_905_ = v___x_880_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_val_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
v_a_908_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_877_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_877_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_config_857_ = stack[0].m_obj;
lean_object* v___y_858_ = stack[1].m_obj;
lean_object* v___y_859_ = stack[2].m_obj;
lean_object* v___y_860_ = stack[3].m_obj;
lean_object* v___y_861_ = stack[4].m_obj;
lean_object* v___y_862_ = stack[5].m_obj;
lean_object* v___y_863_ = stack[6].m_obj;
lean_object* v___y_864_ = stack[7].m_obj;
lean_object* v___y_865_ = stack[8].m_obj;
lean_object* v___y_866_ = stack[9].m_obj;
lean_object* v___y_867_ = stack[10].m_obj;
lean_object* v___y_868_ = stack[11].m_obj;
lean_object* v_res_916_;
v_res_916_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0(v_config_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
stack->m_obj
 = v_res_916_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0___boxed(lean_object* v_config_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0(v_config_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
return v_res_930_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1(lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_config_943_; lean_object* v_maxSteps_944_; uint8_t v___x_945_; lean_object* v_config_946_; lean_object* v___f_947_; lean_object* v___x_948_; lean_object* v_target_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v_config_943_ = lean_ctor_get(v___y_931_, 0);
v_maxSteps_944_ = lean_ctor_get(v_config_943_, 1);
v___x_945_ = 1;
lean_inc(v_maxSteps_944_);
v_config_946_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_config_946_, 0, v_maxSteps_944_);
lean_ctor_set_uint8(v_config_946_, sizeof(void*)*1, v___x_945_);
v___f_947_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0___boxed), 13, 1);
lean_closure_set(v___f_947_, 0, v_config_946_);
v___x_948_ = lean_st_ref_get(v___y_932_);
v_target_949_ = lean_ctor_get(v___x_948_, 2);
lean_inc_ref(v_target_949_);
lean_dec(v___x_948_);
v___x_950_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_949_);
lean_dec_ref(v_target_949_);
v___x_951_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__2___redArg(v___x_950_, v___f_947_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
return v___x_951_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_931_ = stack[0].m_obj;
lean_object* v___y_932_ = stack[1].m_obj;
lean_object* v___y_933_ = stack[2].m_obj;
lean_object* v___y_934_ = stack[3].m_obj;
lean_object* v___y_935_ = stack[4].m_obj;
lean_object* v___y_936_ = stack[5].m_obj;
lean_object* v___y_937_ = stack[6].m_obj;
lean_object* v___y_938_ = stack[7].m_obj;
lean_object* v___y_939_ = stack[8].m_obj;
lean_object* v___y_940_ = stack[9].m_obj;
lean_object* v___y_941_ = stack[10].m_obj;
lean_object* v_res_952_;
v_res_952_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1(v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
stack->m_obj
 = v_res_952_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1___boxed(lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1(v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
return v_res_965_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0(lean_object* v_cls_974_, lean_object* v_msg_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(v_cls_974_, v_msg_975_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
return v___x_988_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_974_ = stack[0].m_obj;
lean_object* v_msg_975_ = stack[1].m_obj;
lean_object* v___y_976_ = stack[2].m_obj;
lean_object* v___y_977_ = stack[3].m_obj;
lean_object* v___y_978_ = stack[4].m_obj;
lean_object* v___y_979_ = stack[5].m_obj;
lean_object* v___y_980_ = stack[6].m_obj;
lean_object* v___y_981_ = stack[7].m_obj;
lean_object* v___y_982_ = stack[8].m_obj;
lean_object* v___y_983_ = stack[9].m_obj;
lean_object* v___y_984_ = stack[10].m_obj;
lean_object* v___y_985_ = stack[11].m_obj;
lean_object* v___y_986_ = stack[12].m_obj;
lean_object* v_res_989_;
v_res_989_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0(v_cls_974_, v_msg_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
stack->m_obj
 = v_res_989_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___boxed(lean_object* v_cls_990_, lean_object* v_msg_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0(v_cls_990_, v_msg_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
return v_res_1004_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1(lean_object* v_upperBound_1005_, lean_object* v___x_1006_, lean_object* v_config_1007_, lean_object* v_inst_1008_, lean_object* v_R_1009_, lean_object* v_a_1010_, lean_object* v_b_1011_, lean_object* v_c_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg(v_upperBound_1005_, v___x_1006_, v_config_1007_, v_a_1010_, v_b_1011_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1005_ = stack[0].m_obj;
lean_object* v___x_1006_ = stack[1].m_obj;
lean_object* v_config_1007_ = stack[2].m_obj;
lean_object* v_a_1010_ = stack[5].m_obj;
lean_object* v_b_1011_ = stack[6].m_obj;
lean_object* v___y_1013_ = stack[8].m_obj;
lean_object* v___y_1014_ = stack[9].m_obj;
lean_object* v___y_1015_ = stack[10].m_obj;
lean_object* v___y_1016_ = stack[11].m_obj;
lean_object* v___y_1017_ = stack[12].m_obj;
lean_object* v___y_1018_ = stack[13].m_obj;
lean_object* v___y_1019_ = stack[14].m_obj;
lean_object* v___y_1020_ = stack[15].m_obj;
lean_object* v___y_1021_ = stack[16].m_obj;
lean_object* v___y_1022_ = stack[17].m_obj;
lean_object* v___y_1023_ = stack[18].m_obj;
lean_object* v_res_1026_;
v_res_1026_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1(v_upperBound_1005_, v___x_1006_, v_config_1007_, lean_box(0), lean_box(0), v_a_1010_, v_b_1011_, lean_box(0), v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
stack->m_obj
 = v_res_1026_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_1027_ = _args[0];
lean_object* v___x_1028_ = _args[1];
lean_object* v_config_1029_ = _args[2];
lean_object* v_inst_1030_ = _args[3];
lean_object* v_R_1031_ = _args[4];
lean_object* v_a_1032_ = _args[5];
lean_object* v_b_1033_ = _args[6];
lean_object* v_c_1034_ = _args[7];
lean_object* v___y_1035_ = _args[8];
lean_object* v___y_1036_ = _args[9];
lean_object* v___y_1037_ = _args[10];
lean_object* v___y_1038_ = _args[11];
lean_object* v___y_1039_ = _args[12];
lean_object* v___y_1040_ = _args[13];
lean_object* v___y_1041_ = _args[14];
lean_object* v___y_1042_ = _args[15];
lean_object* v___y_1043_ = _args[16];
lean_object* v___y_1044_ = _args[17];
lean_object* v___y_1045_ = _args[18];
lean_object* v___y_1046_ = _args[19];
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1(v_upperBound_1027_, v___x_1028_, v_config_1029_, v_inst_1030_, v_R_1031_, v_a_1032_, v_b_1033_, v_c_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec_ref(v___x_1028_);
lean_dec(v_upperBound_1027_);
return v_res_1047_;
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

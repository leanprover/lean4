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
lean_object* l_Lean_Meta_Sym_DSimp_dsimpProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_85_ = l_Lean_Meta_Sym_DSimp_dsimpProj(v_e_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
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
v___x_252_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_240_, v___y_246_, v___y_248_, v___y_249_);
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
lean_inc(v_a_312_);
if (lean_obj_tag(v_a_312_) == 0)
{
lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_323_; 
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
lean_dec_ref_known(v_a_312_, 1);
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
uint8_t v___x_11514__boxed_384_; lean_object* v_res_385_; 
v___x_11514__boxed_384_ = lean_unbox(v___x_369_);
v_res_385_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7(v___x_11514__boxed_384_, v___f_370_, v_____r_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
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
lean_object* v___x_392_; lean_object* v_env_393_; lean_object* v___x_394_; lean_object* v_toCold_395_; lean_object* v_mctx_396_; lean_object* v_lctx_397_; lean_object* v_options_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_392_ = lean_st_ref_get(v___y_390_);
v_env_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc_ref(v_env_393_);
lean_dec(v___x_392_);
v___x_394_ = lean_st_ref_get(v___y_388_);
v_toCold_395_ = lean_ctor_get(v___y_389_, 0);
v_mctx_396_ = lean_ctor_get(v___x_394_, 0);
lean_inc_ref(v_mctx_396_);
lean_dec(v___x_394_);
v_lctx_397_ = lean_ctor_get(v___y_387_, 2);
v_options_398_ = lean_ctor_get(v_toCold_395_, 2);
lean_inc_ref(v_options_398_);
lean_inc_ref(v_lctx_397_);
v___x_399_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_399_, 0, v_env_393_);
lean_ctor_set(v___x_399_, 1, v_mctx_396_);
lean_ctor_set(v___x_399_, 2, v_lctx_397_);
lean_ctor_set(v___x_399_, 3, v_options_398_);
v___x_400_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set(v___x_400_, 1, v_msgData_386_);
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0___boxed(lean_object* v_msgData_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0(v_msgData_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
return v_res_408_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_409_; double v___x_410_; 
v___x_409_ = lean_unsigned_to_nat(0u);
v___x_410_ = lean_float_of_nat(v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(lean_object* v_cls_414_, lean_object* v_msg_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_ref_421_; lean_object* v___x_422_; lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_468_; 
v_ref_421_ = lean_ctor_get(v___y_418_, 2);
v___x_422_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0_spec__0(v_msg_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
v_a_423_ = lean_ctor_get(v___x_422_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_422_);
if (v_isSharedCheck_468_ == 0)
{
v___x_425_ = v___x_422_;
v_isShared_426_ = v_isSharedCheck_468_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_422_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_468_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v_traceState_428_; lean_object* v_env_429_; lean_object* v_nextMacroScope_430_; lean_object* v_ngen_431_; lean_object* v_auxDeclNGen_432_; lean_object* v_cache_433_; lean_object* v_recordedDeps_434_; lean_object* v_messages_435_; lean_object* v_infoState_436_; lean_object* v_snapshotTasks_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_467_; 
v___x_427_ = lean_st_ref_take(v___y_419_);
v_traceState_428_ = lean_ctor_get(v___x_427_, 4);
v_env_429_ = lean_ctor_get(v___x_427_, 0);
v_nextMacroScope_430_ = lean_ctor_get(v___x_427_, 1);
v_ngen_431_ = lean_ctor_get(v___x_427_, 2);
v_auxDeclNGen_432_ = lean_ctor_get(v___x_427_, 3);
v_cache_433_ = lean_ctor_get(v___x_427_, 5);
v_recordedDeps_434_ = lean_ctor_get(v___x_427_, 6);
v_messages_435_ = lean_ctor_get(v___x_427_, 7);
v_infoState_436_ = lean_ctor_get(v___x_427_, 8);
v_snapshotTasks_437_ = lean_ctor_get(v___x_427_, 9);
v_isSharedCheck_467_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_467_ == 0)
{
v___x_439_ = v___x_427_;
v_isShared_440_ = v_isSharedCheck_467_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_snapshotTasks_437_);
lean_inc(v_infoState_436_);
lean_inc(v_messages_435_);
lean_inc(v_recordedDeps_434_);
lean_inc(v_cache_433_);
lean_inc(v_traceState_428_);
lean_inc(v_auxDeclNGen_432_);
lean_inc(v_ngen_431_);
lean_inc(v_nextMacroScope_430_);
lean_inc(v_env_429_);
lean_dec(v___x_427_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_467_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
uint64_t v_tid_441_; lean_object* v_traces_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_466_; 
v_tid_441_ = lean_ctor_get_uint64(v_traceState_428_, sizeof(void*)*1);
v_traces_442_ = lean_ctor_get(v_traceState_428_, 0);
v_isSharedCheck_466_ = !lean_is_exclusive(v_traceState_428_);
if (v_isSharedCheck_466_ == 0)
{
v___x_444_ = v_traceState_428_;
v_isShared_445_ = v_isSharedCheck_466_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_traces_442_);
lean_dec(v_traceState_428_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_466_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_446_; lean_object* v___x_447_; double v___x_448_; uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_457_; 
v___x_446_ = lean_box(0);
v___x_447_ = lean_box(0);
v___x_448_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__0);
v___x_449_ = 0;
v___x_450_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__1));
v___x_451_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_451_, 0, v_cls_414_);
lean_ctor_set(v___x_451_, 1, v___x_447_);
lean_ctor_set(v___x_451_, 2, v___x_450_);
lean_ctor_set_float(v___x_451_, sizeof(void*)*3, v___x_448_);
lean_ctor_set_float(v___x_451_, sizeof(void*)*3 + 8, v___x_448_);
lean_ctor_set_uint8(v___x_451_, sizeof(void*)*3 + 16, v___x_449_);
v___x_452_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___closed__2));
v___x_453_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set(v___x_453_, 1, v_a_423_);
lean_ctor_set(v___x_453_, 2, v___x_452_);
lean_inc(v_ref_421_);
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v_ref_421_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = l_Lean_PersistentArray_push___redArg(v_traces_442_, v___x_454_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_455_);
v___x_457_ = v___x_444_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_455_);
lean_ctor_set_uint64(v_reuseFailAlloc_465_, sizeof(void*)*1, v_tid_441_);
v___x_457_ = v_reuseFailAlloc_465_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_459_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 4, v___x_457_);
v___x_459_ = v___x_439_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_env_429_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v_nextMacroScope_430_);
lean_ctor_set(v_reuseFailAlloc_464_, 2, v_ngen_431_);
lean_ctor_set(v_reuseFailAlloc_464_, 3, v_auxDeclNGen_432_);
lean_ctor_set(v_reuseFailAlloc_464_, 4, v___x_457_);
lean_ctor_set(v_reuseFailAlloc_464_, 5, v_cache_433_);
lean_ctor_set(v_reuseFailAlloc_464_, 6, v_recordedDeps_434_);
lean_ctor_set(v_reuseFailAlloc_464_, 7, v_messages_435_);
lean_ctor_set(v_reuseFailAlloc_464_, 8, v_infoState_436_);
lean_ctor_set(v_reuseFailAlloc_464_, 9, v_snapshotTasks_437_);
v___x_459_ = v_reuseFailAlloc_464_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = lean_st_ref_put(v___y_419_, v___x_459_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_446_);
v___x_462_ = v___x_425_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_446_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___boxed(lean_object* v_cls_469_, lean_object* v_msg_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(v_cls_469_, v_msg_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4(lean_object* v___f_477_, lean_object* v_x_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_box(0);
lean_inc_ref(v___y_479_);
v___x_491_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v___y_479_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
if (lean_obj_tag(v_a_492_) == 0)
{
uint8_t v_done_493_; 
v_done_493_ = lean_ctor_get_uint8(v_a_492_, 0);
lean_dec_ref_known(v_a_492_, 0);
if (v_done_493_ == 0)
{
lean_object* v___x_494_; 
lean_dec_ref_known(v___x_491_, 1);
lean_inc(v___y_488_);
lean_inc_ref(v___y_487_);
lean_inc(v___y_486_);
lean_inc_ref(v___y_485_);
lean_inc(v___y_484_);
lean_inc_ref(v___y_483_);
lean_inc(v___y_482_);
lean_inc_ref(v___y_481_);
lean_inc(v___y_480_);
v___x_494_ = lean_apply_12(v___f_477_, v___x_490_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, lean_box(0));
return v___x_494_;
}
else
{
lean_dec_ref(v___y_479_);
lean_dec_ref(v___f_477_);
return v___x_491_;
}
}
else
{
uint8_t v_done_495_; 
lean_dec_ref(v___y_479_);
v_done_495_ = lean_ctor_get_uint8(v_a_492_, sizeof(void*)*1);
if (v_done_495_ == 0)
{
lean_object* v_e_x27_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_514_; 
lean_dec_ref_known(v___x_491_, 1);
v_e_x27_496_ = lean_ctor_get(v_a_492_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v_a_492_);
if (v_isSharedCheck_514_ == 0)
{
v___x_498_ = v_a_492_;
v_isShared_499_ = v_isSharedCheck_514_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_e_x27_496_);
lean_dec(v_a_492_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_514_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; 
lean_inc(v___y_488_);
lean_inc_ref(v___y_487_);
lean_inc(v___y_486_);
lean_inc_ref(v___y_485_);
lean_inc(v___y_484_);
lean_inc_ref(v___y_483_);
lean_inc(v___y_482_);
lean_inc_ref(v___y_481_);
lean_inc(v___y_480_);
lean_inc_ref(v_e_x27_496_);
v___x_500_ = lean_apply_12(v___f_477_, v___x_490_, v_e_x27_496_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, lean_box(0));
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
if (lean_obj_tag(v_a_501_) == 0)
{
lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_512_; 
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; 
v_unused_513_ = lean_ctor_get(v___x_500_, 0);
lean_dec(v_unused_513_);
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_512_;
goto v_resetjp_502_;
}
else
{
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_512_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
uint8_t v_done_505_; lean_object* v___x_507_; 
v_done_505_ = lean_ctor_get_uint8(v_a_501_, 0);
lean_dec_ref_known(v_a_501_, 0);
if (v_isShared_499_ == 0)
{
v___x_507_ = v___x_498_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_e_x27_496_);
v___x_507_ = v_reuseFailAlloc_511_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_509_; 
lean_ctor_set_uint8(v___x_507_, sizeof(void*)*1, v_done_505_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_507_);
v___x_509_ = v___x_503_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_501_, 1);
lean_del_object(v___x_498_);
lean_dec_ref(v_e_x27_496_);
return v___x_500_;
}
}
else
{
lean_del_object(v___x_498_);
lean_dec_ref(v_e_x27_496_);
return v___x_500_;
}
}
}
else
{
lean_dec_ref_known(v_a_492_, 1);
lean_dec_ref(v___f_477_);
return v___x_491_;
}
}
}
else
{
lean_dec_ref(v___y_479_);
lean_dec_ref(v___f_477_);
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4___boxed(lean_object* v___f_515_, lean_object* v_x_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__4(v___f_515_, v_x_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2(lean_object* v___f_529_, lean_object* v_x_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_box(0);
lean_inc_ref(v___y_531_);
v___x_543_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_531_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_544_);
if (lean_obj_tag(v_a_544_) == 0)
{
uint8_t v_done_545_; 
v_done_545_ = lean_ctor_get_uint8(v_a_544_, 0);
lean_dec_ref_known(v_a_544_, 0);
if (v_done_545_ == 0)
{
lean_object* v___x_546_; 
lean_dec_ref_known(v___x_543_, 1);
lean_inc(v___y_540_);
lean_inc_ref(v___y_539_);
lean_inc(v___y_538_);
lean_inc_ref(v___y_537_);
lean_inc(v___y_536_);
lean_inc_ref(v___y_535_);
lean_inc(v___y_534_);
lean_inc_ref(v___y_533_);
lean_inc(v___y_532_);
v___x_546_ = lean_apply_12(v___f_529_, v___x_542_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, lean_box(0));
return v___x_546_;
}
else
{
lean_dec_ref(v___y_531_);
lean_dec_ref(v___f_529_);
return v___x_543_;
}
}
else
{
uint8_t v_done_547_; 
lean_dec_ref(v___y_531_);
v_done_547_ = lean_ctor_get_uint8(v_a_544_, sizeof(void*)*1);
if (v_done_547_ == 0)
{
lean_object* v_e_x27_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_566_; 
lean_dec_ref_known(v___x_543_, 1);
v_e_x27_548_ = lean_ctor_get(v_a_544_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v_a_544_);
if (v_isSharedCheck_566_ == 0)
{
v___x_550_ = v_a_544_;
v_isShared_551_ = v_isSharedCheck_566_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_e_x27_548_);
lean_dec(v_a_544_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_566_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; 
lean_inc(v___y_540_);
lean_inc_ref(v___y_539_);
lean_inc(v___y_538_);
lean_inc_ref(v___y_537_);
lean_inc(v___y_536_);
lean_inc_ref(v___y_535_);
lean_inc(v___y_534_);
lean_inc_ref(v___y_533_);
lean_inc(v___y_532_);
lean_inc_ref(v_e_x27_548_);
v___x_552_ = lean_apply_12(v___f_529_, v___x_542_, v_e_x27_548_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, lean_box(0));
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
if (lean_obj_tag(v_a_553_) == 0)
{
lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_564_; 
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_564_ == 0)
{
lean_object* v_unused_565_; 
v_unused_565_ = lean_ctor_get(v___x_552_, 0);
lean_dec(v_unused_565_);
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_564_;
goto v_resetjp_554_;
}
else
{
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_564_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
uint8_t v_done_557_; lean_object* v___x_559_; 
v_done_557_ = lean_ctor_get_uint8(v_a_553_, 0);
lean_dec_ref_known(v_a_553_, 0);
if (v_isShared_551_ == 0)
{
v___x_559_ = v___x_550_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_e_x27_548_);
v___x_559_ = v_reuseFailAlloc_563_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_561_; 
lean_ctor_set_uint8(v___x_559_, sizeof(void*)*1, v_done_557_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_559_);
v___x_561_ = v___x_555_;
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
else
{
lean_dec_ref_known(v_a_553_, 1);
lean_del_object(v___x_550_);
lean_dec_ref(v_e_x27_548_);
return v___x_552_;
}
}
else
{
lean_del_object(v___x_550_);
lean_dec_ref(v_e_x27_548_);
return v___x_552_;
}
}
}
else
{
lean_dec_ref_known(v_a_544_, 1);
lean_dec_ref(v___f_529_);
return v___x_543_;
}
}
}
else
{
lean_dec_ref(v___y_531_);
lean_dec_ref(v___f_529_);
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2___boxed(lean_object* v___f_567_, lean_object* v_x_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__2(v___f_567_, v_x_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6(lean_object* v_snd_581_, lean_object* v_a_582_, lean_object* v___x_583_, lean_object* v_____r_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_597_ = lean_array_push(v_snd_581_, v_a_582_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_583_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6___boxed(lean_object* v_snd_601_, lean_object* v_a_602_, lean_object* v___x_603_, lean_object* v_____r_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6(v_snd_601_, v_a_602_, v___x_603_, v_____r_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5(lean_object* v___x_618_, lean_object* v___f_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_box(0);
lean_inc_ref(v___y_620_);
v___x_632_ = l_Lean_Meta_Sym_DSimp_evalGround___redArg(v___x_618_, v___y_620_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
if (lean_obj_tag(v_a_633_) == 0)
{
uint8_t v_done_634_; 
v_done_634_ = lean_ctor_get_uint8(v_a_633_, 0);
lean_dec_ref_known(v_a_633_, 0);
if (v_done_634_ == 0)
{
lean_object* v___x_635_; 
lean_dec_ref_known(v___x_632_, 1);
v___x_635_ = lean_apply_12(v___f_619_, v___x_631_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, lean_box(0));
return v___x_635_;
}
else
{
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec_ref(v___f_619_);
return v___x_632_;
}
}
else
{
uint8_t v_done_636_; 
lean_dec_ref(v___y_620_);
v_done_636_ = lean_ctor_get_uint8(v_a_633_, sizeof(void*)*1);
if (v_done_636_ == 0)
{
lean_object* v_e_x27_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_655_; 
lean_dec_ref_known(v___x_632_, 1);
v_e_x27_637_ = lean_ctor_get(v_a_633_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v_a_633_);
if (v_isSharedCheck_655_ == 0)
{
v___x_639_ = v_a_633_;
v_isShared_640_ = v_isSharedCheck_655_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_e_x27_637_);
lean_dec(v_a_633_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_655_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; 
lean_inc_ref(v_e_x27_637_);
v___x_641_ = lean_apply_12(v___f_619_, v___x_631_, v_e_x27_637_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, lean_box(0));
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
if (lean_obj_tag(v_a_642_) == 0)
{
lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_653_; 
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; 
v_unused_654_ = lean_ctor_get(v___x_641_, 0);
lean_dec(v_unused_654_);
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_653_;
goto v_resetjp_643_;
}
else
{
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_653_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
uint8_t v_done_646_; lean_object* v___x_648_; 
v_done_646_ = lean_ctor_get_uint8(v_a_642_, 0);
lean_dec_ref_known(v_a_642_, 0);
if (v_isShared_640_ == 0)
{
v___x_648_ = v___x_639_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_e_x27_637_);
v___x_648_ = v_reuseFailAlloc_652_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_650_; 
lean_ctor_set_uint8(v___x_648_, sizeof(void*)*1, v_done_646_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v___x_648_);
v___x_650_ = v___x_644_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_642_, 1);
lean_del_object(v___x_639_);
lean_dec_ref(v_e_x27_637_);
return v___x_641_;
}
}
else
{
lean_del_object(v___x_639_);
lean_dec_ref(v_e_x27_637_);
return v___x_641_;
}
}
}
else
{
lean_dec_ref_known(v_a_633_, 1);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___f_619_);
return v___x_632_;
}
}
}
else
{
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec_ref(v___f_619_);
return v___x_632_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5___boxed(lean_object* v___x_656_, lean_object* v___f_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__5(v___x_656_, v___f_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_);
lean_dec(v___x_656_);
return v_res_669_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__10));
v___x_695_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__12));
v___x_696_ = l_Lean_Name_append(v___x_695_, v___x_694_);
return v___x_696_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__15(void){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__14));
v___x_699_ = l_Lean_stringToMessageData(v___x_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg(lean_object* v_upperBound_700_, lean_object* v___x_701_, lean_object* v_config_702_, lean_object* v_a_703_, lean_object* v_b_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v___y_718_; uint8_t v___x_740_; 
v___x_740_ = lean_nat_dec_lt(v_a_703_, v_upperBound_700_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
lean_dec(v_a_703_);
lean_dec_ref(v_config_702_);
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v_b_704_);
return v___x_741_;
}
else
{
lean_object* v_snd_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_818_; 
v_snd_742_ = lean_ctor_get(v_b_704_, 1);
v_isSharedCheck_818_ = !lean_is_exclusive(v_b_704_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; 
v_unused_819_ = lean_ctor_get(v_b_704_, 0);
lean_dec(v_unused_819_);
v___x_744_ = v_b_704_;
v_isShared_745_ = v_isSharedCheck_818_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_snd_742_);
lean_dec(v_b_704_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_818_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
uint8_t v___x_746_; lean_object* v_methods_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_746_ = 1;
v_methods_747_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__6));
v___x_748_ = lean_box(0);
v___x_749_ = lean_array_fget_borrowed(v___x_701_, v_a_703_);
lean_inc(v___x_749_);
lean_inc_ref(v_config_702_);
v___x_750_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v___x_746_, v_methods_747_, v_config_702_, v___x_749_, v___y_706_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v_type_752_; lean_object* v_value_753_; uint8_t v___x_754_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
lean_dec_ref_known(v___x_750_, 1);
v_type_752_ = lean_ctor_get(v_a_751_, 1);
v_value_753_ = lean_ctor_get(v_a_751_, 2);
lean_inc_ref(v_type_752_);
v___x_754_ = l_Lean_Expr_isFalse(v_type_752_);
if (v___x_754_ == 0)
{
lean_object* v_type_755_; lean_object* v___f_756_; uint8_t v___x_785_; 
lean_del_object(v___x_744_);
v_type_755_ = lean_ctor_get(v___x_749_, 1);
lean_inc(v_a_751_);
lean_inc(v_snd_742_);
v___f_756_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6___boxed), 16, 3);
lean_closure_set(v___f_756_, 0, v_snd_742_);
lean_closure_set(v___f_756_, 1, v_a_751_);
lean_closure_set(v___f_756_, 2, v___x_748_);
v___x_785_ = lean_expr_eqv(v_type_755_, v_type_752_);
if (v___x_785_ == 0)
{
lean_inc_ref(v_type_752_);
lean_dec(v_a_751_);
lean_dec(v_snd_742_);
goto v___jp_760_;
}
else
{
if (v___x_754_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; 
lean_dec_ref(v___f_756_);
v___x_786_ = lean_box(0);
v___x_787_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__6(v_snd_742_, v_a_751_, v___x_748_, v___x_786_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
v___y_718_ = v___x_787_;
goto v___jp_717_;
}
else
{
lean_inc_ref(v_type_752_);
lean_dec(v_a_751_);
lean_dec(v_snd_742_);
goto v___jp_760_;
}
}
v___jp_757_:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_box(0);
v___x_759_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7(v___x_740_, v___f_756_, v___x_758_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
v___y_718_ = v___x_759_;
goto v___jp_717_;
}
v___jp_760_:
{
lean_object* v_toCold_761_; lean_object* v_options_762_; uint8_t v_hasTrace_763_; 
v_toCold_761_ = lean_ctor_get(v___y_714_, 0);
v_options_762_ = lean_ctor_get(v_toCold_761_, 2);
v_hasTrace_763_ = lean_ctor_get_uint8(v_options_762_, sizeof(void*)*1);
if (v_hasTrace_763_ == 0)
{
lean_dec_ref(v_type_752_);
goto v___jp_757_;
}
else
{
lean_object* v_inheritedTraceOptions_764_; lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v_inheritedTraceOptions_764_ = lean_ctor_get(v_toCold_761_, 11);
v___x_765_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__10));
v___x_766_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__13);
v___x_767_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_764_, v_options_762_, v___x_766_);
if (v___x_767_ == 0)
{
lean_dec_ref(v_type_752_);
goto v___jp_757_;
}
else
{
lean_object* v_type_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_type_768_ = lean_ctor_get(v___x_749_, 1);
lean_inc_ref(v_type_768_);
v___x_769_ = l_Lean_MessageData_ofExpr(v_type_768_);
v___x_770_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___closed__15);
v___x_771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_769_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = l_Lean_MessageData_ofExpr(v_type_752_);
v___x_773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_771_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(v___x_765_, v___x_773_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_776_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref_known(v___x_774_, 1);
v___x_776_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__1___redArg___lam__7(v___x_740_, v___f_756_, v_a_775_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
v___y_718_ = v___x_776_;
goto v___jp_717_;
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_dec_ref(v___f_756_);
lean_dec(v_a_703_);
lean_dec_ref(v_config_702_);
v_a_777_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_774_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_774_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
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
}
}
}
else
{
lean_object* v___x_788_; 
lean_inc_ref(v_value_753_);
lean_dec(v_a_751_);
lean_dec(v_a_703_);
lean_dec_ref(v_config_702_);
v___x_788_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_753_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
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
v___x_792_ = lean_box(v___x_740_);
v___x_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_793_);
v___x_795_ = v___x_744_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_799_, 1, v_snd_742_);
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
lean_del_object(v___x_744_);
lean_dec(v_snd_742_);
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
lean_del_object(v___x_744_);
lean_dec(v_snd_742_);
lean_dec(v_a_703_);
lean_dec_ref(v_config_702_);
v_a_810_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_750_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_750_);
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
v___jp_717_:
{
if (lean_obj_tag(v___y_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_731_; 
v_a_719_ = lean_ctor_get(v___y_718_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___y_718_);
if (v_isSharedCheck_731_ == 0)
{
v___x_721_ = v___y_718_;
v_isShared_722_ = v_isSharedCheck_731_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___y_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_731_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
if (lean_obj_tag(v_a_719_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_725_; 
lean_dec(v_a_703_);
lean_dec_ref(v_config_702_);
v_a_723_ = lean_ctor_get(v_a_719_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v_a_719_, 1);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v_a_723_);
v___x_725_ = v___x_721_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
lean_del_object(v___x_721_);
v_a_727_ = lean_ctor_get(v_a_719_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v_a_719_, 1);
v___x_728_ = lean_unsigned_to_nat(1u);
v___x_729_ = lean_nat_add(v_a_703_, v___x_728_);
lean_dec(v_a_703_);
v_a_703_ = v___x_729_;
v_b_704_ = v_a_727_;
goto _start;
}
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec(v_a_703_);
lean_dec_ref(v_config_702_);
v_a_732_ = lean_ctor_get(v___y_718_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___y_718_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___y_718_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___y_718_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
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

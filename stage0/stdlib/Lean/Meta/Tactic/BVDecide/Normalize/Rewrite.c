// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.Rewrite
// Imports: public import Lean.Meta.Tactic.BVDecide.Normalize.Basic import Lean.Meta.Tactic.BVDecide.Normalize.Simproc import Lean.Meta.Sym.Simp.Rewrite import Lean.Meta.Sym.Simp.EvalGround import Lean.Meta.Sym.DSimp import Lean.Meta.Sym.Simp.Forall import Lean.Meta.Sym.Simp.ControlFlow
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
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteDsimproc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_evalGround___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpControl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_bvNormalizeExt;
lean_object* l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_evalGround___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "rewriteRules simproc statistics:"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__3___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__0_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__1___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__0_value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__1_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__2___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__1_value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__2_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__3___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__3_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__4___boxed, .m_arity = 13, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__2_value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__4_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__3_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__7_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__8_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__9_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__9_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__9_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__10_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__11_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "  ==>  "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__13_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__14;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__9(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__9___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__10___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___boxed(lean_object**);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_evalGround___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__0_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__1_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__1_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__5;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__6;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "rewriteRules"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__2_value),LEAN_SCALAR_PTR_LITERAL(39, 217, 1, 104, 84, 94, 139, 227)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; 
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc(v___y_4_);
lean_inc(v___y_3_);
lean_inc_ref(v___y_2_);
v___x_14_ = lean_apply_12(v_x_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0___boxed(lean_object* v_x_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0(v_x_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg(lean_object* v_mvarId_29_, lean_object* v_x_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___f_43_; lean_object* v___x_44_; 
lean_inc(v___y_37_);
lean_inc_ref(v___y_36_);
lean_inc(v___y_35_);
lean_inc_ref(v___y_34_);
lean_inc(v___y_33_);
lean_inc(v___y_32_);
lean_inc_ref(v___y_31_);
v___f_43_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_43_, 0, v_x_30_);
lean_closure_set(v___f_43_, 1, v___y_31_);
lean_closure_set(v___f_43_, 2, v___y_32_);
lean_closure_set(v___f_43_, 3, v___y_33_);
lean_closure_set(v___f_43_, 4, v___y_34_);
lean_closure_set(v___f_43_, 5, v___y_35_);
lean_closure_set(v___f_43_, 6, v___y_36_);
lean_closure_set(v___f_43_, 7, v___y_37_);
v___x_44_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_29_, v___f_43_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
if (lean_obj_tag(v___x_44_) == 0)
{
return v___x_44_;
}
else
{
lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_52_; 
v_a_45_ = lean_ctor_get(v___x_44_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_44_);
if (v_isSharedCheck_52_ == 0)
{
v___x_47_ = v___x_44_;
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_44_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_45_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___boxed(lean_object* v_mvarId_53_, lean_object* v_x_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg(v_mvarId_53_, v_x_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2(lean_object* v_00_u03b1_68_, lean_object* v_mvarId_69_, lean_object* v_x_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg(v_mvarId_69_, v_x_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___boxed(lean_object* v_00_u03b1_84_, lean_object* v_mvarId_85_, lean_object* v_x_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2(v_00_u03b1_84_, v_mvarId_85_, v_x_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
return v_res_99_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = lean_unsigned_to_nat(32u);
v___x_101_ = lean_mk_empty_array_with_capacity(v___x_100_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_103_ = ((size_t)5ULL);
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = lean_unsigned_to_nat(32u);
v___x_106_ = lean_mk_empty_array_with_capacity(v___x_105_);
v___x_107_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___closed__0);
v___x_108_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___x_106_);
lean_ctor_set(v___x_108_, 2, v___x_104_);
lean_ctor_set(v___x_108_, 3, v___x_104_);
lean_ctor_set_usize(v___x_108_, 4, v___x_103_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg(lean_object* v___y_109_){
_start:
{
lean_object* v___x_111_; lean_object* v_traceState_112_; lean_object* v_traces_113_; lean_object* v___x_114_; lean_object* v_traceState_115_; lean_object* v_env_116_; lean_object* v_nextMacroScope_117_; lean_object* v_ngen_118_; lean_object* v_auxDeclNGen_119_; lean_object* v_cache_120_; lean_object* v_recordedDeps_121_; lean_object* v_messages_122_; lean_object* v_infoState_123_; lean_object* v_snapshotTasks_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_143_; 
v___x_111_ = lean_st_ref_get(v___y_109_);
v_traceState_112_ = lean_ctor_get(v___x_111_, 4);
lean_inc_ref(v_traceState_112_);
lean_dec(v___x_111_);
v_traces_113_ = lean_ctor_get(v_traceState_112_, 0);
lean_inc_ref(v_traces_113_);
lean_dec_ref(v_traceState_112_);
v___x_114_ = lean_st_ref_take(v___y_109_);
v_traceState_115_ = lean_ctor_get(v___x_114_, 4);
v_env_116_ = lean_ctor_get(v___x_114_, 0);
v_nextMacroScope_117_ = lean_ctor_get(v___x_114_, 1);
v_ngen_118_ = lean_ctor_get(v___x_114_, 2);
v_auxDeclNGen_119_ = lean_ctor_get(v___x_114_, 3);
v_cache_120_ = lean_ctor_get(v___x_114_, 5);
v_recordedDeps_121_ = lean_ctor_get(v___x_114_, 6);
v_messages_122_ = lean_ctor_get(v___x_114_, 7);
v_infoState_123_ = lean_ctor_get(v___x_114_, 8);
v_snapshotTasks_124_ = lean_ctor_get(v___x_114_, 9);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_143_ == 0)
{
v___x_126_ = v___x_114_;
v_isShared_127_ = v_isSharedCheck_143_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_snapshotTasks_124_);
lean_inc(v_infoState_123_);
lean_inc(v_messages_122_);
lean_inc(v_recordedDeps_121_);
lean_inc(v_cache_120_);
lean_inc(v_traceState_115_);
lean_inc(v_auxDeclNGen_119_);
lean_inc(v_ngen_118_);
lean_inc(v_nextMacroScope_117_);
lean_inc(v_env_116_);
lean_dec(v___x_114_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_143_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
uint64_t v_tid_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_141_; 
v_tid_128_ = lean_ctor_get_uint64(v_traceState_115_, sizeof(void*)*1);
v_isSharedCheck_141_ = !lean_is_exclusive(v_traceState_115_);
if (v_isSharedCheck_141_ == 0)
{
lean_object* v_unused_142_; 
v_unused_142_ = lean_ctor_get(v_traceState_115_, 0);
lean_dec(v_unused_142_);
v___x_130_ = v_traceState_115_;
v_isShared_131_ = v_isSharedCheck_141_;
goto v_resetjp_129_;
}
else
{
lean_dec(v_traceState_115_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_141_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_132_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___closed__1);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 0, v___x_132_);
v___x_134_ = v___x_130_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_132_);
lean_ctor_set_uint64(v_reuseFailAlloc_140_, sizeof(void*)*1, v_tid_128_);
v___x_134_ = v_reuseFailAlloc_140_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
lean_object* v___x_136_; 
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 4, v___x_134_);
v___x_136_ = v___x_126_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_env_116_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_nextMacroScope_117_);
lean_ctor_set(v_reuseFailAlloc_139_, 2, v_ngen_118_);
lean_ctor_set(v_reuseFailAlloc_139_, 3, v_auxDeclNGen_119_);
lean_ctor_set(v_reuseFailAlloc_139_, 4, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_139_, 5, v_cache_120_);
lean_ctor_set(v_reuseFailAlloc_139_, 6, v_recordedDeps_121_);
lean_ctor_set(v_reuseFailAlloc_139_, 7, v_messages_122_);
lean_ctor_set(v_reuseFailAlloc_139_, 8, v_infoState_123_);
lean_ctor_set(v_reuseFailAlloc_139_, 9, v_snapshotTasks_124_);
v___x_136_ = v_reuseFailAlloc_139_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_st_ref_put(v___y_109_, v___x_136_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v_traces_113_);
return v___x_138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___boxed(lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg(v___y_144_);
lean_dec(v___y_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4(lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg(v___y_157_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___boxed(lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4(v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
return v_res_172_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5(lean_object* v_opts_173_, lean_object* v_opt_174_){
_start:
{
lean_object* v_name_175_; lean_object* v_defValue_176_; lean_object* v_map_177_; lean_object* v___x_178_; 
v_name_175_ = lean_ctor_get(v_opt_174_, 0);
v_defValue_176_ = lean_ctor_get(v_opt_174_, 1);
v_map_177_ = lean_ctor_get(v_opts_173_, 0);
v___x_178_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_177_, v_name_175_);
if (lean_obj_tag(v___x_178_) == 0)
{
uint8_t v___x_179_; 
v___x_179_ = lean_unbox(v_defValue_176_);
return v___x_179_;
}
else
{
lean_object* v_val_180_; 
v_val_180_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_val_180_);
lean_dec_ref_known(v___x_178_, 1);
if (lean_obj_tag(v_val_180_) == 1)
{
uint8_t v_v_181_; 
v_v_181_ = lean_ctor_get_uint8(v_val_180_, 0);
lean_dec_ref_known(v_val_180_, 0);
return v_v_181_;
}
else
{
uint8_t v___x_182_; 
lean_dec(v_val_180_);
v___x_182_ = lean_unbox(v_defValue_176_);
return v___x_182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___boxed(lean_object* v_opts_183_, lean_object* v_opt_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5(v_opts_183_, v_opt_184_);
lean_dec_ref(v_opt_184_);
lean_dec_ref(v_opts_183_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__2(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__1));
v___x_191_ = l_Lean_MessageData_ofFormat(v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(lean_object* v_x_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__2);
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___boxed(lean_object* v_x_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(v_x_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec_ref(v_x_207_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1(lean_object* v_e_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Meta_Sym_Simp_simpControl(v_e_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_263_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_263_ == 0)
{
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_263_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_263_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
if (lean_obj_tag(v_a_233_) == 0)
{
uint8_t v_contextDependent_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_248_; 
v_contextDependent_237_ = lean_ctor_get_uint8(v_a_233_, 1);
v_isSharedCheck_248_ = !lean_is_exclusive(v_a_233_);
if (v_isSharedCheck_248_ == 0)
{
v___x_239_ = v_a_233_;
v_isShared_240_ = v_isSharedCheck_248_;
goto v_resetjp_238_;
}
else
{
lean_dec(v_a_233_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_248_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
uint8_t v___x_241_; lean_object* v___x_243_; 
v___x_241_ = 0;
if (v_isShared_240_ == 0)
{
v___x_243_ = v___x_239_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_247_, 1, v_contextDependent_237_);
v___x_243_ = v_reuseFailAlloc_247_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_245_; 
lean_ctor_set_uint8(v___x_243_, 0, v___x_241_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_243_);
v___x_245_ = v___x_235_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
else
{
lean_object* v_e_x27_249_; lean_object* v_proof_250_; uint8_t v_contextDependent_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_262_; 
v_e_x27_249_ = lean_ctor_get(v_a_233_, 0);
v_proof_250_ = lean_ctor_get(v_a_233_, 1);
v_contextDependent_251_ = lean_ctor_get_uint8(v_a_233_, sizeof(void*)*2 + 1);
v_isSharedCheck_262_ = !lean_is_exclusive(v_a_233_);
if (v_isSharedCheck_262_ == 0)
{
v___x_253_ = v_a_233_;
v_isShared_254_ = v_isSharedCheck_262_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_proof_250_);
lean_inc(v_e_x27_249_);
lean_dec(v_a_233_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_262_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
uint8_t v___x_255_; lean_object* v___x_257_; 
v___x_255_ = 0;
if (v_isShared_254_ == 0)
{
v___x_257_ = v___x_253_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_e_x27_249_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_proof_250_);
lean_ctor_set_uint8(v_reuseFailAlloc_261_, sizeof(void*)*2 + 1, v_contextDependent_251_);
v___x_257_ = v_reuseFailAlloc_261_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_259_; 
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*2, v___x_255_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_257_);
v___x_259_ = v___x_235_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
}
else
{
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___boxed(lean_object* v_e_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1(v_e_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2(lean_object* v_val_276_, lean_object* v_a_277_, lean_object* v___x_278_, lean_object* v_x_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; 
lean_inc_ref(v___y_280_);
v___x_291_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteSimproc(v_val_276_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_a_292_);
if (lean_obj_tag(v_a_292_) == 0)
{
uint8_t v_done_293_; 
v_done_293_ = lean_ctor_get_uint8(v_a_292_, 0);
if (v_done_293_ == 0)
{
uint8_t v_contextDependent_294_; lean_object* v___x_295_; 
lean_dec_ref_known(v___x_291_, 1);
v_contextDependent_294_ = lean_ctor_get_uint8(v_a_292_, 1);
lean_dec_ref_known(v_a_292_, 0);
v___x_295_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_277_, v___x_278_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v_a_296_; uint8_t v___y_298_; 
v_a_296_ = lean_ctor_get(v___x_295_, 0);
if (v_contextDependent_294_ == 0)
{
return v___x_295_;
}
else
{
if (lean_obj_tag(v_a_296_) == 0)
{
uint8_t v_contextDependent_308_; 
v_contextDependent_308_ = lean_ctor_get_uint8(v_a_296_, 1);
v___y_298_ = v_contextDependent_308_;
goto v___jp_297_;
}
else
{
uint8_t v_contextDependent_309_; 
v_contextDependent_309_ = lean_ctor_get_uint8(v_a_296_, sizeof(void*)*2 + 1);
v___y_298_ = v_contextDependent_309_;
goto v___jp_297_;
}
}
v___jp_297_:
{
if (v___y_298_ == 0)
{
lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_306_; 
lean_inc(v_a_296_);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_295_);
if (v_isSharedCheck_306_ == 0)
{
lean_object* v_unused_307_; 
v_unused_307_ = lean_ctor_get(v___x_295_, 0);
lean_dec(v_unused_307_);
v___x_300_ = v___x_295_;
v_isShared_301_ = v_isSharedCheck_306_;
goto v_resetjp_299_;
}
else
{
lean_dec(v___x_295_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_306_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_302_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_296_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v___x_302_);
v___x_304_ = v___x_300_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
else
{
return v___x_295_;
}
}
}
else
{
return v___x_295_;
}
}
else
{
lean_dec_ref_known(v_a_292_, 0);
lean_dec_ref(v___y_280_);
lean_dec_ref(v___x_278_);
return v___x_291_;
}
}
else
{
uint8_t v_done_310_; 
v_done_310_ = lean_ctor_get_uint8(v_a_292_, sizeof(void*)*2);
if (v_done_310_ == 0)
{
lean_object* v_e_x27_311_; lean_object* v_proof_312_; uint8_t v_contextDependent_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_363_; 
lean_dec_ref_known(v___x_291_, 1);
v_e_x27_311_ = lean_ctor_get(v_a_292_, 0);
v_proof_312_ = lean_ctor_get(v_a_292_, 1);
v_contextDependent_313_ = lean_ctor_get_uint8(v_a_292_, sizeof(void*)*2 + 1);
v_isSharedCheck_363_ = !lean_is_exclusive(v_a_292_);
if (v_isSharedCheck_363_ == 0)
{
v___x_315_ = v_a_292_;
v_isShared_316_ = v_isSharedCheck_363_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_proof_312_);
lean_inc(v_e_x27_311_);
lean_dec(v_a_292_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_363_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; 
lean_inc_ref(v_e_x27_311_);
v___x_317_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_277_, v___x_278_, v_e_x27_311_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_362_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_362_ == 0)
{
v___x_320_ = v___x_317_;
v_isShared_321_ = v_isSharedCheck_362_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_362_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
if (lean_obj_tag(v_a_318_) == 0)
{
uint8_t v_done_322_; uint8_t v_contextDependent_323_; uint8_t v___y_325_; 
lean_dec_ref(v___y_280_);
v_done_322_ = lean_ctor_get_uint8(v_a_318_, 0);
v_contextDependent_323_ = lean_ctor_get_uint8(v_a_318_, 1);
lean_dec_ref_known(v_a_318_, 0);
if (v_contextDependent_313_ == 0)
{
v___y_325_ = v_contextDependent_323_;
goto v___jp_324_;
}
else
{
v___y_325_ = v_contextDependent_313_;
goto v___jp_324_;
}
v___jp_324_:
{
lean_object* v___x_327_; 
if (v_isShared_316_ == 0)
{
v___x_327_ = v___x_315_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_e_x27_311_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_proof_312_);
v___x_327_ = v_reuseFailAlloc_331_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_329_; 
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*2, v_done_322_);
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*2 + 1, v___y_325_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v___x_327_);
v___x_329_ = v___x_320_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
else
{
lean_object* v_e_x27_332_; lean_object* v_proof_333_; uint8_t v_done_334_; uint8_t v_contextDependent_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_361_; 
lean_del_object(v___x_320_);
lean_del_object(v___x_315_);
v_e_x27_332_ = lean_ctor_get(v_a_318_, 0);
v_proof_333_ = lean_ctor_get(v_a_318_, 1);
v_done_334_ = lean_ctor_get_uint8(v_a_318_, sizeof(void*)*2);
v_contextDependent_335_ = lean_ctor_get_uint8(v_a_318_, sizeof(void*)*2 + 1);
v_isSharedCheck_361_ = !lean_is_exclusive(v_a_318_);
if (v_isSharedCheck_361_ == 0)
{
v___x_337_ = v_a_318_;
v_isShared_338_ = v_isSharedCheck_361_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_proof_333_);
lean_inc(v_e_x27_332_);
lean_dec(v_a_318_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_361_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_339_; 
lean_inc_ref(v_e_x27_332_);
v___x_339_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_280_, v_e_x27_311_, v_proof_312_, v_e_x27_332_, v_proof_333_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_352_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_352_ == 0)
{
v___x_342_ = v___x_339_;
v_isShared_343_ = v_isSharedCheck_352_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_352_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
uint8_t v___y_345_; 
if (v_contextDependent_313_ == 0)
{
v___y_345_ = v_contextDependent_335_;
goto v___jp_344_;
}
else
{
v___y_345_ = v_contextDependent_313_;
goto v___jp_344_;
}
v___jp_344_:
{
lean_object* v___x_347_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 1, v_a_340_);
v___x_347_ = v___x_337_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_e_x27_332_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_a_340_);
lean_ctor_set_uint8(v_reuseFailAlloc_351_, sizeof(void*)*2, v_done_334_);
v___x_347_ = v_reuseFailAlloc_351_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_object* v___x_349_; 
lean_ctor_set_uint8(v___x_347_, sizeof(void*)*2 + 1, v___y_345_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v___x_347_);
v___x_349_ = v___x_342_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
lean_del_object(v___x_337_);
lean_dec_ref(v_e_x27_332_);
v_a_353_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_339_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_339_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_315_);
lean_dec_ref(v_proof_312_);
lean_dec_ref(v_e_x27_311_);
lean_dec_ref(v___y_280_);
return v___x_317_;
}
}
}
else
{
lean_dec_ref_known(v_a_292_, 2);
lean_dec_ref(v___y_280_);
lean_dec_ref(v___x_278_);
return v___x_291_;
}
}
}
else
{
lean_dec_ref(v___y_280_);
lean_dec_ref(v___x_278_);
return v___x_291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2___boxed(lean_object* v_val_364_, lean_object* v_a_365_, lean_object* v___x_366_, lean_object* v_x_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2(v_val_364_, v_a_365_, v___x_366_, v_x_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v_a_365_);
lean_dec(v_val_364_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3(lean_object* v___x_380_, lean_object* v___f_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_box(0);
lean_inc_ref(v___y_382_);
v___x_394_ = l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(v___y_382_, v___x_380_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_395_);
if (lean_obj_tag(v_a_395_) == 0)
{
uint8_t v_done_396_; 
v_done_396_ = lean_ctor_get_uint8(v_a_395_, 0);
if (v_done_396_ == 0)
{
uint8_t v_contextDependent_397_; lean_object* v___x_398_; 
lean_dec_ref_known(v___x_394_, 1);
v_contextDependent_397_ = lean_ctor_get_uint8(v_a_395_, 1);
lean_dec_ref_known(v_a_395_, 0);
v___x_398_ = lean_apply_12(v___f_381_, v___x_393_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, lean_box(0));
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; uint8_t v___y_401_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
if (v_contextDependent_397_ == 0)
{
lean_dec(v_a_399_);
return v___x_398_;
}
else
{
if (lean_obj_tag(v_a_399_) == 0)
{
uint8_t v_contextDependent_411_; 
v_contextDependent_411_ = lean_ctor_get_uint8(v_a_399_, 1);
v___y_401_ = v_contextDependent_411_;
goto v___jp_400_;
}
else
{
uint8_t v_contextDependent_412_; 
v_contextDependent_412_ = lean_ctor_get_uint8(v_a_399_, sizeof(void*)*2 + 1);
v___y_401_ = v_contextDependent_412_;
goto v___jp_400_;
}
}
v___jp_400_:
{
if (v___y_401_ == 0)
{
lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_409_; 
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; 
v_unused_410_ = lean_ctor_get(v___x_398_, 0);
lean_dec(v_unused_410_);
v___x_403_ = v___x_398_;
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
else
{
lean_dec(v___x_398_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_399_);
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v___x_405_);
v___x_407_ = v___x_403_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
else
{
lean_dec(v_a_399_);
return v___x_398_;
}
}
}
else
{
return v___x_398_;
}
}
else
{
lean_dec_ref_known(v_a_395_, 0);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec_ref(v___f_381_);
return v___x_394_;
}
}
else
{
uint8_t v_done_413_; 
v_done_413_ = lean_ctor_get_uint8(v_a_395_, sizeof(void*)*2);
if (v_done_413_ == 0)
{
lean_object* v_e_x27_414_; lean_object* v_proof_415_; uint8_t v_contextDependent_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_466_; 
lean_dec_ref_known(v___x_394_, 1);
v_e_x27_414_ = lean_ctor_get(v_a_395_, 0);
v_proof_415_ = lean_ctor_get(v_a_395_, 1);
v_contextDependent_416_ = lean_ctor_get_uint8(v_a_395_, sizeof(void*)*2 + 1);
v_isSharedCheck_466_ = !lean_is_exclusive(v_a_395_);
if (v_isSharedCheck_466_ == 0)
{
v___x_418_ = v_a_395_;
v_isShared_419_ = v_isSharedCheck_466_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_proof_415_);
lean_inc(v_e_x27_414_);
lean_dec(v_a_395_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_466_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; 
lean_inc(v___y_391_);
lean_inc_ref(v___y_390_);
lean_inc(v___y_389_);
lean_inc_ref(v___y_388_);
lean_inc(v___y_387_);
lean_inc_ref(v___y_386_);
lean_inc_ref(v_e_x27_414_);
v___x_420_ = lean_apply_12(v___f_381_, v___x_393_, v_e_x27_414_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, lean_box(0));
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_465_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_465_ == 0)
{
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_465_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_465_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
if (lean_obj_tag(v_a_421_) == 0)
{
uint8_t v_done_425_; uint8_t v_contextDependent_426_; uint8_t v___y_428_; 
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec_ref(v___y_382_);
v_done_425_ = lean_ctor_get_uint8(v_a_421_, 0);
v_contextDependent_426_ = lean_ctor_get_uint8(v_a_421_, 1);
lean_dec_ref_known(v_a_421_, 0);
if (v_contextDependent_416_ == 0)
{
v___y_428_ = v_contextDependent_426_;
goto v___jp_427_;
}
else
{
v___y_428_ = v_contextDependent_416_;
goto v___jp_427_;
}
v___jp_427_:
{
lean_object* v___x_430_; 
if (v_isShared_419_ == 0)
{
v___x_430_ = v___x_418_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_e_x27_414_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_proof_415_);
v___x_430_ = v_reuseFailAlloc_434_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v___x_432_; 
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*2, v_done_425_);
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*2 + 1, v___y_428_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_430_);
v___x_432_ = v___x_423_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
else
{
lean_object* v_e_x27_435_; lean_object* v_proof_436_; uint8_t v_done_437_; uint8_t v_contextDependent_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_464_; 
lean_del_object(v___x_423_);
lean_del_object(v___x_418_);
v_e_x27_435_ = lean_ctor_get(v_a_421_, 0);
v_proof_436_ = lean_ctor_get(v_a_421_, 1);
v_done_437_ = lean_ctor_get_uint8(v_a_421_, sizeof(void*)*2);
v_contextDependent_438_ = lean_ctor_get_uint8(v_a_421_, sizeof(void*)*2 + 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v_a_421_);
if (v_isSharedCheck_464_ == 0)
{
v___x_440_ = v_a_421_;
v_isShared_441_ = v_isSharedCheck_464_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_proof_436_);
lean_inc(v_e_x27_435_);
lean_dec(v_a_421_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_464_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; 
lean_inc_ref(v_e_x27_435_);
v___x_442_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_382_, v_e_x27_414_, v_proof_415_, v_e_x27_435_, v_proof_436_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_455_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_455_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_455_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_455_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
uint8_t v___y_448_; 
if (v_contextDependent_416_ == 0)
{
v___y_448_ = v_contextDependent_438_;
goto v___jp_447_;
}
else
{
v___y_448_ = v_contextDependent_416_;
goto v___jp_447_;
}
v___jp_447_:
{
lean_object* v___x_450_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v_a_443_);
v___x_450_ = v___x_440_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_e_x27_435_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_a_443_);
lean_ctor_set_uint8(v_reuseFailAlloc_454_, sizeof(void*)*2, v_done_437_);
v___x_450_ = v_reuseFailAlloc_454_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_452_; 
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*2 + 1, v___y_448_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_450_);
v___x_452_ = v___x_445_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
lean_del_object(v___x_440_);
lean_dec_ref(v_e_x27_435_);
v_a_456_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_442_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_442_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_418_);
lean_dec_ref(v_proof_415_);
lean_dec_ref(v_e_x27_414_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec_ref(v___y_382_);
return v___x_420_;
}
}
}
else
{
lean_dec_ref_known(v_a_395_, 2);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec_ref(v___f_381_);
return v___x_394_;
}
}
}
else
{
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec_ref(v___f_381_);
return v___x_394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3___boxed(lean_object* v___x_467_, lean_object* v___f_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3(v___x_467_, v___f_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
lean_dec_ref(v___x_467_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__5(lean_object* v_snd_481_, lean_object* v_a_482_, lean_object* v___x_483_, lean_object* v_____r_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_497_ = lean_array_push(v_snd_481_, v_a_482_);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_483_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__5___boxed(lean_object* v_snd_501_, lean_object* v_a_502_, lean_object* v___x_503_, lean_object* v_____r_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__5(v_snd_501_, v_a_502_, v___x_503_, v_____r_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__6(uint8_t v___x_518_, lean_object* v___f_519_, lean_object* v_____r_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v___x_533_; lean_object* v_caches_534_; lean_object* v_typeAnalysis_535_; lean_object* v_target_536_; lean_object* v_hypotheses_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_547_; 
v___x_533_ = lean_st_ref_take(v___y_522_);
v_caches_534_ = lean_ctor_get(v___x_533_, 0);
v_typeAnalysis_535_ = lean_ctor_get(v___x_533_, 1);
v_target_536_ = lean_ctor_get(v___x_533_, 2);
v_hypotheses_537_ = lean_ctor_get(v___x_533_, 3);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_547_ == 0)
{
v___x_539_ = v___x_533_;
v_isShared_540_ = v_isSharedCheck_547_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_hypotheses_537_);
lean_inc(v_target_536_);
lean_inc(v_typeAnalysis_535_);
lean_inc(v_caches_534_);
lean_dec(v___x_533_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_547_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = lean_box(0);
if (v_isShared_540_ == 0)
{
v___x_543_ = v___x_539_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_caches_534_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_typeAnalysis_535_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_target_536_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v_hypotheses_537_);
v___x_543_ = v_reuseFailAlloc_546_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_ctor_set_uint8(v___x_543_, sizeof(void*)*4, v___x_518_);
v___x_544_ = lean_st_ref_put(v___y_522_, v___x_543_);
lean_inc(v___y_531_);
lean_inc_ref(v___y_530_);
lean_inc(v___y_529_);
lean_inc_ref(v___y_528_);
lean_inc(v___y_527_);
lean_inc_ref(v___y_526_);
lean_inc(v___y_525_);
lean_inc_ref(v___y_524_);
lean_inc(v___y_523_);
lean_inc(v___y_522_);
lean_inc_ref(v___y_521_);
v___x_545_ = lean_apply_13(v___f_519_, v___x_541_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, lean_box(0));
return v___x_545_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__6___boxed(lean_object* v___x_548_, lean_object* v___f_549_, lean_object* v_____r_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
uint8_t v___x_195598__boxed_563_; lean_object* v_res_564_; 
v___x_195598__boxed_563_ = lean_unbox(v___x_548_);
v_res_564_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__6(v___x_195598__boxed_563_, v___f_549_, v_____r_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(lean_object* v_msgData_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_571_; lean_object* v_env_572_; uint8_t v___x_573_; lean_object* v_env_574_; lean_object* v___x_575_; lean_object* v_toCold_576_; lean_object* v_mctx_577_; lean_object* v_lctx_578_; lean_object* v_options_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_571_ = lean_st_ref_get(v___y_569_);
v_env_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc_ref(v_env_572_);
lean_dec(v___x_571_);
v___x_573_ = 0;
v_env_574_ = l_Lean_Environment_setRecordingDeps(v_env_572_, v___x_573_);
v___x_575_ = lean_st_ref_get(v___y_567_);
v_toCold_576_ = lean_ctor_get(v___y_568_, 0);
v_mctx_577_ = lean_ctor_get(v___x_575_, 0);
lean_inc_ref(v_mctx_577_);
lean_dec(v___x_575_);
v_lctx_578_ = lean_ctor_get(v___y_566_, 2);
v_options_579_ = lean_ctor_get(v_toCold_576_, 2);
lean_inc_ref(v_options_579_);
lean_inc_ref(v_lctx_578_);
v___x_580_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_580_, 0, v_env_574_);
lean_ctor_set(v___x_580_, 1, v_mctx_577_);
lean_ctor_set(v___x_580_, 2, v_lctx_578_);
lean_ctor_set(v___x_580_, 3, v_options_579_);
v___x_581_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v_msgData_565_);
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0___boxed(lean_object* v_msgData_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(v_msgData_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
return v_res_589_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_590_; double v___x_591_; 
v___x_590_ = lean_unsigned_to_nat(0u);
v___x_591_ = lean_float_of_nat(v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(lean_object* v_cls_595_, lean_object* v_msg_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_ref_602_; lean_object* v___x_603_; lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_649_; 
v_ref_602_ = lean_ctor_get(v___y_599_, 2);
v___x_603_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(v_msg_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
v_a_604_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_649_ == 0)
{
v___x_606_ = v___x_603_;
v_isShared_607_ = v_isSharedCheck_649_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_603_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_649_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v_traceState_609_; lean_object* v_env_610_; lean_object* v_nextMacroScope_611_; lean_object* v_ngen_612_; lean_object* v_auxDeclNGen_613_; lean_object* v_cache_614_; lean_object* v_recordedDeps_615_; lean_object* v_messages_616_; lean_object* v_infoState_617_; lean_object* v_snapshotTasks_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_648_; 
v___x_608_ = lean_st_ref_take(v___y_600_);
v_traceState_609_ = lean_ctor_get(v___x_608_, 4);
v_env_610_ = lean_ctor_get(v___x_608_, 0);
v_nextMacroScope_611_ = lean_ctor_get(v___x_608_, 1);
v_ngen_612_ = lean_ctor_get(v___x_608_, 2);
v_auxDeclNGen_613_ = lean_ctor_get(v___x_608_, 3);
v_cache_614_ = lean_ctor_get(v___x_608_, 5);
v_recordedDeps_615_ = lean_ctor_get(v___x_608_, 6);
v_messages_616_ = lean_ctor_get(v___x_608_, 7);
v_infoState_617_ = lean_ctor_get(v___x_608_, 8);
v_snapshotTasks_618_ = lean_ctor_get(v___x_608_, 9);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_648_ == 0)
{
v___x_620_ = v___x_608_;
v_isShared_621_ = v_isSharedCheck_648_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_snapshotTasks_618_);
lean_inc(v_infoState_617_);
lean_inc(v_messages_616_);
lean_inc(v_recordedDeps_615_);
lean_inc(v_cache_614_);
lean_inc(v_traceState_609_);
lean_inc(v_auxDeclNGen_613_);
lean_inc(v_ngen_612_);
lean_inc(v_nextMacroScope_611_);
lean_inc(v_env_610_);
lean_dec(v___x_608_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_648_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
uint64_t v_tid_622_; lean_object* v_traces_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_647_; 
v_tid_622_ = lean_ctor_get_uint64(v_traceState_609_, sizeof(void*)*1);
v_traces_623_ = lean_ctor_get(v_traceState_609_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v_traceState_609_);
if (v_isSharedCheck_647_ == 0)
{
v___x_625_ = v_traceState_609_;
v_isShared_626_ = v_isSharedCheck_647_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_traces_623_);
lean_dec(v_traceState_609_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_647_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_628_; double v___x_629_; uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_627_ = lean_box(0);
v___x_628_ = lean_box(0);
v___x_629_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0);
v___x_630_ = 0;
v___x_631_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1));
v___x_632_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_632_, 0, v_cls_595_);
lean_ctor_set(v___x_632_, 1, v___x_628_);
lean_ctor_set(v___x_632_, 2, v___x_631_);
lean_ctor_set_float(v___x_632_, sizeof(void*)*3, v___x_629_);
lean_ctor_set_float(v___x_632_, sizeof(void*)*3 + 8, v___x_629_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*3 + 16, v___x_630_);
v___x_633_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__2));
v___x_634_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v_a_604_);
lean_ctor_set(v___x_634_, 2, v___x_633_);
lean_inc(v_ref_602_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v_ref_602_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = l_Lean_PersistentArray_push___redArg(v_traces_623_, v___x_635_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v___x_636_);
v___x_638_ = v___x_625_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_636_);
lean_ctor_set_uint64(v_reuseFailAlloc_646_, sizeof(void*)*1, v_tid_622_);
v___x_638_ = v_reuseFailAlloc_646_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_640_; 
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 4, v___x_638_);
v___x_640_ = v___x_620_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_env_610_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_nextMacroScope_611_);
lean_ctor_set(v_reuseFailAlloc_645_, 2, v_ngen_612_);
lean_ctor_set(v_reuseFailAlloc_645_, 3, v_auxDeclNGen_613_);
lean_ctor_set(v_reuseFailAlloc_645_, 4, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_645_, 5, v_cache_614_);
lean_ctor_set(v_reuseFailAlloc_645_, 6, v_recordedDeps_615_);
lean_ctor_set(v_reuseFailAlloc_645_, 7, v_messages_616_);
lean_ctor_set(v_reuseFailAlloc_645_, 8, v_infoState_617_);
lean_ctor_set(v_reuseFailAlloc_645_, 9, v_snapshotTasks_618_);
v___x_640_ = v_reuseFailAlloc_645_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_641_ = lean_st_ref_put(v___y_600_, v___x_640_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_627_);
v___x_643_ = v___x_606_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_627_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___boxed(lean_object* v_cls_650_, lean_object* v_msg_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v_cls_650_, v_msg_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__4(lean_object* v___x_658_, lean_object* v___f_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_box(0);
lean_inc_ref(v___y_660_);
v___x_672_ = l_Lean_Meta_Sym_DSimp_evalGround___redArg(v___x_658_, v___y_660_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
if (lean_obj_tag(v_a_673_) == 0)
{
uint8_t v_done_674_; 
v_done_674_ = lean_ctor_get_uint8(v_a_673_, 0);
lean_dec_ref_known(v_a_673_, 0);
if (v_done_674_ == 0)
{
lean_object* v___x_675_; 
lean_dec_ref_known(v___x_672_, 1);
v___x_675_ = lean_apply_12(v___f_659_, v___x_671_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, lean_box(0));
return v___x_675_;
}
else
{
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec_ref(v___f_659_);
return v___x_672_;
}
}
else
{
uint8_t v_done_676_; 
lean_dec_ref(v___y_660_);
v_done_676_ = lean_ctor_get_uint8(v_a_673_, sizeof(void*)*1);
if (v_done_676_ == 0)
{
lean_object* v_e_x27_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_695_; 
lean_dec_ref_known(v___x_672_, 1);
v_e_x27_677_ = lean_ctor_get(v_a_673_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v_a_673_);
if (v_isSharedCheck_695_ == 0)
{
v___x_679_ = v_a_673_;
v_isShared_680_ = v_isSharedCheck_695_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_e_x27_677_);
lean_dec(v_a_673_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_695_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_681_; 
lean_inc_ref(v_e_x27_677_);
v___x_681_ = lean_apply_12(v___f_659_, v___x_671_, v_e_x27_677_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, lean_box(0));
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
if (lean_obj_tag(v_a_682_) == 0)
{
lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_693_; 
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_693_ == 0)
{
lean_object* v_unused_694_; 
v_unused_694_ = lean_ctor_get(v___x_681_, 0);
lean_dec(v_unused_694_);
v___x_684_ = v___x_681_;
v_isShared_685_ = v_isSharedCheck_693_;
goto v_resetjp_683_;
}
else
{
lean_dec(v___x_681_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_693_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
uint8_t v_done_686_; lean_object* v___x_688_; 
v_done_686_ = lean_ctor_get_uint8(v_a_682_, 0);
lean_dec_ref_known(v_a_682_, 0);
if (v_isShared_680_ == 0)
{
v___x_688_ = v___x_679_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_e_x27_677_);
v___x_688_ = v_reuseFailAlloc_692_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_690_; 
lean_ctor_set_uint8(v___x_688_, sizeof(void*)*1, v_done_686_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_688_);
v___x_690_ = v___x_684_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_682_, 1);
lean_del_object(v___x_679_);
lean_dec_ref(v_e_x27_677_);
return v___x_681_;
}
}
else
{
lean_del_object(v___x_679_);
lean_dec_ref(v_e_x27_677_);
return v___x_681_;
}
}
}
else
{
lean_dec_ref_known(v_a_673_, 1);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___f_659_);
return v___x_672_;
}
}
}
else
{
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec_ref(v___f_659_);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__4___boxed(lean_object* v___x_696_, lean_object* v___f_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__4(v___x_696_, v___f_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___x_696_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__3(lean_object* v_x_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__3___closed__0));
v___x_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__3___boxed(lean_object* v_x_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__3(v_x_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v_x_725_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__2(lean_object* v___f_737_, lean_object* v_x_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_box(0);
lean_inc_ref(v___y_739_);
v___x_751_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v___y_739_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
if (lean_obj_tag(v_a_752_) == 0)
{
uint8_t v_done_753_; 
v_done_753_ = lean_ctor_get_uint8(v_a_752_, 0);
lean_dec_ref_known(v_a_752_, 0);
if (v_done_753_ == 0)
{
lean_object* v___x_754_; 
lean_dec_ref_known(v___x_751_, 1);
lean_inc(v___y_748_);
lean_inc_ref(v___y_747_);
lean_inc(v___y_746_);
lean_inc_ref(v___y_745_);
lean_inc(v___y_744_);
lean_inc_ref(v___y_743_);
lean_inc(v___y_742_);
lean_inc_ref(v___y_741_);
lean_inc(v___y_740_);
v___x_754_ = lean_apply_12(v___f_737_, v___x_750_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, lean_box(0));
return v___x_754_;
}
else
{
lean_dec_ref(v___y_739_);
lean_dec_ref(v___f_737_);
return v___x_751_;
}
}
else
{
uint8_t v_done_755_; 
lean_dec_ref(v___y_739_);
v_done_755_ = lean_ctor_get_uint8(v_a_752_, sizeof(void*)*1);
if (v_done_755_ == 0)
{
lean_object* v_e_x27_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_774_; 
lean_dec_ref_known(v___x_751_, 1);
v_e_x27_756_ = lean_ctor_get(v_a_752_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v_a_752_);
if (v_isSharedCheck_774_ == 0)
{
v___x_758_ = v_a_752_;
v_isShared_759_ = v_isSharedCheck_774_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_e_x27_756_);
lean_dec(v_a_752_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_774_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; 
lean_inc(v___y_748_);
lean_inc_ref(v___y_747_);
lean_inc(v___y_746_);
lean_inc_ref(v___y_745_);
lean_inc(v___y_744_);
lean_inc_ref(v___y_743_);
lean_inc(v___y_742_);
lean_inc_ref(v___y_741_);
lean_inc(v___y_740_);
lean_inc_ref(v_e_x27_756_);
v___x_760_ = lean_apply_12(v___f_737_, v___x_750_, v_e_x27_756_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, lean_box(0));
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; 
v_a_761_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_a_761_);
if (lean_obj_tag(v_a_761_) == 0)
{
lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_772_; 
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; 
v_unused_773_ = lean_ctor_get(v___x_760_, 0);
lean_dec(v_unused_773_);
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_772_;
goto v_resetjp_762_;
}
else
{
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_772_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
uint8_t v_done_765_; lean_object* v___x_767_; 
v_done_765_ = lean_ctor_get_uint8(v_a_761_, 0);
lean_dec_ref_known(v_a_761_, 0);
if (v_isShared_759_ == 0)
{
v___x_767_ = v___x_758_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_e_x27_756_);
v___x_767_ = v_reuseFailAlloc_771_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
lean_ctor_set_uint8(v___x_767_, sizeof(void*)*1, v_done_765_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v___x_767_);
v___x_769_ = v___x_763_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_767_);
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
lean_dec_ref_known(v_a_761_, 1);
lean_del_object(v___x_758_);
lean_dec_ref(v_e_x27_756_);
return v___x_760_;
}
}
else
{
lean_del_object(v___x_758_);
lean_dec_ref(v_e_x27_756_);
return v___x_760_;
}
}
}
else
{
lean_dec_ref_known(v_a_752_, 1);
lean_dec_ref(v___f_737_);
return v___x_751_;
}
}
}
else
{
lean_dec_ref(v___y_739_);
lean_dec_ref(v___f_737_);
return v___x_751_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__2___boxed(lean_object* v___f_775_, lean_object* v_x_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__2(v___f_775_, v_x_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__1(lean_object* v___f_789_, lean_object* v_x_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_box(0);
lean_inc_ref(v___y_791_);
v___x_803_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_791_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
if (lean_obj_tag(v_a_804_) == 0)
{
uint8_t v_done_805_; 
v_done_805_ = lean_ctor_get_uint8(v_a_804_, 0);
lean_dec_ref_known(v_a_804_, 0);
if (v_done_805_ == 0)
{
lean_object* v___x_806_; 
lean_dec_ref_known(v___x_803_, 1);
lean_inc(v___y_800_);
lean_inc_ref(v___y_799_);
lean_inc(v___y_798_);
lean_inc_ref(v___y_797_);
lean_inc(v___y_796_);
lean_inc_ref(v___y_795_);
lean_inc(v___y_794_);
lean_inc_ref(v___y_793_);
lean_inc(v___y_792_);
v___x_806_ = lean_apply_12(v___f_789_, v___x_802_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, lean_box(0));
return v___x_806_;
}
else
{
lean_dec_ref(v___y_791_);
lean_dec_ref(v___f_789_);
return v___x_803_;
}
}
else
{
uint8_t v_done_807_; 
lean_dec_ref(v___y_791_);
v_done_807_ = lean_ctor_get_uint8(v_a_804_, sizeof(void*)*1);
if (v_done_807_ == 0)
{
lean_object* v_e_x27_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref_known(v___x_803_, 1);
v_e_x27_808_ = lean_ctor_get(v_a_804_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v_a_804_);
if (v_isSharedCheck_826_ == 0)
{
v___x_810_ = v_a_804_;
v_isShared_811_ = v_isSharedCheck_826_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_e_x27_808_);
lean_dec(v_a_804_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_826_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_812_; 
lean_inc(v___y_800_);
lean_inc_ref(v___y_799_);
lean_inc(v___y_798_);
lean_inc_ref(v___y_797_);
lean_inc(v___y_796_);
lean_inc_ref(v___y_795_);
lean_inc(v___y_794_);
lean_inc_ref(v___y_793_);
lean_inc(v___y_792_);
lean_inc_ref(v_e_x27_808_);
v___x_812_ = lean_apply_12(v___f_789_, v___x_802_, v_e_x27_808_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, lean_box(0));
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
if (lean_obj_tag(v_a_813_) == 0)
{
lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_824_; 
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v___x_812_, 0);
lean_dec(v_unused_825_);
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_824_;
goto v_resetjp_814_;
}
else
{
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_824_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
uint8_t v_done_817_; lean_object* v___x_819_; 
v_done_817_ = lean_ctor_get_uint8(v_a_813_, 0);
lean_dec_ref_known(v_a_813_, 0);
if (v_isShared_811_ == 0)
{
v___x_819_ = v___x_810_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_e_x27_808_);
v___x_819_ = v_reuseFailAlloc_823_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_821_; 
lean_ctor_set_uint8(v___x_819_, sizeof(void*)*1, v_done_817_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_819_);
v___x_821_ = v___x_815_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_813_, 1);
lean_del_object(v___x_810_);
lean_dec_ref(v_e_x27_808_);
return v___x_812_;
}
}
else
{
lean_del_object(v___x_810_);
lean_dec_ref(v_e_x27_808_);
return v___x_812_;
}
}
}
else
{
lean_dec_ref_known(v_a_804_, 1);
lean_dec_ref(v___f_789_);
return v___x_803_;
}
}
}
else
{
lean_dec_ref(v___y_791_);
lean_dec_ref(v___f_789_);
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__1___boxed(lean_object* v___f_827_, lean_object* v_x_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__1(v___f_827_, v_x_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__0(lean_object* v_x_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v___x_853_; 
lean_inc_ref(v___y_842_);
v___x_853_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_842_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
if (lean_obj_tag(v_a_854_) == 0)
{
uint8_t v_done_855_; 
v_done_855_ = lean_ctor_get_uint8(v_a_854_, 0);
lean_dec_ref_known(v_a_854_, 0);
if (v_done_855_ == 0)
{
lean_object* v___x_856_; 
lean_dec_ref_known(v___x_853_, 1);
v___x_856_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteDsimproc___redArg(v___y_842_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
return v___x_856_;
}
else
{
lean_dec_ref(v___y_842_);
return v___x_853_;
}
}
else
{
uint8_t v_done_857_; 
lean_dec_ref(v___y_842_);
v_done_857_ = lean_ctor_get_uint8(v_a_854_, sizeof(void*)*1);
if (v_done_857_ == 0)
{
lean_object* v_e_x27_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_876_; 
lean_dec_ref_known(v___x_853_, 1);
v_e_x27_858_ = lean_ctor_get(v_a_854_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v_a_854_);
if (v_isSharedCheck_876_ == 0)
{
v___x_860_ = v_a_854_;
v_isShared_861_ = v_isSharedCheck_876_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_e_x27_858_);
lean_dec(v_a_854_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_876_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_862_; 
lean_inc_ref(v_e_x27_858_);
v___x_862_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteDsimproc___redArg(v_e_x27_858_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
if (lean_obj_tag(v_a_863_) == 0)
{
lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_874_; 
lean_inc_ref(v_a_863_);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; 
v_unused_875_ = lean_ctor_get(v___x_862_, 0);
lean_dec(v_unused_875_);
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_874_;
goto v_resetjp_864_;
}
else
{
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_874_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
uint8_t v_done_867_; lean_object* v___x_869_; 
v_done_867_ = lean_ctor_get_uint8(v_a_863_, 0);
lean_dec_ref_known(v_a_863_, 0);
if (v_isShared_861_ == 0)
{
v___x_869_ = v___x_860_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_e_x27_858_);
v___x_869_ = v_reuseFailAlloc_873_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_871_; 
lean_ctor_set_uint8(v___x_869_, sizeof(void*)*1, v_done_867_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_869_);
v___x_871_ = v___x_865_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
else
{
lean_del_object(v___x_860_);
lean_dec_ref(v_e_x27_858_);
return v___x_862_;
}
}
else
{
lean_del_object(v___x_860_);
lean_dec_ref(v_e_x27_858_);
return v___x_862_;
}
}
}
else
{
lean_dec_ref_known(v_a_854_, 1);
return v___x_853_;
}
}
}
else
{
lean_dec_ref(v___y_842_);
return v___x_853_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__0___boxed(lean_object* v_x_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__0(v_x_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
return v_res_889_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_912_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__9));
v___x_913_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__11));
v___x_914_ = l_Lean_Name_append(v___x_913_, v___x_912_);
return v___x_914_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__14(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__13));
v___x_917_ = l_Lean_stringToMessageData(v___x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(lean_object* v_upperBound_918_, lean_object* v___x_919_, lean_object* v___x_920_, lean_object* v___x_921_, lean_object* v___x_922_, lean_object* v_a_923_, lean_object* v_b_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v___y_938_; uint8_t v___x_960_; 
v___x_960_ = lean_nat_dec_lt(v_a_923_, v_upperBound_918_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; 
lean_dec(v_a_923_);
lean_dec_ref(v___x_922_);
lean_dec_ref(v___x_921_);
lean_dec_ref(v___x_920_);
v___x_961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_961_, 0, v_b_924_);
return v___x_961_;
}
else
{
lean_object* v_snd_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_1047_; 
v_snd_962_ = lean_ctor_get(v_b_924_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_b_924_);
if (v_isSharedCheck_1047_ == 0)
{
lean_object* v_unused_1048_; 
v_unused_1048_ = lean_ctor_get(v_b_924_, 0);
lean_dec(v_unused_1048_);
v___x_964_ = v_b_924_;
v_isShared_965_ = v_isSharedCheck_1047_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_snd_962_);
lean_dec(v_b_924_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_1047_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; lean_object* v___x_970_; 
v___x_966_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__5));
v___x_967_ = lean_box(0);
v___x_968_ = lean_array_fget_borrowed(v___x_919_, v_a_923_);
v___x_969_ = 0;
lean_inc(v___x_968_);
lean_inc_ref(v___x_920_);
v___x_970_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v___x_969_, v___x_966_, v___x_920_, v___x_968_, v___y_926_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; uint8_t v___x_972_; lean_object* v___x_973_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
lean_dec_ref_known(v___x_970_, 1);
v___x_972_ = 0;
lean_inc_ref(v___x_922_);
lean_inc_ref(v___x_921_);
v___x_973_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v___x_972_, v___x_921_, v___x_922_, v_a_971_, v___y_926_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v_type_975_; lean_object* v_value_976_; uint8_t v___x_977_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
v_type_975_ = lean_ctor_get(v_a_974_, 1);
v_value_976_ = lean_ctor_get(v_a_974_, 2);
lean_inc_ref(v_type_975_);
v___x_977_ = l_Lean_Expr_isFalse(v_type_975_);
if (v___x_977_ == 0)
{
lean_object* v_type_978_; lean_object* v___f_979_; uint8_t v___x_980_; 
lean_del_object(v___x_964_);
v_type_978_ = lean_ctor_get(v___x_968_, 1);
lean_inc(v_a_974_);
lean_inc(v_snd_962_);
v___f_979_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__5___boxed), 16, 3);
lean_closure_set(v___f_979_, 0, v_snd_962_);
lean_closure_set(v___f_979_, 1, v_a_974_);
lean_closure_set(v___f_979_, 2, v___x_967_);
v___x_980_ = lean_expr_eqv(v_type_978_, v_type_975_);
if (v___x_980_ == 0)
{
lean_object* v_toCold_981_; lean_object* v_options_982_; lean_object* v_inheritedTraceOptions_983_; uint8_t v_hasTrace_984_; 
lean_inc_ref(v_type_975_);
lean_dec(v_a_974_);
lean_dec(v_snd_962_);
v_toCold_981_ = lean_ctor_get(v___y_934_, 0);
v_options_982_ = lean_ctor_get(v_toCold_981_, 2);
v_inheritedTraceOptions_983_ = lean_ctor_get(v_toCold_981_, 11);
v_hasTrace_984_ = lean_ctor_get_uint8(v_options_982_, sizeof(void*)*1);
if (v_hasTrace_984_ == 0)
{
lean_dec_ref(v_type_975_);
goto v___jp_985_;
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_988_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__9));
v___x_989_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12);
v___x_990_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_983_, v_options_982_, v___x_989_);
if (v___x_990_ == 0)
{
lean_dec_ref(v_type_975_);
goto v___jp_985_;
}
else
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
lean_inc_ref(v_type_978_);
v___x_991_ = l_Lean_MessageData_ofExpr(v_type_978_);
v___x_992_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__14, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__14_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__14);
v___x_993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_991_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = l_Lean_MessageData_ofExpr(v_type_975_);
v___x_995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_993_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v___x_988_, v___x_995_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_998_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
lean_inc(v_a_997_);
lean_dec_ref_known(v___x_996_, 1);
v___x_998_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__6(v___x_960_, v___f_979_, v_a_997_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
v___y_938_ = v___x_998_;
goto v___jp_937_;
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec_ref(v___f_979_);
lean_dec(v_a_923_);
lean_dec_ref(v___x_922_);
lean_dec_ref(v___x_921_);
lean_dec_ref(v___x_920_);
v_a_999_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_996_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_996_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
}
v___jp_985_:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = lean_box(0);
v___x_987_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__6(v___x_960_, v___f_979_, v___x_986_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
v___y_938_ = v___x_987_;
goto v___jp_937_;
}
}
else
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_dec_ref(v___f_979_);
v___x_1007_ = lean_box(0);
v___x_1008_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__5(v_snd_962_, v_a_974_, v___x_967_, v___x_1007_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
v___y_938_ = v___x_1008_;
goto v___jp_937_;
}
}
else
{
lean_object* v___x_1009_; 
lean_inc_ref(v_value_976_);
lean_dec(v_a_974_);
lean_dec(v_a_923_);
lean_dec_ref(v___x_922_);
lean_dec_ref(v___x_921_);
lean_dec_ref(v___x_920_);
v___x_1009_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_976_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1021_; 
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1021_ == 0)
{
lean_object* v_unused_1022_; 
v_unused_1022_ = lean_ctor_get(v___x_1009_, 0);
lean_dec(v_unused_1022_);
v___x_1011_ = v___x_1009_;
v_isShared_1012_ = v_isSharedCheck_1021_;
goto v_resetjp_1010_;
}
else
{
lean_dec(v___x_1009_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1021_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
v___x_1013_ = lean_box(v___x_960_);
v___x_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_1014_);
v___x_1016_ = v___x_964_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1020_, 1, v_snd_962_);
v___x_1016_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
lean_object* v___x_1018_; 
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1016_);
v___x_1018_ = v___x_1011_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_del_object(v___x_964_);
lean_dec(v_snd_962_);
v_a_1023_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_1009_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_1009_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_del_object(v___x_964_);
lean_dec(v_snd_962_);
lean_dec(v_a_923_);
lean_dec_ref(v___x_922_);
lean_dec_ref(v___x_921_);
lean_dec_ref(v___x_920_);
v_a_1031_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_973_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_973_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
else
{
lean_object* v_a_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_del_object(v___x_964_);
lean_dec(v_snd_962_);
lean_dec(v_a_923_);
lean_dec_ref(v___x_922_);
lean_dec_ref(v___x_921_);
lean_dec_ref(v___x_920_);
v_a_1039_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_970_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_a_1039_);
lean_dec(v___x_970_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_a_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
v___jp_937_:
{
if (lean_obj_tag(v___y_938_) == 0)
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_951_; 
v_a_939_ = lean_ctor_get(v___y_938_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___y_938_);
if (v_isSharedCheck_951_ == 0)
{
v___x_941_ = v___y_938_;
v_isShared_942_ = v_isSharedCheck_951_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___y_938_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_951_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
if (lean_obj_tag(v_a_939_) == 0)
{
lean_object* v_a_943_; lean_object* v___x_945_; 
lean_dec(v_a_923_);
lean_dec_ref(v___x_922_);
lean_dec_ref(v___x_921_);
lean_dec_ref(v___x_920_);
v_a_943_ = lean_ctor_get(v_a_939_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v_a_939_, 1);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v_a_943_);
v___x_945_ = v___x_941_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
lean_del_object(v___x_941_);
v_a_947_ = lean_ctor_get(v_a_939_, 0);
lean_inc(v_a_947_);
lean_dec_ref_known(v_a_939_, 1);
v___x_948_ = lean_unsigned_to_nat(1u);
v___x_949_ = lean_nat_add(v_a_923_, v___x_948_);
lean_dec(v_a_923_);
v_a_923_ = v___x_949_;
v_b_924_ = v_a_947_;
goto _start;
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec(v_a_923_);
lean_dec_ref(v___x_922_);
lean_dec_ref(v___x_921_);
lean_dec_ref(v___x_920_);
v_a_952_ = lean_ctor_get(v___y_938_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___y_938_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___y_938_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___y_938_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_1049_ = _args[0];
lean_object* v___x_1050_ = _args[1];
lean_object* v___x_1051_ = _args[2];
lean_object* v___x_1052_ = _args[3];
lean_object* v___x_1053_ = _args[4];
lean_object* v_a_1054_ = _args[5];
lean_object* v_b_1055_ = _args[6];
lean_object* v___y_1056_ = _args[7];
lean_object* v___y_1057_ = _args[8];
lean_object* v___y_1058_ = _args[9];
lean_object* v___y_1059_ = _args[10];
lean_object* v___y_1060_ = _args[11];
lean_object* v___y_1061_ = _args[12];
lean_object* v___y_1062_ = _args[13];
lean_object* v___y_1063_ = _args[14];
lean_object* v___y_1064_ = _args[15];
lean_object* v___y_1065_ = _args[16];
lean_object* v___y_1066_ = _args[17];
lean_object* v___y_1067_ = _args[18];
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v_upperBound_1049_, v___x_1050_, v___x_1051_, v___x_1052_, v___x_1053_, v_a_1054_, v_b_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec_ref(v___x_1050_);
lean_dec(v_upperBound_1049_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4(lean_object* v___x_1069_, lean_object* v___x_1070_, lean_object* v___x_1071_, lean_object* v___x_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v___x_1085_; lean_object* v_hypotheses_1086_; lean_object* v___x_1087_; lean_object* v_newHyps_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1085_ = lean_st_ref_get(v___y_1074_);
v_hypotheses_1086_ = lean_ctor_get(v___x_1085_, 3);
lean_inc_ref(v_hypotheses_1086_);
lean_dec(v___x_1085_);
v___x_1087_ = lean_array_get_size(v_hypotheses_1086_);
v_newHyps_1088_ = lean_mk_empty_array_with_capacity(v___x_1087_);
v___x_1089_ = lean_box(0);
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
lean_ctor_set(v___x_1090_, 1, v_newHyps_1088_);
v___x_1091_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v___x_1087_, v_hypotheses_1086_, v___x_1069_, v___x_1070_, v___x_1071_, v___x_1072_, v___x_1090_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec_ref(v_hypotheses_1086_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1121_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1121_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1121_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v_fst_1096_; 
v_fst_1096_ = lean_ctor_get(v_a_1092_, 0);
if (lean_obj_tag(v_fst_1096_) == 0)
{
lean_object* v_snd_1097_; lean_object* v___x_1098_; lean_object* v_caches_1099_; lean_object* v_typeAnalysis_1100_; lean_object* v_target_1101_; uint8_t v_didChange_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1115_; 
v_snd_1097_ = lean_ctor_get(v_a_1092_, 1);
lean_inc(v_snd_1097_);
lean_dec(v_a_1092_);
v___x_1098_ = lean_st_ref_take(v___y_1074_);
v_caches_1099_ = lean_ctor_get(v___x_1098_, 0);
v_typeAnalysis_1100_ = lean_ctor_get(v___x_1098_, 1);
v_target_1101_ = lean_ctor_get(v___x_1098_, 2);
v_didChange_1102_ = lean_ctor_get_uint8(v___x_1098_, sizeof(void*)*4);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; 
v_unused_1116_ = lean_ctor_get(v___x_1098_, 3);
lean_dec(v_unused_1116_);
v___x_1104_ = v___x_1098_;
v_isShared_1105_ = v_isSharedCheck_1115_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_target_1101_);
lean_inc(v_typeAnalysis_1100_);
lean_inc(v_caches_1099_);
lean_dec(v___x_1098_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1115_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 3, v_snd_1097_);
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_caches_1099_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_typeAnalysis_1100_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_target_1101_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_snd_1097_);
lean_ctor_set_uint8(v_reuseFailAlloc_1114_, sizeof(void*)*4, v_didChange_1102_);
v___x_1107_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1108_; uint8_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1108_ = lean_st_ref_put(v___y_1074_, v___x_1107_);
v___x_1109_ = 0;
v___x_1110_ = lean_box(v___x_1109_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1110_);
v___x_1112_ = v___x_1094_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
else
{
lean_object* v_val_1117_; lean_object* v___x_1119_; 
lean_inc_ref(v_fst_1096_);
lean_dec(v_a_1092_);
v_val_1117_ = lean_ctor_get(v_fst_1096_, 0);
lean_inc(v_val_1117_);
lean_dec_ref_known(v_fst_1096_, 1);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v_val_1117_);
v___x_1119_ = v___x_1094_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_val_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
v_a_1122_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1091_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1091_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4___boxed(lean_object* v___x_1130_, lean_object* v___x_1131_, lean_object* v___x_1132_, lean_object* v___x_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4(v___x_1130_, v___x_1131_, v___x_1132_, v___x_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8___redArg(lean_object* v_x_1147_){
_start:
{
if (lean_obj_tag(v_x_1147_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
v_a_1149_ = lean_ctor_get(v_x_1147_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_x_1147_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v_x_1147_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v_x_1147_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set_tag(v___x_1151_, 1);
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
v_a_1157_ = lean_ctor_get(v_x_1147_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_x_1147_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v_x_1147_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v_x_1147_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set_tag(v___x_1159_, 0);
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8___redArg___boxed(lean_object* v_x_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8___redArg(v_x_1165_);
return v_res_1167_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__9(lean_object* v_e_1168_){
_start:
{
if (lean_obj_tag(v_e_1168_) == 0)
{
uint8_t v___x_1169_; 
v___x_1169_ = 2;
return v___x_1169_;
}
else
{
uint8_t v___x_1170_; 
v___x_1170_ = 0;
return v___x_1170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__9___boxed(lean_object* v_e_1171_){
_start:
{
uint8_t v_res_1172_; lean_object* v_r_1173_; 
v_res_1172_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__9(v_e_1171_);
lean_dec_ref(v_e_1171_);
v_r_1173_ = lean_box(v_res_1172_);
return v_r_1173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7_spec__8(size_t v_sz_1174_, size_t v_i_1175_, lean_object* v_bs_1176_){
_start:
{
uint8_t v___x_1177_; 
v___x_1177_ = lean_usize_dec_lt(v_i_1175_, v_sz_1174_);
if (v___x_1177_ == 0)
{
return v_bs_1176_;
}
else
{
lean_object* v_v_1178_; lean_object* v_msg_1179_; lean_object* v___x_1180_; lean_object* v_bs_x27_1181_; size_t v___x_1182_; size_t v___x_1183_; lean_object* v___x_1184_; 
v_v_1178_ = lean_array_uget_borrowed(v_bs_1176_, v_i_1175_);
v_msg_1179_ = lean_ctor_get(v_v_1178_, 1);
lean_inc_ref(v_msg_1179_);
v___x_1180_ = lean_unsigned_to_nat(0u);
v_bs_x27_1181_ = lean_array_uset(v_bs_1176_, v_i_1175_, v___x_1180_);
v___x_1182_ = ((size_t)1ULL);
v___x_1183_ = lean_usize_add(v_i_1175_, v___x_1182_);
v___x_1184_ = lean_array_uset(v_bs_x27_1181_, v_i_1175_, v_msg_1179_);
v_i_1175_ = v___x_1183_;
v_bs_1176_ = v___x_1184_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7_spec__8___boxed(lean_object* v_sz_1186_, lean_object* v_i_1187_, lean_object* v_bs_1188_){
_start:
{
size_t v_sz_boxed_1189_; size_t v_i_boxed_1190_; lean_object* v_res_1191_; 
v_sz_boxed_1189_ = lean_unbox_usize(v_sz_1186_);
lean_dec(v_sz_1186_);
v_i_boxed_1190_ = lean_unbox_usize(v_i_1187_);
lean_dec(v_i_1187_);
v_res_1191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7_spec__8(v_sz_boxed_1189_, v_i_boxed_1190_, v_bs_1188_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7___redArg(lean_object* v_oldTraces_1192_, lean_object* v_data_1193_, lean_object* v_ref_1194_, lean_object* v_msg_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_toCold_1201_; lean_object* v_currRecDepth_1202_; lean_object* v_ref_1203_; uint16_t v_optionFlags_1204_; uint8_t v_suppressElabErrors_1205_; uint8_t v_isRecordingDeps_1206_; lean_object* v_ref_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v_traceState_1210_; lean_object* v_traces_1211_; lean_object* v___x_1212_; size_t v_sz_1213_; size_t v___x_1214_; lean_object* v___x_1215_; lean_object* v_msg_1216_; lean_object* v___x_1217_; lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1256_; 
v_toCold_1201_ = lean_ctor_get(v___y_1198_, 0);
v_currRecDepth_1202_ = lean_ctor_get(v___y_1198_, 1);
v_ref_1203_ = lean_ctor_get(v___y_1198_, 2);
v_optionFlags_1204_ = lean_ctor_get_uint16(v___y_1198_, sizeof(void*)*3);
v_suppressElabErrors_1205_ = lean_ctor_get_uint8(v___y_1198_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1206_ = lean_ctor_get_uint8(v___y_1198_, sizeof(void*)*3 + 3);
v_ref_1207_ = l_Lean_replaceRef(v_ref_1194_, v_ref_1203_);
lean_inc(v_currRecDepth_1202_);
lean_inc_ref(v_toCold_1201_);
v___x_1208_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1208_, 0, v_toCold_1201_);
lean_ctor_set(v___x_1208_, 1, v_currRecDepth_1202_);
lean_ctor_set(v___x_1208_, 2, v_ref_1207_);
lean_ctor_set_uint16(v___x_1208_, sizeof(void*)*3, v_optionFlags_1204_);
lean_ctor_set_uint8(v___x_1208_, sizeof(void*)*3 + 2, v_suppressElabErrors_1205_);
lean_ctor_set_uint8(v___x_1208_, sizeof(void*)*3 + 3, v_isRecordingDeps_1206_);
v___x_1209_ = lean_st_ref_get(v___y_1199_);
v_traceState_1210_ = lean_ctor_get(v___x_1209_, 4);
lean_inc_ref(v_traceState_1210_);
lean_dec(v___x_1209_);
v_traces_1211_ = lean_ctor_get(v_traceState_1210_, 0);
lean_inc_ref(v_traces_1211_);
lean_dec_ref(v_traceState_1210_);
v___x_1212_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1211_);
lean_dec_ref(v_traces_1211_);
v_sz_1213_ = lean_array_size(v___x_1212_);
v___x_1214_ = ((size_t)0ULL);
v___x_1215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7_spec__8(v_sz_1213_, v___x_1214_, v___x_1212_);
v_msg_1216_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1216_, 0, v_data_1193_);
lean_ctor_set(v_msg_1216_, 1, v_msg_1195_);
lean_ctor_set(v_msg_1216_, 2, v___x_1215_);
v___x_1217_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(v_msg_1216_, v___y_1196_, v___y_1197_, v___x_1208_, v___y_1199_);
lean_dec_ref_known(v___x_1208_, 3);
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1220_ = v___x_1217_;
v_isShared_1221_ = v_isSharedCheck_1256_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1217_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1256_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v_traceState_1223_; lean_object* v_env_1224_; lean_object* v_nextMacroScope_1225_; lean_object* v_ngen_1226_; lean_object* v_auxDeclNGen_1227_; lean_object* v_cache_1228_; lean_object* v_recordedDeps_1229_; lean_object* v_messages_1230_; lean_object* v_infoState_1231_; lean_object* v_snapshotTasks_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1255_; 
v___x_1222_ = lean_st_ref_take(v___y_1199_);
v_traceState_1223_ = lean_ctor_get(v___x_1222_, 4);
v_env_1224_ = lean_ctor_get(v___x_1222_, 0);
v_nextMacroScope_1225_ = lean_ctor_get(v___x_1222_, 1);
v_ngen_1226_ = lean_ctor_get(v___x_1222_, 2);
v_auxDeclNGen_1227_ = lean_ctor_get(v___x_1222_, 3);
v_cache_1228_ = lean_ctor_get(v___x_1222_, 5);
v_recordedDeps_1229_ = lean_ctor_get(v___x_1222_, 6);
v_messages_1230_ = lean_ctor_get(v___x_1222_, 7);
v_infoState_1231_ = lean_ctor_get(v___x_1222_, 8);
v_snapshotTasks_1232_ = lean_ctor_get(v___x_1222_, 9);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1234_ = v___x_1222_;
v_isShared_1235_ = v_isSharedCheck_1255_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_snapshotTasks_1232_);
lean_inc(v_infoState_1231_);
lean_inc(v_messages_1230_);
lean_inc(v_recordedDeps_1229_);
lean_inc(v_cache_1228_);
lean_inc(v_traceState_1223_);
lean_inc(v_auxDeclNGen_1227_);
lean_inc(v_ngen_1226_);
lean_inc(v_nextMacroScope_1225_);
lean_inc(v_env_1224_);
lean_dec(v___x_1222_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1255_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
uint64_t v_tid_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1253_; 
v_tid_1236_ = lean_ctor_get_uint64(v_traceState_1223_, sizeof(void*)*1);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_traceState_1223_);
if (v_isSharedCheck_1253_ == 0)
{
lean_object* v_unused_1254_; 
v_unused_1254_ = lean_ctor_get(v_traceState_1223_, 0);
lean_dec(v_unused_1254_);
v___x_1238_ = v_traceState_1223_;
v_isShared_1239_ = v_isSharedCheck_1253_;
goto v_resetjp_1237_;
}
else
{
lean_dec(v_traceState_1223_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1253_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1240_ = lean_box(0);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v_ref_1194_);
lean_ctor_set(v___x_1241_, 1, v_a_1218_);
v___x_1242_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1192_, v___x_1241_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1242_);
v___x_1244_ = v___x_1238_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1242_);
lean_ctor_set_uint64(v_reuseFailAlloc_1252_, sizeof(void*)*1, v_tid_1236_);
v___x_1244_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1246_; 
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 4, v___x_1244_);
v___x_1246_ = v___x_1234_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_env_1224_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_nextMacroScope_1225_);
lean_ctor_set(v_reuseFailAlloc_1251_, 2, v_ngen_1226_);
lean_ctor_set(v_reuseFailAlloc_1251_, 3, v_auxDeclNGen_1227_);
lean_ctor_set(v_reuseFailAlloc_1251_, 4, v___x_1244_);
lean_ctor_set(v_reuseFailAlloc_1251_, 5, v_cache_1228_);
lean_ctor_set(v_reuseFailAlloc_1251_, 6, v_recordedDeps_1229_);
lean_ctor_set(v_reuseFailAlloc_1251_, 7, v_messages_1230_);
lean_ctor_set(v_reuseFailAlloc_1251_, 8, v_infoState_1231_);
lean_ctor_set(v_reuseFailAlloc_1251_, 9, v_snapshotTasks_1232_);
v___x_1246_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1247_ = lean_st_ref_put(v___y_1199_, v___x_1246_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1240_);
v___x_1249_ = v___x_1220_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1240_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7___redArg___boxed(lean_object* v_oldTraces_1257_, lean_object* v_data_1258_, lean_object* v_ref_1259_, lean_object* v_msg_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7___redArg(v_oldTraces_1257_, v_data_1258_, v_ref_1259_, v_msg_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__10(lean_object* v_opts_1267_, lean_object* v_opt_1268_){
_start:
{
lean_object* v_name_1269_; lean_object* v_defValue_1270_; lean_object* v_map_1271_; lean_object* v___x_1272_; 
v_name_1269_ = lean_ctor_get(v_opt_1268_, 0);
v_defValue_1270_ = lean_ctor_get(v_opt_1268_, 1);
v_map_1271_ = lean_ctor_get(v_opts_1267_, 0);
v___x_1272_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1271_, v_name_1269_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_inc(v_defValue_1270_);
return v_defValue_1270_;
}
else
{
lean_object* v_val_1273_; 
v_val_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_val_1273_);
lean_dec_ref_known(v___x_1272_, 1);
if (lean_obj_tag(v_val_1273_) == 3)
{
lean_object* v_v_1274_; 
v_v_1274_ = lean_ctor_get(v_val_1273_, 0);
lean_inc(v_v_1274_);
lean_dec_ref_known(v_val_1273_, 1);
return v_v_1274_;
}
else
{
lean_dec(v_val_1273_);
lean_inc(v_defValue_1270_);
return v_defValue_1270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__10___boxed(lean_object* v_opts_1275_, lean_object* v_opt_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__10(v_opts_1275_, v_opt_1276_);
lean_dec_ref(v_opt_1276_);
lean_dec_ref(v_opts_1275_);
return v_res_1277_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__1(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__0));
v___x_1280_ = l_Lean_stringToMessageData(v___x_1279_);
return v___x_1280_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1281_; double v___x_1282_; 
v___x_1281_ = lean_unsigned_to_nat(1000u);
v___x_1282_ = lean_float_of_nat(v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(lean_object* v_cls_1283_, uint8_t v_collapsed_1284_, lean_object* v_tag_1285_, lean_object* v_opts_1286_, uint8_t v_clsEnabled_1287_, lean_object* v_oldTraces_1288_, lean_object* v_msg_1289_, lean_object* v_resStartStop_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_fst_1303_; lean_object* v_snd_1304_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v_data_1308_; lean_object* v_fst_1311_; lean_object* v_snd_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; lean_object* v___y_1316_; lean_object* v_a_1317_; uint8_t v___y_1332_; double v___y_1364_; 
v_fst_1303_ = lean_ctor_get(v_resStartStop_1290_, 0);
lean_inc(v_fst_1303_);
v_snd_1304_ = lean_ctor_get(v_resStartStop_1290_, 1);
lean_inc(v_snd_1304_);
lean_dec_ref(v_resStartStop_1290_);
v_fst_1311_ = lean_ctor_get(v_snd_1304_, 0);
lean_inc(v_fst_1311_);
v_snd_1312_ = lean_ctor_get(v_snd_1304_, 1);
lean_inc(v_snd_1312_);
lean_dec(v_snd_1304_);
v___x_1313_ = l_Lean_trace_profiler;
v___x_1314_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5(v_opts_1286_, v___x_1313_);
if (v___x_1314_ == 0)
{
v___y_1332_ = v___x_1314_;
goto v___jp_1331_;
}
else
{
lean_object* v___x_1369_; uint8_t v___x_1370_; 
v___x_1369_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1370_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5(v_opts_1286_, v___x_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; double v___x_1373_; double v___x_1374_; double v___x_1375_; 
v___x_1371_ = l_Lean_trace_profiler_threshold;
v___x_1372_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__10(v_opts_1286_, v___x_1371_);
v___x_1373_ = lean_float_of_nat(v___x_1372_);
v___x_1374_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__2);
v___x_1375_ = lean_float_div(v___x_1373_, v___x_1374_);
v___y_1364_ = v___x_1375_;
goto v___jp_1363_;
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; double v___x_1378_; 
v___x_1376_ = l_Lean_trace_profiler_threshold;
v___x_1377_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__10(v_opts_1286_, v___x_1376_);
v___x_1378_ = lean_float_of_nat(v___x_1377_);
v___y_1364_ = v___x_1378_;
goto v___jp_1363_;
}
}
v___jp_1305_:
{
lean_object* v___x_1309_; 
lean_inc(v___y_1306_);
v___x_1309_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7___redArg(v_oldTraces_1288_, v_data_1308_, v___y_1306_, v___y_1307_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v___x_1310_; 
lean_dec_ref_known(v___x_1309_, 1);
v___x_1310_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8___redArg(v_fst_1303_);
return v___x_1310_;
}
else
{
lean_dec(v_fst_1303_);
return v___x_1309_;
}
}
v___jp_1315_:
{
uint8_t v_result_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; double v___x_1321_; lean_object* v_data_1322_; 
v_result_1318_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__9(v_fst_1303_);
v___x_1319_ = lean_box(v_result_1318_);
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
v___x_1321_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_1285_);
lean_inc_ref(v___x_1320_);
lean_inc(v_cls_1283_);
v_data_1322_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1322_, 0, v_cls_1283_);
lean_ctor_set(v_data_1322_, 1, v___x_1320_);
lean_ctor_set(v_data_1322_, 2, v_tag_1285_);
lean_ctor_set_float(v_data_1322_, sizeof(void*)*3, v___x_1321_);
lean_ctor_set_float(v_data_1322_, sizeof(void*)*3 + 8, v___x_1321_);
lean_ctor_set_uint8(v_data_1322_, sizeof(void*)*3 + 16, v_collapsed_1284_);
if (v___x_1314_ == 0)
{
lean_dec_ref_known(v___x_1320_, 1);
lean_dec(v_snd_1312_);
lean_dec(v_fst_1311_);
lean_dec_ref(v_tag_1285_);
lean_dec(v_cls_1283_);
v___y_1306_ = v___y_1316_;
v___y_1307_ = v_a_1317_;
v_data_1308_ = v_data_1322_;
goto v___jp_1305_;
}
else
{
lean_object* v_data_1323_; double v___x_1324_; double v___x_1325_; 
lean_dec_ref_known(v_data_1322_, 3);
v_data_1323_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1323_, 0, v_cls_1283_);
lean_ctor_set(v_data_1323_, 1, v___x_1320_);
lean_ctor_set(v_data_1323_, 2, v_tag_1285_);
v___x_1324_ = lean_unbox_float(v_fst_1311_);
lean_dec(v_fst_1311_);
lean_ctor_set_float(v_data_1323_, sizeof(void*)*3, v___x_1324_);
v___x_1325_ = lean_unbox_float(v_snd_1312_);
lean_dec(v_snd_1312_);
lean_ctor_set_float(v_data_1323_, sizeof(void*)*3 + 8, v___x_1325_);
lean_ctor_set_uint8(v_data_1323_, sizeof(void*)*3 + 16, v_collapsed_1284_);
v___y_1306_ = v___y_1316_;
v___y_1307_ = v_a_1317_;
v_data_1308_ = v_data_1323_;
goto v___jp_1305_;
}
}
v___jp_1326_:
{
lean_object* v_ref_1327_; lean_object* v___x_1328_; 
v_ref_1327_ = lean_ctor_get(v___y_1300_, 2);
lean_inc(v___y_1301_);
lean_inc_ref(v___y_1300_);
lean_inc(v___y_1299_);
lean_inc_ref(v___y_1298_);
lean_inc(v___y_1297_);
lean_inc_ref(v___y_1296_);
lean_inc(v___y_1295_);
lean_inc_ref(v___y_1294_);
lean_inc(v___y_1293_);
lean_inc(v___y_1292_);
lean_inc_ref(v___y_1291_);
lean_inc(v_fst_1303_);
v___x_1328_ = lean_apply_13(v_msg_1289_, v_fst_1303_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, lean_box(0));
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1328_, 1);
v___y_1316_ = v_ref_1327_;
v_a_1317_ = v_a_1329_;
goto v___jp_1315_;
}
else
{
lean_object* v___x_1330_; 
lean_dec_ref_known(v___x_1328_, 1);
v___x_1330_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__1);
v___y_1316_ = v_ref_1327_;
v_a_1317_ = v___x_1330_;
goto v___jp_1315_;
}
}
v___jp_1331_:
{
if (v_clsEnabled_1287_ == 0)
{
if (v___y_1332_ == 0)
{
lean_object* v___x_1333_; lean_object* v_traceState_1334_; lean_object* v_env_1335_; lean_object* v_nextMacroScope_1336_; lean_object* v_ngen_1337_; lean_object* v_auxDeclNGen_1338_; lean_object* v_cache_1339_; lean_object* v_recordedDeps_1340_; lean_object* v_messages_1341_; lean_object* v_infoState_1342_; lean_object* v_snapshotTasks_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1362_; 
lean_dec(v_snd_1312_);
lean_dec(v_fst_1311_);
lean_dec_ref(v_msg_1289_);
lean_dec_ref(v_tag_1285_);
lean_dec(v_cls_1283_);
v___x_1333_ = lean_st_ref_take(v___y_1301_);
v_traceState_1334_ = lean_ctor_get(v___x_1333_, 4);
v_env_1335_ = lean_ctor_get(v___x_1333_, 0);
v_nextMacroScope_1336_ = lean_ctor_get(v___x_1333_, 1);
v_ngen_1337_ = lean_ctor_get(v___x_1333_, 2);
v_auxDeclNGen_1338_ = lean_ctor_get(v___x_1333_, 3);
v_cache_1339_ = lean_ctor_get(v___x_1333_, 5);
v_recordedDeps_1340_ = lean_ctor_get(v___x_1333_, 6);
v_messages_1341_ = lean_ctor_get(v___x_1333_, 7);
v_infoState_1342_ = lean_ctor_get(v___x_1333_, 8);
v_snapshotTasks_1343_ = lean_ctor_get(v___x_1333_, 9);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1345_ = v___x_1333_;
v_isShared_1346_ = v_isSharedCheck_1362_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_snapshotTasks_1343_);
lean_inc(v_infoState_1342_);
lean_inc(v_messages_1341_);
lean_inc(v_recordedDeps_1340_);
lean_inc(v_cache_1339_);
lean_inc(v_traceState_1334_);
lean_inc(v_auxDeclNGen_1338_);
lean_inc(v_ngen_1337_);
lean_inc(v_nextMacroScope_1336_);
lean_inc(v_env_1335_);
lean_dec(v___x_1333_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1362_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
uint64_t v_tid_1347_; lean_object* v_traces_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1361_; 
v_tid_1347_ = lean_ctor_get_uint64(v_traceState_1334_, sizeof(void*)*1);
v_traces_1348_ = lean_ctor_get(v_traceState_1334_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_traceState_1334_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1350_ = v_traceState_1334_;
v_isShared_1351_ = v_isSharedCheck_1361_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_traces_1348_);
lean_dec(v_traceState_1334_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1361_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1352_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1288_, v_traces_1348_);
lean_dec_ref(v_traces_1348_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1352_);
v___x_1354_ = v___x_1350_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1352_);
lean_ctor_set_uint64(v_reuseFailAlloc_1360_, sizeof(void*)*1, v_tid_1347_);
v___x_1354_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1356_; 
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 4, v___x_1354_);
v___x_1356_ = v___x_1345_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_env_1335_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_nextMacroScope_1336_);
lean_ctor_set(v_reuseFailAlloc_1359_, 2, v_ngen_1337_);
lean_ctor_set(v_reuseFailAlloc_1359_, 3, v_auxDeclNGen_1338_);
lean_ctor_set(v_reuseFailAlloc_1359_, 4, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1359_, 5, v_cache_1339_);
lean_ctor_set(v_reuseFailAlloc_1359_, 6, v_recordedDeps_1340_);
lean_ctor_set(v_reuseFailAlloc_1359_, 7, v_messages_1341_);
lean_ctor_set(v_reuseFailAlloc_1359_, 8, v_infoState_1342_);
lean_ctor_set(v_reuseFailAlloc_1359_, 9, v_snapshotTasks_1343_);
v___x_1356_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1357_ = lean_st_ref_put(v___y_1301_, v___x_1356_);
v___x_1358_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8___redArg(v_fst_1303_);
return v___x_1358_;
}
}
}
}
}
else
{
goto v___jp_1326_;
}
}
else
{
goto v___jp_1326_;
}
}
v___jp_1363_:
{
double v___x_1365_; double v___x_1366_; double v___x_1367_; uint8_t v___x_1368_; 
v___x_1365_ = lean_unbox_float(v_snd_1312_);
v___x_1366_ = lean_unbox_float(v_fst_1311_);
v___x_1367_ = lean_float_sub(v___x_1365_, v___x_1366_);
v___x_1368_ = lean_float_decLt(v___y_1364_, v___x_1367_);
v___y_1332_ = v___x_1368_;
goto v___jp_1331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___boxed(lean_object** _args){
lean_object* v_cls_1379_ = _args[0];
lean_object* v_collapsed_1380_ = _args[1];
lean_object* v_tag_1381_ = _args[2];
lean_object* v_opts_1382_ = _args[3];
lean_object* v_clsEnabled_1383_ = _args[4];
lean_object* v_oldTraces_1384_ = _args[5];
lean_object* v_msg_1385_ = _args[6];
lean_object* v_resStartStop_1386_ = _args[7];
lean_object* v___y_1387_ = _args[8];
lean_object* v___y_1388_ = _args[9];
lean_object* v___y_1389_ = _args[10];
lean_object* v___y_1390_ = _args[11];
lean_object* v___y_1391_ = _args[12];
lean_object* v___y_1392_ = _args[13];
lean_object* v___y_1393_ = _args[14];
lean_object* v___y_1394_ = _args[15];
lean_object* v___y_1395_ = _args[16];
lean_object* v___y_1396_ = _args[17];
lean_object* v___y_1397_ = _args[18];
lean_object* v___y_1398_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_1399_; uint8_t v_clsEnabled_boxed_1400_; lean_object* v_res_1401_; 
v_collapsed_boxed_1399_ = lean_unbox(v_collapsed_1380_);
v_clsEnabled_boxed_1400_ = lean_unbox(v_clsEnabled_1383_);
v_res_1401_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(v_cls_1379_, v_collapsed_boxed_1399_, v_tag_1381_, v_opts_1382_, v_clsEnabled_boxed_1400_, v_oldTraces_1384_, v_msg_1385_, v_resStartStop_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec_ref(v_opts_1382_);
return v_res_1401_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___closed__0));
v___x_1404_ = l_Lean_stringToMessageData(v___x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3(lean_object* v_as_1405_, size_t v_sz_1406_, size_t v_i_1407_, lean_object* v_b_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v_a_1422_; uint8_t v___x_1426_; 
v___x_1426_ = lean_usize_dec_lt(v_i_1407_, v_sz_1406_);
if (v___x_1426_ == 0)
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v_b_1408_);
return v___x_1427_;
}
else
{
lean_object* v_a_1428_; lean_object* v_toCold_1429_; lean_object* v_options_1430_; lean_object* v_fst_1431_; lean_object* v_snd_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1452_; 
v_a_1428_ = lean_array_uget(v_as_1405_, v_i_1407_);
v_toCold_1429_ = lean_ctor_get(v___y_1418_, 0);
v_options_1430_ = lean_ctor_get(v_toCold_1429_, 2);
v_fst_1431_ = lean_ctor_get(v_a_1428_, 0);
v_snd_1432_ = lean_ctor_get(v_a_1428_, 1);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_a_1428_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1434_ = v_a_1428_;
v_isShared_1435_ = v_isSharedCheck_1452_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_snd_1432_);
lean_inc(v_fst_1431_);
lean_dec(v_a_1428_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1452_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v_inheritedTraceOptions_1436_; uint8_t v_hasTrace_1437_; lean_object* v___x_1438_; 
v_inheritedTraceOptions_1436_ = lean_ctor_get(v_toCold_1429_, 11);
v_hasTrace_1437_ = lean_ctor_get_uint8(v_options_1430_, sizeof(void*)*1);
v___x_1438_ = lean_box(0);
if (v_hasTrace_1437_ == 0)
{
lean_del_object(v___x_1434_);
lean_dec(v_snd_1432_);
lean_dec(v_fst_1431_);
v_a_1422_ = v___x_1438_;
goto v___jp_1421_;
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1439_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__9));
v___x_1440_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12);
v___x_1441_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1436_, v_options_1430_, v___x_1440_);
if (v___x_1441_ == 0)
{
lean_del_object(v___x_1434_);
lean_dec(v_snd_1432_);
lean_dec(v_fst_1431_);
v_a_1422_ = v___x_1438_;
goto v___jp_1421_;
}
else
{
lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1442_ = l_Lean_MessageData_ofName(v_fst_1431_);
v___x_1443_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___closed__1);
if (v_isShared_1435_ == 0)
{
lean_ctor_set_tag(v___x_1434_, 7);
lean_ctor_set(v___x_1434_, 1, v___x_1443_);
lean_ctor_set(v___x_1434_, 0, v___x_1442_);
v___x_1445_ = v___x_1434_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v___x_1443_);
v___x_1445_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1446_ = l_Nat_reprFast(v_snd_1432_);
v___x_1447_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1446_);
v___x_1448_ = l_Lean_MessageData_ofFormat(v___x_1447_);
v___x_1449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1445_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
v___x_1450_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v___x_1439_, v___x_1449_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_dec_ref_known(v___x_1450_, 1);
v_a_1422_ = v___x_1438_;
goto v___jp_1421_;
}
else
{
return v___x_1450_;
}
}
}
}
}
}
v___jp_1421_:
{
size_t v___x_1423_; size_t v___x_1424_; 
v___x_1423_ = ((size_t)1ULL);
v___x_1424_ = lean_usize_add(v_i_1407_, v___x_1423_);
v_i_1407_ = v___x_1424_;
v_b_1408_ = v_a_1422_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___boxed(lean_object* v_as_1453_, lean_object* v_sz_1454_, lean_object* v_i_1455_, lean_object* v_b_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
size_t v_sz_boxed_1469_; size_t v_i_boxed_1470_; lean_object* v_res_1471_; 
v_sz_boxed_1469_ = lean_unbox_usize(v_sz_1454_);
lean_dec(v_sz_1454_);
v_i_boxed_1470_ = lean_unbox_usize(v_i_1455_);
lean_dec(v_i_1455_);
v_res_1471_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3(v_as_1453_, v_sz_boxed_1469_, v_i_boxed_1470_, v_b_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec_ref(v_as_1453_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8(lean_object* v_x_1472_, lean_object* v_x_1473_){
_start:
{
if (lean_obj_tag(v_x_1473_) == 0)
{
return v_x_1472_;
}
else
{
lean_object* v_key_1474_; lean_object* v_value_1475_; lean_object* v_tail_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v_key_1474_ = lean_ctor_get(v_x_1473_, 0);
v_value_1475_ = lean_ctor_get(v_x_1473_, 1);
v_tail_1476_ = lean_ctor_get(v_x_1473_, 2);
lean_inc(v_value_1475_);
lean_inc(v_key_1474_);
v___x_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1477_, 0, v_key_1474_);
lean_ctor_set(v___x_1477_, 1, v_value_1475_);
v___x_1478_ = lean_array_push(v_x_1472_, v___x_1477_);
v_x_1472_ = v___x_1478_;
v_x_1473_ = v_tail_1476_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___boxed(lean_object* v_x_1480_, lean_object* v_x_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8(v_x_1480_, v_x_1481_);
lean_dec(v_x_1481_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9(lean_object* v_as_1483_, size_t v_i_1484_, size_t v_stop_1485_, lean_object* v_b_1486_){
_start:
{
uint8_t v___x_1487_; 
v___x_1487_ = lean_usize_dec_eq(v_i_1484_, v_stop_1485_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; lean_object* v___x_1489_; size_t v___x_1490_; size_t v___x_1491_; 
v___x_1488_ = lean_array_uget_borrowed(v_as_1483_, v_i_1484_);
v___x_1489_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8(v_b_1486_, v___x_1488_);
v___x_1490_ = ((size_t)1ULL);
v___x_1491_ = lean_usize_add(v_i_1484_, v___x_1490_);
v_i_1484_ = v___x_1491_;
v_b_1486_ = v___x_1489_;
goto _start;
}
else
{
return v_b_1486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9___boxed(lean_object* v_as_1493_, lean_object* v_i_1494_, lean_object* v_stop_1495_, lean_object* v_b_1496_){
_start:
{
size_t v_i_boxed_1497_; size_t v_stop_boxed_1498_; lean_object* v_res_1499_; 
v_i_boxed_1497_ = lean_unbox_usize(v_i_1494_);
lean_dec(v_i_1494_);
v_stop_boxed_1498_ = lean_unbox_usize(v_stop_1495_);
lean_dec(v_stop_1495_);
v_res_1499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9(v_as_1493_, v_i_boxed_1497_, v_stop_boxed_1498_, v_b_1496_);
lean_dec_ref(v_as_1493_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12___redArg(lean_object* v_hi_1500_, lean_object* v_pivot_1501_, lean_object* v_as_1502_, lean_object* v_i_1503_, lean_object* v_k_1504_){
_start:
{
uint8_t v___x_1505_; 
v___x_1505_ = lean_nat_dec_lt(v_k_1504_, v_hi_1500_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec(v_k_1504_);
v___x_1506_ = lean_array_fswap(v_as_1502_, v_i_1503_, v_hi_1500_);
v___x_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1507_, 0, v_i_1503_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
return v___x_1507_;
}
else
{
lean_object* v_snd_1508_; lean_object* v___x_1509_; lean_object* v_snd_1510_; uint8_t v___x_1511_; 
v_snd_1508_ = lean_ctor_get(v_pivot_1501_, 1);
v___x_1509_ = lean_array_fget_borrowed(v_as_1502_, v_k_1504_);
v_snd_1510_ = lean_ctor_get(v___x_1509_, 1);
v___x_1511_ = lean_nat_dec_lt(v_snd_1508_, v_snd_1510_);
if (v___x_1511_ == 0)
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_unsigned_to_nat(1u);
v___x_1513_ = lean_nat_add(v_k_1504_, v___x_1512_);
lean_dec(v_k_1504_);
v_k_1504_ = v___x_1513_;
goto _start;
}
else
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1515_ = lean_array_fswap(v_as_1502_, v_i_1503_, v_k_1504_);
v___x_1516_ = lean_unsigned_to_nat(1u);
v___x_1517_ = lean_nat_add(v_i_1503_, v___x_1516_);
lean_dec(v_i_1503_);
v___x_1518_ = lean_nat_add(v_k_1504_, v___x_1516_);
lean_dec(v_k_1504_);
v_as_1502_ = v___x_1515_;
v_i_1503_ = v___x_1517_;
v_k_1504_ = v___x_1518_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12___redArg___boxed(lean_object* v_hi_1520_, lean_object* v_pivot_1521_, lean_object* v_as_1522_, lean_object* v_i_1523_, lean_object* v_k_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12___redArg(v_hi_1520_, v_pivot_1521_, v_as_1522_, v_i_1523_, v_k_1524_);
lean_dec_ref(v_pivot_1521_);
lean_dec(v_hi_1520_);
return v_res_1525_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg___lam__0(lean_object* v_a_1526_, lean_object* v_b_1527_){
_start:
{
lean_object* v_snd_1528_; lean_object* v_snd_1529_; uint8_t v___x_1530_; 
v_snd_1528_ = lean_ctor_get(v_b_1527_, 1);
v_snd_1529_ = lean_ctor_get(v_a_1526_, 1);
v___x_1530_ = lean_nat_dec_lt(v_snd_1528_, v_snd_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg___lam__0___boxed(lean_object* v_a_1531_, lean_object* v_b_1532_){
_start:
{
uint8_t v_res_1533_; lean_object* v_r_1534_; 
v_res_1533_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg___lam__0(v_a_1531_, v_b_1532_);
lean_dec_ref(v_b_1532_);
lean_dec_ref(v_a_1531_);
v_r_1534_ = lean_box(v_res_1533_);
return v_r_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg(lean_object* v_n_1535_, lean_object* v_as_1536_, lean_object* v_lo_1537_, lean_object* v_hi_1538_){
_start:
{
lean_object* v___y_1540_; uint8_t v___x_1550_; 
v___x_1550_ = lean_nat_dec_lt(v_lo_1537_, v_hi_1538_);
if (v___x_1550_ == 0)
{
lean_dec(v_lo_1537_);
return v_as_1536_;
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v_mid_1553_; lean_object* v___y_1555_; lean_object* v___y_1561_; lean_object* v___x_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1551_ = lean_nat_add(v_lo_1537_, v_hi_1538_);
v___x_1552_ = lean_unsigned_to_nat(1u);
v_mid_1553_ = lean_nat_shiftr(v___x_1551_, v___x_1552_);
lean_dec(v___x_1551_);
v___x_1566_ = lean_array_fget_borrowed(v_as_1536_, v_mid_1553_);
v___x_1567_ = lean_array_fget_borrowed(v_as_1536_, v_lo_1537_);
v___x_1568_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg___lam__0(v___x_1566_, v___x_1567_);
if (v___x_1568_ == 0)
{
v___y_1561_ = v_as_1536_;
goto v___jp_1560_;
}
else
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_array_fswap(v_as_1536_, v_lo_1537_, v_mid_1553_);
v___y_1561_ = v___x_1569_;
goto v___jp_1560_;
}
v___jp_1554_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v___x_1556_ = lean_array_fget_borrowed(v___y_1555_, v_mid_1553_);
v___x_1557_ = lean_array_fget_borrowed(v___y_1555_, v_hi_1538_);
v___x_1558_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg___lam__0(v___x_1556_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_dec(v_mid_1553_);
v___y_1540_ = v___y_1555_;
goto v___jp_1539_;
}
else
{
lean_object* v___x_1559_; 
v___x_1559_ = lean_array_fswap(v___y_1555_, v_mid_1553_, v_hi_1538_);
lean_dec(v_mid_1553_);
v___y_1540_ = v___x_1559_;
goto v___jp_1539_;
}
}
v___jp_1560_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1562_ = lean_array_fget_borrowed(v___y_1561_, v_hi_1538_);
v___x_1563_ = lean_array_fget_borrowed(v___y_1561_, v_lo_1537_);
v___x_1564_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg___lam__0(v___x_1562_, v___x_1563_);
if (v___x_1564_ == 0)
{
v___y_1555_ = v___y_1561_;
goto v___jp_1554_;
}
else
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_array_fswap(v___y_1561_, v_lo_1537_, v_hi_1538_);
v___y_1555_ = v___x_1565_;
goto v___jp_1554_;
}
}
}
v___jp_1539_:
{
lean_object* v_pivot_1541_; lean_object* v___x_1542_; lean_object* v_fst_1543_; lean_object* v_snd_1544_; uint8_t v___x_1545_; 
v_pivot_1541_ = lean_array_fget(v___y_1540_, v_hi_1538_);
lean_inc_n(v_lo_1537_, 2);
v___x_1542_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12___redArg(v_hi_1538_, v_pivot_1541_, v___y_1540_, v_lo_1537_, v_lo_1537_);
lean_dec(v_pivot_1541_);
v_fst_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_fst_1543_);
v_snd_1544_ = lean_ctor_get(v___x_1542_, 1);
lean_inc(v_snd_1544_);
lean_dec_ref(v___x_1542_);
v___x_1545_ = lean_nat_dec_le(v_hi_1538_, v_fst_1543_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1546_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg(v_n_1535_, v_snd_1544_, v_lo_1537_, v_fst_1543_);
v___x_1547_ = lean_unsigned_to_nat(1u);
v___x_1548_ = lean_nat_add(v_fst_1543_, v___x_1547_);
lean_dec(v_fst_1543_);
v_as_1536_ = v___x_1546_;
v_lo_1537_ = v___x_1548_;
goto _start;
}
else
{
lean_dec(v_fst_1543_);
lean_dec(v_lo_1537_);
return v_snd_1544_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg___boxed(lean_object* v_n_1570_, lean_object* v_as_1571_, lean_object* v_lo_1572_, lean_object* v_hi_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg(v_n_1570_, v_as_1571_, v_lo_1572_, v_hi_1573_);
lean_dec(v_hi_1573_);
lean_dec(v_n_1570_);
return v_res_1574_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1582_ = lean_box(0);
v___x_1583_ = lean_unsigned_to_nat(16u);
v___x_1584_ = lean_mk_array(v___x_1583_, v___x_1582_);
return v___x_1584_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__4(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1585_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__3);
v___x_1586_ = lean_unsigned_to_nat(0u);
v___x_1587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
lean_ctor_set(v___x_1587_, 1, v___x_1585_);
return v___x_1587_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__5(void){
_start:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__4);
v___x_1589_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
lean_ctor_set(v___x_1589_, 2, v___x_1588_);
lean_ctor_set(v___x_1589_, 3, v___x_1588_);
return v___x_1589_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__6(void){
_start:
{
lean_object* v___x_1590_; double v___x_1591_; 
v___x_1590_ = lean_unsigned_to_nat(1000000000u);
v___x_1591_ = lean_float_of_nat(v___x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5(lean_object* v___x_1594_, lean_object* v___f_1595_, lean_object* v___f_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(v___x_1594_, v___y_1607_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_config_1610_; lean_object* v_a_1611_; lean_object* v_maxSteps_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___f_1621_; lean_object* v___f_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___f_1625_; lean_object* v___x_1626_; lean_object* v_target_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v_config_1610_ = lean_ctor_get(v___y_1597_, 0);
v_a_1611_ = lean_ctor_get(v___x_1609_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v___x_1609_, 1);
v_maxSteps_1612_ = lean_ctor_get(v_config_1610_, 1);
v___x_1613_ = lean_unsigned_to_nat(2u);
lean_inc_n(v_maxSteps_1612_, 2);
v___x_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1614_, 0, v_maxSteps_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = 1;
v___x_1616_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__0));
v___x_1617_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__2));
v___x_1618_ = lean_unsigned_to_nat(0u);
v___x_1619_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__5);
v___x_1620_ = lean_st_mk_ref(v___x_1619_);
lean_inc(v___x_1620_);
v___f_1621_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2___boxed), 15, 3);
lean_closure_set(v___f_1621_, 0, v___x_1620_);
lean_closure_set(v___f_1621_, 1, v_a_1611_);
lean_closure_set(v___f_1621_, 2, v___x_1617_);
v___f_1622_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3___boxed), 13, 2);
lean_closure_set(v___f_1622_, 0, v___x_1616_);
lean_closure_set(v___f_1622_, 1, v___f_1621_);
v___x_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___f_1595_);
lean_ctor_set(v___x_1623_, 1, v___f_1622_);
v___x_1624_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1624_, 0, v_maxSteps_1612_);
lean_ctor_set_uint8(v___x_1624_, sizeof(void*)*1, v___x_1615_);
v___f_1625_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4___boxed), 16, 4);
lean_closure_set(v___f_1625_, 0, v___x_1624_);
lean_closure_set(v___f_1625_, 1, v___x_1623_);
lean_closure_set(v___f_1625_, 2, v___x_1614_);
lean_closure_set(v___f_1625_, 3, v___x_1618_);
v___x_1626_ = lean_st_ref_get(v___y_1598_);
v_target_1627_ = lean_ctor_get(v___x_1626_, 2);
lean_inc_ref(v_target_1627_);
lean_dec(v___x_1626_);
v___x_1628_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_1627_);
lean_dec_ref(v_target_1627_);
v___x_1629_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg(v___x_1628_, v___f_1625_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___y_1632_; lean_object* v_toCold_1649_; lean_object* v_options_1650_; uint8_t v_hasTrace_1651_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
v_toCold_1649_ = lean_ctor_get(v___y_1606_, 0);
v_options_1650_ = lean_ctor_get(v_toCold_1649_, 2);
v_hasTrace_1651_ = lean_ctor_get_uint8(v_options_1650_, sizeof(void*)*1);
if (v_hasTrace_1651_ == 0)
{
lean_dec(v___x_1620_);
lean_dec_ref(v___f_1596_);
return v___x_1629_;
}
else
{
lean_object* v_inheritedTraceOptions_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___y_1659_; lean_object* v_a_1660_; lean_object* v___y_1673_; lean_object* v___y_1674_; lean_object* v___y_1675_; lean_object* v_a_1676_; 
v_inheritedTraceOptions_1652_ = lean_ctor_get(v_toCold_1649_, 11);
v___x_1653_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__9));
v___x_1654_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12);
v___x_1655_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1652_, v_options_1650_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_dec(v___x_1620_);
lean_dec_ref(v___f_1596_);
return v___x_1629_;
}
else
{
lean_object* v___x_1685_; lean_object* v___y_1687_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v___y_1725_; lean_object* v___y_1726_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1731_; lean_object* v_statistics_1737_; lean_object* v_size_1738_; lean_object* v_buckets_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; 
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1629_, 1);
v___x_1685_ = lean_st_ref_get(v___x_1620_);
lean_dec(v___x_1620_);
v_statistics_1737_ = lean_ctor_get(v___x_1685_, 3);
lean_inc_ref(v_statistics_1737_);
lean_dec(v___x_1685_);
v_size_1738_ = lean_ctor_get(v_statistics_1737_, 0);
lean_inc(v_size_1738_);
v_buckets_1739_ = lean_ctor_get(v_statistics_1737_, 1);
lean_inc_ref(v_buckets_1739_);
lean_dec_ref(v_statistics_1737_);
v___x_1740_ = lean_mk_empty_array_with_capacity(v_size_1738_);
lean_dec(v_size_1738_);
v___x_1741_ = lean_array_get_size(v_buckets_1739_);
v___x_1742_ = lean_nat_dec_lt(v___x_1618_, v___x_1741_);
if (v___x_1742_ == 0)
{
lean_dec_ref(v_buckets_1739_);
v___y_1731_ = v___x_1740_;
goto v___jp_1730_;
}
else
{
size_t v___x_1743_; size_t v___x_1744_; lean_object* v___x_1745_; 
v___x_1743_ = ((size_t)0ULL);
v___x_1744_ = lean_usize_of_nat(v___x_1741_);
v___x_1745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9(v_buckets_1739_, v___x_1743_, v___x_1744_, v___x_1740_);
lean_dec_ref(v_buckets_1739_);
v___y_1731_ = v___x_1745_;
goto v___jp_1730_;
}
v___jp_1686_:
{
lean_object* v___x_1688_; size_t v_sz_1689_; size_t v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v_a_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v___x_1688_ = lean_box(0);
v_sz_1689_ = lean_array_size(v___y_1687_);
v___x_1690_ = ((size_t)0ULL);
v___x_1691_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1));
v___x_1692_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg(v___y_1607_);
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref(v___x_1692_);
v___x_1694_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1695_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5(v_options_1650_, v___x_1694_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = lean_io_mono_nanos_now();
v___x_1697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3(v___y_1687_, v_sz_1689_, v___x_1690_, v___x_1688_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec_ref(v___y_1687_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v___x_1698_; 
lean_dec_ref_known(v___x_1697_, 1);
v___x_1698_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__7));
v___y_1657_ = v___x_1696_;
v___y_1658_ = v_a_1693_;
v___y_1659_ = v___x_1691_;
v_a_1660_ = v___x_1698_;
goto v___jp_1656_;
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
v_a_1699_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1697_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1697_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
lean_ctor_set_tag(v___x_1701_, 0);
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
v___y_1657_ = v___x_1696_;
v___y_1658_ = v_a_1693_;
v___y_1659_ = v___x_1691_;
v_a_1660_ = v___x_1704_;
goto v___jp_1656_;
}
}
}
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = lean_io_get_num_heartbeats();
v___x_1708_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3(v___y_1687_, v_sz_1689_, v___x_1690_, v___x_1688_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec_ref(v___y_1687_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v___x_1709_; 
lean_dec_ref_known(v___x_1708_, 1);
v___x_1709_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__7));
v___y_1673_ = v___x_1707_;
v___y_1674_ = v_a_1693_;
v___y_1675_ = v___x_1691_;
v_a_1676_ = v___x_1709_;
goto v___jp_1672_;
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
v_a_1710_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1708_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1708_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
lean_ctor_set_tag(v___x_1712_, 0);
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
v___y_1673_ = v___x_1707_;
v___y_1674_ = v_a_1693_;
v___y_1675_ = v___x_1691_;
v_a_1676_ = v___x_1715_;
goto v___jp_1672_;
}
}
}
}
}
v___jp_1718_:
{
lean_object* v___x_1723_; 
v___x_1723_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg(v___y_1721_, v___y_1720_, v___y_1719_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec(v___y_1721_);
v___y_1687_ = v___x_1723_;
goto v___jp_1686_;
}
v___jp_1724_:
{
uint8_t v___x_1729_; 
v___x_1729_ = lean_nat_dec_le(v___y_1728_, v___y_1726_);
if (v___x_1729_ == 0)
{
lean_dec(v___y_1726_);
lean_inc(v___y_1728_);
v___y_1719_ = v___y_1728_;
v___y_1720_ = v___y_1725_;
v___y_1721_ = v___y_1727_;
v___y_1722_ = v___y_1728_;
goto v___jp_1718_;
}
else
{
v___y_1719_ = v___y_1728_;
v___y_1720_ = v___y_1725_;
v___y_1721_ = v___y_1727_;
v___y_1722_ = v___y_1726_;
goto v___jp_1718_;
}
}
v___jp_1730_:
{
lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1732_ = lean_array_get_size(v___y_1731_);
v___x_1733_ = lean_nat_dec_eq(v___x_1732_, v___x_1618_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; uint8_t v___x_1736_; 
v___x_1734_ = lean_unsigned_to_nat(1u);
v___x_1735_ = lean_nat_sub(v___x_1732_, v___x_1734_);
v___x_1736_ = lean_nat_dec_le(v___x_1618_, v___x_1735_);
if (v___x_1736_ == 0)
{
lean_inc(v___x_1735_);
v___y_1725_ = v___y_1731_;
v___y_1726_ = v___x_1735_;
v___y_1727_ = v___x_1732_;
v___y_1728_ = v___x_1735_;
goto v___jp_1724_;
}
else
{
v___y_1725_ = v___y_1731_;
v___y_1726_ = v___x_1735_;
v___y_1727_ = v___x_1732_;
v___y_1728_ = v___x_1618_;
goto v___jp_1724_;
}
}
else
{
v___y_1687_ = v___y_1731_;
goto v___jp_1686_;
}
}
}
v___jp_1656_:
{
lean_object* v___x_1661_; double v___x_1662_; double v___x_1663_; double v___x_1664_; double v___x_1665_; double v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1661_ = lean_io_mono_nanos_now();
v___x_1662_ = lean_float_of_nat(v___y_1657_);
v___x_1663_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__6);
v___x_1664_ = lean_float_div(v___x_1662_, v___x_1663_);
v___x_1665_ = lean_float_of_nat(v___x_1661_);
v___x_1666_ = lean_float_div(v___x_1665_, v___x_1663_);
v___x_1667_ = lean_box_float(v___x_1664_);
v___x_1668_ = lean_box_float(v___x_1666_);
v___x_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1670_, 0, v_a_1660_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
lean_inc_ref(v___y_1659_);
v___x_1671_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(v___x_1653_, v___x_1615_, v___y_1659_, v_options_1650_, v___x_1655_, v___y_1658_, v___f_1596_, v___x_1670_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
v___y_1632_ = v___x_1671_;
goto v___jp_1631_;
}
v___jp_1672_:
{
lean_object* v___x_1677_; double v___x_1678_; double v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1677_ = lean_io_get_num_heartbeats();
v___x_1678_ = lean_float_of_nat(v___y_1673_);
v___x_1679_ = lean_float_of_nat(v___x_1677_);
v___x_1680_ = lean_box_float(v___x_1678_);
v___x_1681_ = lean_box_float(v___x_1679_);
v___x_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1680_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
v___x_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1683_, 0, v_a_1676_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
lean_inc_ref(v___y_1675_);
v___x_1684_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(v___x_1653_, v___x_1615_, v___y_1675_, v_options_1650_, v___x_1655_, v___y_1674_, v___f_1596_, v___x_1683_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
v___y_1632_ = v___x_1684_;
goto v___jp_1631_;
}
}
v___jp_1631_:
{
if (lean_obj_tag(v___y_1632_) == 0)
{
lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1639_; 
v_isSharedCheck_1639_ = !lean_is_exclusive(v___y_1632_);
if (v_isSharedCheck_1639_ == 0)
{
lean_object* v_unused_1640_; 
v_unused_1640_ = lean_ctor_get(v___y_1632_, 0);
lean_dec(v_unused_1640_);
v___x_1634_ = v___y_1632_;
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
else
{
lean_dec(v___y_1632_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1639_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1637_; 
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v_a_1630_);
v___x_1637_ = v___x_1634_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_a_1630_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
else
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
lean_dec(v_a_1630_);
v_a_1641_ = lean_ctor_get(v___y_1632_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___y_1632_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___y_1632_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___y_1632_);
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
}
else
{
lean_dec(v___x_1620_);
lean_dec_ref(v___f_1596_);
return v___x_1629_;
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec_ref(v___f_1596_);
lean_dec_ref(v___f_1595_);
v_a_1746_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1609_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1609_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___boxed(lean_object* v___x_1754_, lean_object* v___f_1755_, lean_object* v___f_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5(v___x_1754_, v___f_1755_, v___f_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec_ref(v___x_1754_);
return v_res_1769_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4(void){
_start:
{
lean_object* v___f_1775_; lean_object* v___f_1776_; lean_object* v___x_1777_; lean_object* v___f_1778_; 
v___f_1775_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__0));
v___f_1776_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__1));
v___x_1777_ = l_Lean_Meta_Tactic_BVDecide_bvNormalizeExt;
v___f_1778_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___boxed), 15, 3);
lean_closure_set(v___f_1778_, 0, v___x_1777_);
lean_closure_set(v___f_1778_, 1, v___f_1776_);
lean_closure_set(v___f_1778_, 2, v___f_1775_);
return v___f_1778_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__5(void){
_start:
{
lean_object* v___f_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___f_1779_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4);
v___x_1780_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__3));
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
lean_ctor_set(v___x_1781_, 1, v___f_1779_);
return v___x_1781_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass(void){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__5);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0(lean_object* v_cls_1783_, lean_object* v_msg_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v_cls_1783_, v_msg_1784_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___boxed(lean_object* v_cls_1798_, lean_object* v_msg_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0(v_cls_1798_, v_msg_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1(lean_object* v_upperBound_1813_, lean_object* v___x_1814_, lean_object* v___x_1815_, lean_object* v___x_1816_, lean_object* v___x_1817_, lean_object* v_inst_1818_, lean_object* v_R_1819_, lean_object* v_a_1820_, lean_object* v_b_1821_, lean_object* v_c_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v_upperBound_1813_, v___x_1814_, v___x_1815_, v___x_1816_, v___x_1817_, v_a_1820_, v_b_1821_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_1836_ = _args[0];
lean_object* v___x_1837_ = _args[1];
lean_object* v___x_1838_ = _args[2];
lean_object* v___x_1839_ = _args[3];
lean_object* v___x_1840_ = _args[4];
lean_object* v_inst_1841_ = _args[5];
lean_object* v_R_1842_ = _args[6];
lean_object* v_a_1843_ = _args[7];
lean_object* v_b_1844_ = _args[8];
lean_object* v_c_1845_ = _args[9];
lean_object* v___y_1846_ = _args[10];
lean_object* v___y_1847_ = _args[11];
lean_object* v___y_1848_ = _args[12];
lean_object* v___y_1849_ = _args[13];
lean_object* v___y_1850_ = _args[14];
lean_object* v___y_1851_ = _args[15];
lean_object* v___y_1852_ = _args[16];
lean_object* v___y_1853_ = _args[17];
lean_object* v___y_1854_ = _args[18];
lean_object* v___y_1855_ = _args[19];
lean_object* v___y_1856_ = _args[20];
lean_object* v___y_1857_ = _args[21];
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1(v_upperBound_1836_, v___x_1837_, v___x_1838_, v___x_1839_, v___x_1840_, v_inst_1841_, v_R_1842_, v_a_1843_, v_b_1844_, v_c_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec_ref(v___x_1837_);
lean_dec(v_upperBound_1836_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8(lean_object* v_00_u03b1_1859_, lean_object* v_x_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8___redArg(v_x_1860_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1874_, lean_object* v_x_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8(v_00_u03b1_1874_, v_x_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
lean_dec(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7(lean_object* v_n_1889_, lean_object* v_as_1890_, lean_object* v_lo_1891_, lean_object* v_hi_1892_, lean_object* v_w_1893_, lean_object* v_hlo_1894_, lean_object* v_hhi_1895_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg(v_n_1889_, v_as_1890_, v_lo_1891_, v_hi_1892_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___boxed(lean_object* v_n_1897_, lean_object* v_as_1898_, lean_object* v_lo_1899_, lean_object* v_hi_1900_, lean_object* v_w_1901_, lean_object* v_hlo_1902_, lean_object* v_hhi_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7(v_n_1897_, v_as_1898_, v_lo_1899_, v_hi_1900_, v_w_1901_, v_hlo_1902_, v_hhi_1903_);
lean_dec(v_hi_1900_);
lean_dec(v_n_1897_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7(lean_object* v_oldTraces_1905_, lean_object* v_data_1906_, lean_object* v_ref_1907_, lean_object* v_msg_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7___redArg(v_oldTraces_1905_, v_data_1906_, v_ref_1907_, v_msg_1908_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7___boxed(lean_object* v_oldTraces_1922_, lean_object* v_data_1923_, lean_object* v_ref_1924_, lean_object* v_msg_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7(v_oldTraces_1922_, v_data_1923_, v_ref_1924_, v_msg_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12(lean_object* v_n_1939_, lean_object* v_lo_1940_, lean_object* v_hi_1941_, lean_object* v_hhi_1942_, lean_object* v_pivot_1943_, lean_object* v_as_1944_, lean_object* v_i_1945_, lean_object* v_k_1946_, lean_object* v_ilo_1947_, lean_object* v_ik_1948_, lean_object* v_w_1949_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12___redArg(v_hi_1941_, v_pivot_1943_, v_as_1944_, v_i_1945_, v_k_1946_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12___boxed(lean_object* v_n_1951_, lean_object* v_lo_1952_, lean_object* v_hi_1953_, lean_object* v_hhi_1954_, lean_object* v_pivot_1955_, lean_object* v_as_1956_, lean_object* v_i_1957_, lean_object* v_k_1958_, lean_object* v_ilo_1959_, lean_object* v_ik_1960_, lean_object* v_w_1961_){
_start:
{
lean_object* v_res_1962_; 
v_res_1962_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12(v_n_1951_, v_lo_1952_, v_hi_1953_, v_hhi_1954_, v_pivot_1955_, v_as_1956_, v_i_1957_, v_k_1958_, v_ilo_1959_, v_ik_1960_, v_w_1961_);
lean_dec_ref(v_pivot_1955_);
lean_dec(v_hi_1953_);
lean_dec(v_lo_1952_);
lean_dec(v_n_1951_);
return v_res_1962_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_EvalGround(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_EvalGround(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass = _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_EvalGround(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_ControlFlow(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_EvalGround(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite(builtin);
}
#ifdef __cplusplus
}
#endif

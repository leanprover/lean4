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
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
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
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v___y_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v___y_9_ = stack[8].m_obj;
lean_object* v___y_10_ = stack[9].m_obj;
lean_object* v___y_11_ = stack[10].m_obj;
lean_object* v___y_12_ = stack[11].m_obj;
lean_object* v_res_15_;
v_res_15_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0(v_x_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0___boxed(lean_object* v_x_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0(v_x_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_29_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg(lean_object* v_mvarId_30_, lean_object* v_x_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v___f_44_; lean_object* v___x_45_; 
lean_inc(v___y_38_);
lean_inc_ref(v___y_37_);
lean_inc(v___y_36_);
lean_inc_ref(v___y_35_);
lean_inc(v___y_34_);
lean_inc(v___y_33_);
lean_inc_ref(v___y_32_);
v___f_44_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_44_, 0, v_x_31_);
lean_closure_set(v___f_44_, 1, v___y_32_);
lean_closure_set(v___f_44_, 2, v___y_33_);
lean_closure_set(v___f_44_, 3, v___y_34_);
lean_closure_set(v___f_44_, 4, v___y_35_);
lean_closure_set(v___f_44_, 5, v___y_36_);
lean_closure_set(v___f_44_, 6, v___y_37_);
lean_closure_set(v___f_44_, 7, v___y_38_);
v___x_45_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_30_, v___f_44_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
if (lean_obj_tag(v___x_45_) == 0)
{
return v___x_45_;
}
else
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_53_; 
v_a_46_ = lean_ctor_get(v___x_45_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_53_ == 0)
{
v___x_48_ = v___x_45_;
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_45_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_51_; 
if (v_isShared_49_ == 0)
{
v___x_51_ = v___x_48_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_a_46_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
return v___x_51_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_30_ = stack[0].m_obj;
lean_object* v_x_31_ = stack[1].m_obj;
lean_object* v___y_32_ = stack[2].m_obj;
lean_object* v___y_33_ = stack[3].m_obj;
lean_object* v___y_34_ = stack[4].m_obj;
lean_object* v___y_35_ = stack[5].m_obj;
lean_object* v___y_36_ = stack[6].m_obj;
lean_object* v___y_37_ = stack[7].m_obj;
lean_object* v___y_38_ = stack[8].m_obj;
lean_object* v___y_39_ = stack[9].m_obj;
lean_object* v___y_40_ = stack[10].m_obj;
lean_object* v___y_41_ = stack[11].m_obj;
lean_object* v___y_42_ = stack[12].m_obj;
lean_object* v_res_54_;
v_res_54_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg(v_mvarId_30_, v_x_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
stack->m_obj
 = v_res_54_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___boxed(lean_object* v_mvarId_55_, lean_object* v_x_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg(v_mvarId_55_, v_x_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
lean_dec(v___y_65_);
lean_dec_ref(v___y_64_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
return v_res_69_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2(lean_object* v_00_u03b1_70_, lean_object* v_mvarId_71_, lean_object* v_x_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg(v_mvarId_71_, v_x_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
return v___x_85_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_71_ = stack[1].m_obj;
lean_object* v_x_72_ = stack[2].m_obj;
lean_object* v___y_73_ = stack[3].m_obj;
lean_object* v___y_74_ = stack[4].m_obj;
lean_object* v___y_75_ = stack[5].m_obj;
lean_object* v___y_76_ = stack[6].m_obj;
lean_object* v___y_77_ = stack[7].m_obj;
lean_object* v___y_78_ = stack[8].m_obj;
lean_object* v___y_79_ = stack[9].m_obj;
lean_object* v___y_80_ = stack[10].m_obj;
lean_object* v___y_81_ = stack[11].m_obj;
lean_object* v___y_82_ = stack[12].m_obj;
lean_object* v___y_83_ = stack[13].m_obj;
lean_object* v_res_86_;
v_res_86_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2(lean_box(0), v_mvarId_71_, v_x_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___boxed(lean_object* v_00_u03b1_87_, lean_object* v_mvarId_88_, lean_object* v_x_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2(v_00_u03b1_87_, v_mvarId_88_, v_x_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
return v_res_102_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_unsigned_to_nat(32u);
v___x_104_ = lean_mk_empty_array_with_capacity(v___x_103_);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_106_ = ((size_t)5ULL);
v___x_107_ = lean_unsigned_to_nat(0u);
v___x_108_ = lean_unsigned_to_nat(32u);
v___x_109_ = lean_mk_empty_array_with_capacity(v___x_108_);
v___x_110_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___closed__0);
v___x_111_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v___x_109_);
lean_ctor_set(v___x_111_, 2, v___x_107_);
lean_ctor_set(v___x_111_, 3, v___x_107_);
lean_ctor_set_usize(v___x_111_, 4, v___x_106_);
return v___x_111_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg(lean_object* v___y_112_){
_start:
{
lean_object* v___x_114_; lean_object* v_traceState_115_; lean_object* v_traces_116_; lean_object* v___x_117_; lean_object* v_traceState_118_; lean_object* v_env_119_; lean_object* v_nextMacroScope_120_; lean_object* v_ngen_121_; lean_object* v_auxDeclNGen_122_; lean_object* v_cache_123_; lean_object* v_recordedDeps_124_; lean_object* v_messages_125_; lean_object* v_infoState_126_; lean_object* v_snapshotTasks_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_146_; 
v___x_114_ = lean_st_ref_get(v___y_112_);
v_traceState_115_ = lean_ctor_get(v___x_114_, 4);
lean_inc_ref(v_traceState_115_);
lean_dec(v___x_114_);
v_traces_116_ = lean_ctor_get(v_traceState_115_, 0);
lean_inc_ref(v_traces_116_);
lean_dec_ref(v_traceState_115_);
v___x_117_ = lean_st_ref_take(v___y_112_);
v_traceState_118_ = lean_ctor_get(v___x_117_, 4);
v_env_119_ = lean_ctor_get(v___x_117_, 0);
v_nextMacroScope_120_ = lean_ctor_get(v___x_117_, 1);
v_ngen_121_ = lean_ctor_get(v___x_117_, 2);
v_auxDeclNGen_122_ = lean_ctor_get(v___x_117_, 3);
v_cache_123_ = lean_ctor_get(v___x_117_, 5);
v_recordedDeps_124_ = lean_ctor_get(v___x_117_, 6);
v_messages_125_ = lean_ctor_get(v___x_117_, 7);
v_infoState_126_ = lean_ctor_get(v___x_117_, 8);
v_snapshotTasks_127_ = lean_ctor_get(v___x_117_, 9);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_146_ == 0)
{
v___x_129_ = v___x_117_;
v_isShared_130_ = v_isSharedCheck_146_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_snapshotTasks_127_);
lean_inc(v_infoState_126_);
lean_inc(v_messages_125_);
lean_inc(v_recordedDeps_124_);
lean_inc(v_cache_123_);
lean_inc(v_traceState_118_);
lean_inc(v_auxDeclNGen_122_);
lean_inc(v_ngen_121_);
lean_inc(v_nextMacroScope_120_);
lean_inc(v_env_119_);
lean_dec(v___x_117_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_146_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
uint64_t v_tid_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_144_; 
v_tid_131_ = lean_ctor_get_uint64(v_traceState_118_, sizeof(void*)*1);
v_isSharedCheck_144_ = !lean_is_exclusive(v_traceState_118_);
if (v_isSharedCheck_144_ == 0)
{
lean_object* v_unused_145_; 
v_unused_145_ = lean_ctor_get(v_traceState_118_, 0);
lean_dec(v_unused_145_);
v___x_133_ = v_traceState_118_;
v_isShared_134_ = v_isSharedCheck_144_;
goto v_resetjp_132_;
}
else
{
lean_dec(v_traceState_118_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_144_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_135_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___closed__1);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_135_);
v___x_137_ = v___x_133_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_135_);
lean_ctor_set_uint64(v_reuseFailAlloc_143_, sizeof(void*)*1, v_tid_131_);
v___x_137_ = v_reuseFailAlloc_143_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_139_; 
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 4, v___x_137_);
v___x_139_ = v___x_129_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_env_119_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_nextMacroScope_120_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v_ngen_121_);
lean_ctor_set(v_reuseFailAlloc_142_, 3, v_auxDeclNGen_122_);
lean_ctor_set(v_reuseFailAlloc_142_, 4, v___x_137_);
lean_ctor_set(v_reuseFailAlloc_142_, 5, v_cache_123_);
lean_ctor_set(v_reuseFailAlloc_142_, 6, v_recordedDeps_124_);
lean_ctor_set(v_reuseFailAlloc_142_, 7, v_messages_125_);
lean_ctor_set(v_reuseFailAlloc_142_, 8, v_infoState_126_);
lean_ctor_set(v_reuseFailAlloc_142_, 9, v_snapshotTasks_127_);
v___x_139_ = v_reuseFailAlloc_142_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_st_ref_put(v___y_112_, v___x_139_);
v___x_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_141_, 0, v_traces_116_);
return v___x_141_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_112_ = stack[0].m_obj;
lean_object* v_res_147_;
v_res_147_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg(v___y_112_);
stack->m_obj
 = v_res_147_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg___boxed(lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg(v___y_148_);
lean_dec(v___y_148_);
return v_res_150_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4(lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg(v___y_161_);
return v___x_163_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_151_ = stack[0].m_obj;
lean_object* v___y_152_ = stack[1].m_obj;
lean_object* v___y_153_ = stack[2].m_obj;
lean_object* v___y_154_ = stack[3].m_obj;
lean_object* v___y_155_ = stack[4].m_obj;
lean_object* v___y_156_ = stack[5].m_obj;
lean_object* v___y_157_ = stack[6].m_obj;
lean_object* v___y_158_ = stack[7].m_obj;
lean_object* v___y_159_ = stack[8].m_obj;
lean_object* v___y_160_ = stack[9].m_obj;
lean_object* v___y_161_ = stack[10].m_obj;
lean_object* v_res_164_;
v_res_164_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4(v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
stack->m_obj
 = v_res_164_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___boxed(lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4(v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
return v_res_177_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5(lean_object* v_opts_178_, lean_object* v_opt_179_){
_start:
{
lean_object* v_name_180_; lean_object* v_defValue_181_; lean_object* v_map_182_; lean_object* v___x_183_; 
v_name_180_ = lean_ctor_get(v_opt_179_, 0);
v_defValue_181_ = lean_ctor_get(v_opt_179_, 1);
v_map_182_ = lean_ctor_get(v_opts_178_, 0);
v___x_183_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_182_, v_name_180_);
if (lean_obj_tag(v___x_183_) == 0)
{
uint8_t v___x_184_; 
v___x_184_ = lean_unbox(v_defValue_181_);
return v___x_184_;
}
else
{
lean_object* v_val_185_; 
v_val_185_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_val_185_);
lean_dec_ref_known(v___x_183_, 1);
if (lean_obj_tag(v_val_185_) == 1)
{
uint8_t v_v_186_; 
v_v_186_ = lean_ctor_get_uint8(v_val_185_, 0);
lean_dec_ref_known(v_val_185_, 0);
return v_v_186_;
}
else
{
uint8_t v___x_187_; 
lean_dec(v_val_185_);
v___x_187_ = lean_unbox(v_defValue_181_);
return v___x_187_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_178_ = stack[0].m_obj;
lean_object* v_opt_179_ = stack[1].m_obj;
uint8_t v_res_188_;
v_res_188_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5(v_opts_178_, v_opt_179_);
stack->m_num = v_res_188_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___boxed(lean_object* v_opts_189_, lean_object* v_opt_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5(v_opts_189_, v_opt_190_);
lean_dec_ref(v_opt_190_);
lean_dec_ref(v_opts_189_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__2(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__1));
v___x_197_ = l_Lean_MessageData_ofFormat(v___x_196_);
return v___x_197_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(lean_object* v_x_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__2);
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_198_ = stack[0].m_obj;
lean_object* v___y_199_ = stack[1].m_obj;
lean_object* v___y_200_ = stack[2].m_obj;
lean_object* v___y_201_ = stack[3].m_obj;
lean_object* v___y_202_ = stack[4].m_obj;
lean_object* v___y_203_ = stack[5].m_obj;
lean_object* v___y_204_ = stack[6].m_obj;
lean_object* v___y_205_ = stack[7].m_obj;
lean_object* v___y_206_ = stack[8].m_obj;
lean_object* v___y_207_ = stack[9].m_obj;
lean_object* v___y_208_ = stack[10].m_obj;
lean_object* v___y_209_ = stack[11].m_obj;
lean_object* v_res_213_;
v_res_213_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(v_x_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
stack->m_obj
 = v_res_213_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___boxed(lean_object* v_x_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(v_x_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec_ref(v_x_214_);
return v_res_227_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1(lean_object* v_e_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Meta_Sym_Simp_simpControl(v_e_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_270_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_270_ == 0)
{
v___x_242_ = v___x_239_;
v_isShared_243_ = v_isSharedCheck_270_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_239_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_270_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
if (lean_obj_tag(v_a_240_) == 0)
{
uint8_t v_contextDependent_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_255_; 
v_contextDependent_244_ = lean_ctor_get_uint8(v_a_240_, 1);
v_isSharedCheck_255_ = !lean_is_exclusive(v_a_240_);
if (v_isSharedCheck_255_ == 0)
{
v___x_246_ = v_a_240_;
v_isShared_247_ = v_isSharedCheck_255_;
goto v_resetjp_245_;
}
else
{
lean_dec(v_a_240_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_255_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
uint8_t v___x_248_; lean_object* v___x_250_; 
v___x_248_ = 0;
if (v_isShared_247_ == 0)
{
v___x_250_ = v___x_246_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_254_, 1, v_contextDependent_244_);
v___x_250_ = v_reuseFailAlloc_254_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_252_; 
lean_ctor_set_uint8(v___x_250_, 0, v___x_248_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 0, v___x_250_);
v___x_252_ = v___x_242_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
else
{
lean_object* v_e_x27_256_; lean_object* v_proof_257_; uint8_t v_contextDependent_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_269_; 
v_e_x27_256_ = lean_ctor_get(v_a_240_, 0);
v_proof_257_ = lean_ctor_get(v_a_240_, 1);
v_contextDependent_258_ = lean_ctor_get_uint8(v_a_240_, sizeof(void*)*2 + 1);
v_isSharedCheck_269_ = !lean_is_exclusive(v_a_240_);
if (v_isSharedCheck_269_ == 0)
{
v___x_260_ = v_a_240_;
v_isShared_261_ = v_isSharedCheck_269_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_proof_257_);
lean_inc(v_e_x27_256_);
lean_dec(v_a_240_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_269_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
uint8_t v___x_262_; lean_object* v___x_264_; 
v___x_262_ = 0;
if (v_isShared_261_ == 0)
{
v___x_264_ = v___x_260_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_e_x27_256_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_proof_257_);
lean_ctor_set_uint8(v_reuseFailAlloc_268_, sizeof(void*)*2 + 1, v_contextDependent_258_);
v___x_264_ = v_reuseFailAlloc_268_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_266_; 
lean_ctor_set_uint8(v___x_264_, sizeof(void*)*2, v___x_262_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 0, v___x_264_);
v___x_266_ = v___x_242_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
}
else
{
return v___x_239_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_228_ = stack[0].m_obj;
lean_object* v___y_229_ = stack[1].m_obj;
lean_object* v___y_230_ = stack[2].m_obj;
lean_object* v___y_231_ = stack[3].m_obj;
lean_object* v___y_232_ = stack[4].m_obj;
lean_object* v___y_233_ = stack[5].m_obj;
lean_object* v___y_234_ = stack[6].m_obj;
lean_object* v___y_235_ = stack[7].m_obj;
lean_object* v___y_236_ = stack[8].m_obj;
lean_object* v___y_237_ = stack[9].m_obj;
lean_object* v_res_271_;
v_res_271_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1(v_e_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
stack->m_obj
 = v_res_271_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___boxed(lean_object* v_e_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1(v_e_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
return v_res_283_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2(lean_object* v_val_284_, lean_object* v_a_285_, lean_object* v___x_286_, lean_object* v_x_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v___x_299_; 
lean_inc_ref(v___y_288_);
v___x_299_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteSimproc(v_val_284_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_300_);
if (lean_obj_tag(v_a_300_) == 0)
{
uint8_t v_done_301_; 
v_done_301_ = lean_ctor_get_uint8(v_a_300_, 0);
if (v_done_301_ == 0)
{
uint8_t v_contextDependent_302_; lean_object* v___x_303_; 
lean_dec_ref_known(v___x_299_, 1);
v_contextDependent_302_ = lean_ctor_get_uint8(v_a_300_, 1);
lean_dec_ref_known(v_a_300_, 0);
v___x_303_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_285_, v___x_286_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; uint8_t v___y_306_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
if (v_contextDependent_302_ == 0)
{
return v___x_303_;
}
else
{
if (lean_obj_tag(v_a_304_) == 0)
{
uint8_t v_contextDependent_316_; 
v_contextDependent_316_ = lean_ctor_get_uint8(v_a_304_, 1);
v___y_306_ = v_contextDependent_316_;
goto v___jp_305_;
}
else
{
uint8_t v_contextDependent_317_; 
v_contextDependent_317_ = lean_ctor_get_uint8(v_a_304_, sizeof(void*)*2 + 1);
v___y_306_ = v_contextDependent_317_;
goto v___jp_305_;
}
}
v___jp_305_:
{
if (v___y_306_ == 0)
{
lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_314_; 
lean_inc(v_a_304_);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_314_ == 0)
{
lean_object* v_unused_315_; 
v_unused_315_ = lean_ctor_get(v___x_303_, 0);
lean_dec(v_unused_315_);
v___x_308_ = v___x_303_;
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
else
{
lean_dec(v___x_303_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_314_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_304_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_310_);
v___x_312_ = v___x_308_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
else
{
return v___x_303_;
}
}
}
else
{
return v___x_303_;
}
}
else
{
lean_dec_ref_known(v_a_300_, 0);
lean_dec_ref(v___y_288_);
lean_dec_ref(v___x_286_);
return v___x_299_;
}
}
else
{
uint8_t v_done_318_; 
v_done_318_ = lean_ctor_get_uint8(v_a_300_, sizeof(void*)*2);
if (v_done_318_ == 0)
{
lean_object* v_e_x27_319_; lean_object* v_proof_320_; uint8_t v_contextDependent_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_371_; 
lean_dec_ref_known(v___x_299_, 1);
v_e_x27_319_ = lean_ctor_get(v_a_300_, 0);
v_proof_320_ = lean_ctor_get(v_a_300_, 1);
v_contextDependent_321_ = lean_ctor_get_uint8(v_a_300_, sizeof(void*)*2 + 1);
v_isSharedCheck_371_ = !lean_is_exclusive(v_a_300_);
if (v_isSharedCheck_371_ == 0)
{
v___x_323_ = v_a_300_;
v_isShared_324_ = v_isSharedCheck_371_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_proof_320_);
lean_inc(v_e_x27_319_);
lean_dec(v_a_300_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_371_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; 
lean_inc_ref(v_e_x27_319_);
v___x_325_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_285_, v___x_286_, v_e_x27_319_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_370_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_370_ == 0)
{
v___x_328_ = v___x_325_;
v_isShared_329_ = v_isSharedCheck_370_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_370_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
if (lean_obj_tag(v_a_326_) == 0)
{
uint8_t v_done_330_; uint8_t v_contextDependent_331_; uint8_t v___y_333_; 
lean_dec_ref(v___y_288_);
v_done_330_ = lean_ctor_get_uint8(v_a_326_, 0);
v_contextDependent_331_ = lean_ctor_get_uint8(v_a_326_, 1);
lean_dec_ref_known(v_a_326_, 0);
if (v_contextDependent_321_ == 0)
{
v___y_333_ = v_contextDependent_331_;
goto v___jp_332_;
}
else
{
v___y_333_ = v_contextDependent_321_;
goto v___jp_332_;
}
v___jp_332_:
{
lean_object* v___x_335_; 
if (v_isShared_324_ == 0)
{
v___x_335_ = v___x_323_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_e_x27_319_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_proof_320_);
v___x_335_ = v_reuseFailAlloc_339_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_337_; 
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*2, v_done_330_);
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*2 + 1, v___y_333_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_335_);
v___x_337_ = v___x_328_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_335_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
else
{
lean_object* v_e_x27_340_; lean_object* v_proof_341_; uint8_t v_done_342_; uint8_t v_contextDependent_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_369_; 
lean_del_object(v___x_328_);
lean_del_object(v___x_323_);
v_e_x27_340_ = lean_ctor_get(v_a_326_, 0);
v_proof_341_ = lean_ctor_get(v_a_326_, 1);
v_done_342_ = lean_ctor_get_uint8(v_a_326_, sizeof(void*)*2);
v_contextDependent_343_ = lean_ctor_get_uint8(v_a_326_, sizeof(void*)*2 + 1);
v_isSharedCheck_369_ = !lean_is_exclusive(v_a_326_);
if (v_isSharedCheck_369_ == 0)
{
v___x_345_ = v_a_326_;
v_isShared_346_ = v_isSharedCheck_369_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_proof_341_);
lean_inc(v_e_x27_340_);
lean_dec(v_a_326_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_369_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; 
lean_inc_ref(v_e_x27_340_);
v___x_347_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_288_, v_e_x27_319_, v_proof_320_, v_e_x27_340_, v_proof_341_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_360_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_360_ == 0)
{
v___x_350_ = v___x_347_;
v_isShared_351_ = v_isSharedCheck_360_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_360_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
uint8_t v___y_353_; 
if (v_contextDependent_321_ == 0)
{
v___y_353_ = v_contextDependent_343_;
goto v___jp_352_;
}
else
{
v___y_353_ = v_contextDependent_321_;
goto v___jp_352_;
}
v___jp_352_:
{
lean_object* v___x_355_; 
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 1, v_a_348_);
v___x_355_ = v___x_345_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_e_x27_340_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_a_348_);
lean_ctor_set_uint8(v_reuseFailAlloc_359_, sizeof(void*)*2, v_done_342_);
v___x_355_ = v_reuseFailAlloc_359_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_357_; 
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*2 + 1, v___y_353_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_355_);
v___x_357_ = v___x_350_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
lean_del_object(v___x_345_);
lean_dec_ref(v_e_x27_340_);
v_a_361_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_347_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_347_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_323_);
lean_dec_ref(v_proof_320_);
lean_dec_ref(v_e_x27_319_);
lean_dec_ref(v___y_288_);
return v___x_325_;
}
}
}
else
{
lean_dec_ref_known(v_a_300_, 2);
lean_dec_ref(v___y_288_);
lean_dec_ref(v___x_286_);
return v___x_299_;
}
}
}
else
{
lean_dec_ref(v___y_288_);
lean_dec_ref(v___x_286_);
return v___x_299_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_284_ = stack[0].m_obj;
lean_object* v_a_285_ = stack[1].m_obj;
lean_object* v___x_286_ = stack[2].m_obj;
lean_object* v_x_287_ = stack[3].m_obj;
lean_object* v___y_288_ = stack[4].m_obj;
lean_object* v___y_289_ = stack[5].m_obj;
lean_object* v___y_290_ = stack[6].m_obj;
lean_object* v___y_291_ = stack[7].m_obj;
lean_object* v___y_292_ = stack[8].m_obj;
lean_object* v___y_293_ = stack[9].m_obj;
lean_object* v___y_294_ = stack[10].m_obj;
lean_object* v___y_295_ = stack[11].m_obj;
lean_object* v___y_296_ = stack[12].m_obj;
lean_object* v___y_297_ = stack[13].m_obj;
lean_object* v_res_372_;
v_res_372_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2(v_val_284_, v_a_285_, v___x_286_, v_x_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
stack->m_obj
 = v_res_372_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2___boxed(lean_object* v_val_373_, lean_object* v_a_374_, lean_object* v___x_375_, lean_object* v_x_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2(v_val_373_, v_a_374_, v___x_375_, v_x_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v_a_374_);
lean_dec(v_val_373_);
return v_res_388_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3(lean_object* v___x_389_, lean_object* v___f_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_box(0);
lean_inc_ref(v___y_391_);
v___x_403_ = l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(v___y_391_, v___x_389_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_a_404_);
if (lean_obj_tag(v_a_404_) == 0)
{
uint8_t v_done_405_; 
v_done_405_ = lean_ctor_get_uint8(v_a_404_, 0);
if (v_done_405_ == 0)
{
uint8_t v_contextDependent_406_; lean_object* v___x_407_; 
lean_dec_ref_known(v___x_403_, 1);
v_contextDependent_406_ = lean_ctor_get_uint8(v_a_404_, 1);
lean_dec_ref_known(v_a_404_, 0);
v___x_407_ = lean_apply_12(v___f_390_, v___x_402_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, lean_box(0));
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; uint8_t v___y_410_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
if (v_contextDependent_406_ == 0)
{
lean_dec(v_a_408_);
return v___x_407_;
}
else
{
if (lean_obj_tag(v_a_408_) == 0)
{
uint8_t v_contextDependent_420_; 
v_contextDependent_420_ = lean_ctor_get_uint8(v_a_408_, 1);
v___y_410_ = v_contextDependent_420_;
goto v___jp_409_;
}
else
{
uint8_t v_contextDependent_421_; 
v_contextDependent_421_ = lean_ctor_get_uint8(v_a_408_, sizeof(void*)*2 + 1);
v___y_410_ = v_contextDependent_421_;
goto v___jp_409_;
}
}
v___jp_409_:
{
if (v___y_410_ == 0)
{
lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_418_; 
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; 
v_unused_419_ = lean_ctor_get(v___x_407_, 0);
lean_dec(v_unused_419_);
v___x_412_ = v___x_407_;
v_isShared_413_ = v_isSharedCheck_418_;
goto v_resetjp_411_;
}
else
{
lean_dec(v___x_407_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_418_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_408_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_414_);
v___x_416_ = v___x_412_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
else
{
lean_dec(v_a_408_);
return v___x_407_;
}
}
}
else
{
return v___x_407_;
}
}
else
{
lean_dec_ref_known(v_a_404_, 0);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec_ref(v___f_390_);
return v___x_403_;
}
}
else
{
uint8_t v_done_422_; 
v_done_422_ = lean_ctor_get_uint8(v_a_404_, sizeof(void*)*2);
if (v_done_422_ == 0)
{
lean_object* v_e_x27_423_; lean_object* v_proof_424_; uint8_t v_contextDependent_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_475_; 
lean_dec_ref_known(v___x_403_, 1);
v_e_x27_423_ = lean_ctor_get(v_a_404_, 0);
v_proof_424_ = lean_ctor_get(v_a_404_, 1);
v_contextDependent_425_ = lean_ctor_get_uint8(v_a_404_, sizeof(void*)*2 + 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v_a_404_);
if (v_isSharedCheck_475_ == 0)
{
v___x_427_ = v_a_404_;
v_isShared_428_ = v_isSharedCheck_475_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_proof_424_);
lean_inc(v_e_x27_423_);
lean_dec(v_a_404_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_475_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; 
lean_inc(v___y_400_);
lean_inc_ref(v___y_399_);
lean_inc(v___y_398_);
lean_inc_ref(v___y_397_);
lean_inc(v___y_396_);
lean_inc_ref(v___y_395_);
lean_inc_ref(v_e_x27_423_);
v___x_429_ = lean_apply_12(v___f_390_, v___x_402_, v_e_x27_423_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, lean_box(0));
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_474_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_474_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_474_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_474_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
if (lean_obj_tag(v_a_430_) == 0)
{
uint8_t v_done_434_; uint8_t v_contextDependent_435_; uint8_t v___y_437_; 
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec_ref(v___y_391_);
v_done_434_ = lean_ctor_get_uint8(v_a_430_, 0);
v_contextDependent_435_ = lean_ctor_get_uint8(v_a_430_, 1);
lean_dec_ref_known(v_a_430_, 0);
if (v_contextDependent_425_ == 0)
{
v___y_437_ = v_contextDependent_435_;
goto v___jp_436_;
}
else
{
v___y_437_ = v_contextDependent_425_;
goto v___jp_436_;
}
v___jp_436_:
{
lean_object* v___x_439_; 
if (v_isShared_428_ == 0)
{
v___x_439_ = v___x_427_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_e_x27_423_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_proof_424_);
v___x_439_ = v_reuseFailAlloc_443_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_441_; 
lean_ctor_set_uint8(v___x_439_, sizeof(void*)*2, v_done_434_);
lean_ctor_set_uint8(v___x_439_, sizeof(void*)*2 + 1, v___y_437_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_439_);
v___x_441_ = v___x_432_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
}
else
{
lean_object* v_e_x27_444_; lean_object* v_proof_445_; uint8_t v_done_446_; uint8_t v_contextDependent_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_473_; 
lean_del_object(v___x_432_);
lean_del_object(v___x_427_);
v_e_x27_444_ = lean_ctor_get(v_a_430_, 0);
v_proof_445_ = lean_ctor_get(v_a_430_, 1);
v_done_446_ = lean_ctor_get_uint8(v_a_430_, sizeof(void*)*2);
v_contextDependent_447_ = lean_ctor_get_uint8(v_a_430_, sizeof(void*)*2 + 1);
v_isSharedCheck_473_ = !lean_is_exclusive(v_a_430_);
if (v_isSharedCheck_473_ == 0)
{
v___x_449_ = v_a_430_;
v_isShared_450_ = v_isSharedCheck_473_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_proof_445_);
lean_inc(v_e_x27_444_);
lean_dec(v_a_430_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_473_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; 
lean_inc_ref(v_e_x27_444_);
v___x_451_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_391_, v_e_x27_423_, v_proof_424_, v_e_x27_444_, v_proof_445_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_464_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_464_ == 0)
{
v___x_454_ = v___x_451_;
v_isShared_455_ = v_isSharedCheck_464_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_451_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_464_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
uint8_t v___y_457_; 
if (v_contextDependent_425_ == 0)
{
v___y_457_ = v_contextDependent_447_;
goto v___jp_456_;
}
else
{
v___y_457_ = v_contextDependent_425_;
goto v___jp_456_;
}
v___jp_456_:
{
lean_object* v___x_459_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 1, v_a_452_);
v___x_459_ = v___x_449_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_e_x27_444_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_a_452_);
lean_ctor_set_uint8(v_reuseFailAlloc_463_, sizeof(void*)*2, v_done_446_);
v___x_459_ = v_reuseFailAlloc_463_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_461_; 
lean_ctor_set_uint8(v___x_459_, sizeof(void*)*2 + 1, v___y_457_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_459_);
v___x_461_ = v___x_454_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
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
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_del_object(v___x_449_);
lean_dec_ref(v_e_x27_444_);
v_a_465_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_451_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_451_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_427_);
lean_dec_ref(v_proof_424_);
lean_dec_ref(v_e_x27_423_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec_ref(v___y_391_);
return v___x_429_;
}
}
}
else
{
lean_dec_ref_known(v_a_404_, 2);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec_ref(v___f_390_);
return v___x_403_;
}
}
}
else
{
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec_ref(v___f_390_);
return v___x_403_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_389_ = stack[0].m_obj;
lean_object* v___f_390_ = stack[1].m_obj;
lean_object* v___y_391_ = stack[2].m_obj;
lean_object* v___y_392_ = stack[3].m_obj;
lean_object* v___y_393_ = stack[4].m_obj;
lean_object* v___y_394_ = stack[5].m_obj;
lean_object* v___y_395_ = stack[6].m_obj;
lean_object* v___y_396_ = stack[7].m_obj;
lean_object* v___y_397_ = stack[8].m_obj;
lean_object* v___y_398_ = stack[9].m_obj;
lean_object* v___y_399_ = stack[10].m_obj;
lean_object* v___y_400_ = stack[11].m_obj;
lean_object* v_res_476_;
v_res_476_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3(v___x_389_, v___f_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
stack->m_obj
 = v_res_476_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3___boxed(lean_object* v___x_477_, lean_object* v___f_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3(v___x_477_, v___f_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec_ref(v___x_477_);
return v_res_490_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__5(lean_object* v_snd_491_, lean_object* v_a_492_, lean_object* v___x_493_, lean_object* v_____r_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_507_ = lean_array_push(v_snd_491_, v_a_492_);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_493_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_491_ = stack[0].m_obj;
lean_object* v_a_492_ = stack[1].m_obj;
lean_object* v___x_493_ = stack[2].m_obj;
lean_object* v_____r_494_ = stack[3].m_obj;
lean_object* v___y_495_ = stack[4].m_obj;
lean_object* v___y_496_ = stack[5].m_obj;
lean_object* v___y_497_ = stack[6].m_obj;
lean_object* v___y_498_ = stack[7].m_obj;
lean_object* v___y_499_ = stack[8].m_obj;
lean_object* v___y_500_ = stack[9].m_obj;
lean_object* v___y_501_ = stack[10].m_obj;
lean_object* v___y_502_ = stack[11].m_obj;
lean_object* v___y_503_ = stack[12].m_obj;
lean_object* v___y_504_ = stack[13].m_obj;
lean_object* v___y_505_ = stack[14].m_obj;
lean_object* v_res_511_;
v_res_511_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__5(v_snd_491_, v_a_492_, v___x_493_, v_____r_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
stack->m_obj
 = v_res_511_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__5___boxed(lean_object* v_snd_512_, lean_object* v_a_513_, lean_object* v___x_514_, lean_object* v_____r_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__5(v_snd_512_, v_a_513_, v___x_514_, v_____r_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
return v_res_528_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__6(uint8_t v___x_529_, lean_object* v___f_530_, lean_object* v_____r_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v___x_544_; lean_object* v_caches_545_; lean_object* v_typeAnalysis_546_; lean_object* v_target_547_; lean_object* v_hypotheses_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_558_; 
v___x_544_ = lean_st_ref_take(v___y_533_);
v_caches_545_ = lean_ctor_get(v___x_544_, 0);
v_typeAnalysis_546_ = lean_ctor_get(v___x_544_, 1);
v_target_547_ = lean_ctor_get(v___x_544_, 2);
v_hypotheses_548_ = lean_ctor_get(v___x_544_, 3);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_558_ == 0)
{
v___x_550_ = v___x_544_;
v_isShared_551_ = v_isSharedCheck_558_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_hypotheses_548_);
lean_inc(v_target_547_);
lean_inc(v_typeAnalysis_546_);
lean_inc(v_caches_545_);
lean_dec(v___x_544_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_558_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = lean_box(0);
if (v_isShared_551_ == 0)
{
v___x_554_ = v___x_550_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_caches_545_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_typeAnalysis_546_);
lean_ctor_set(v_reuseFailAlloc_557_, 2, v_target_547_);
lean_ctor_set(v_reuseFailAlloc_557_, 3, v_hypotheses_548_);
v___x_554_ = v_reuseFailAlloc_557_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_ctor_set_uint8(v___x_554_, sizeof(void*)*4, v___x_529_);
v___x_555_ = lean_st_ref_put(v___y_533_, v___x_554_);
lean_inc(v___y_542_);
lean_inc_ref(v___y_541_);
lean_inc(v___y_540_);
lean_inc_ref(v___y_539_);
lean_inc(v___y_538_);
lean_inc_ref(v___y_537_);
lean_inc(v___y_536_);
lean_inc_ref(v___y_535_);
lean_inc(v___y_534_);
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
v___x_556_ = lean_apply_13(v___f_530_, v___x_552_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, lean_box(0));
return v___x_556_;
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_529_ = stack[0].m_num;
lean_object* v___f_530_ = stack[1].m_obj;
lean_object* v_____r_531_ = stack[2].m_obj;
lean_object* v___y_532_ = stack[3].m_obj;
lean_object* v___y_533_ = stack[4].m_obj;
lean_object* v___y_534_ = stack[5].m_obj;
lean_object* v___y_535_ = stack[6].m_obj;
lean_object* v___y_536_ = stack[7].m_obj;
lean_object* v___y_537_ = stack[8].m_obj;
lean_object* v___y_538_ = stack[9].m_obj;
lean_object* v___y_539_ = stack[10].m_obj;
lean_object* v___y_540_ = stack[11].m_obj;
lean_object* v___y_541_ = stack[12].m_obj;
lean_object* v___y_542_ = stack[13].m_obj;
lean_object* v_res_559_;
v_res_559_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__6(v___x_529_, v___f_530_, v_____r_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
stack->m_obj
 = v_res_559_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__6___boxed(lean_object* v___x_560_, lean_object* v___f_561_, lean_object* v_____r_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
uint8_t v___x_195438__boxed_575_; lean_object* v_res_576_; 
v___x_195438__boxed_575_ = lean_unbox(v___x_560_);
v_res_576_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__6(v___x_195438__boxed_575_, v___f_561_, v_____r_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
return v_res_576_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(lean_object* v_msgData_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v___x_583_; lean_object* v_env_584_; uint8_t v___x_585_; lean_object* v_env_586_; lean_object* v___x_587_; lean_object* v_toCold_588_; lean_object* v_mctx_589_; lean_object* v_lctx_590_; lean_object* v_options_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_583_ = lean_st_ref_get(v___y_581_);
v_env_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc_ref(v_env_584_);
lean_dec(v___x_583_);
v___x_585_ = 0;
v_env_586_ = l_Lean_Environment_setRecordingDeps(v_env_584_, v___x_585_);
v___x_587_ = lean_st_ref_get(v___y_579_);
v_toCold_588_ = lean_ctor_get(v___y_580_, 0);
v_mctx_589_ = lean_ctor_get(v___x_587_, 0);
lean_inc_ref(v_mctx_589_);
lean_dec(v___x_587_);
v_lctx_590_ = lean_ctor_get(v___y_578_, 2);
v_options_591_ = lean_ctor_get(v_toCold_588_, 2);
lean_inc_ref(v_options_591_);
lean_inc_ref(v_lctx_590_);
v___x_592_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_592_, 0, v_env_586_);
lean_ctor_set(v___x_592_, 1, v_mctx_589_);
lean_ctor_set(v___x_592_, 2, v_lctx_590_);
lean_ctor_set(v___x_592_, 3, v_options_591_);
v___x_593_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v_msgData_577_);
v___x_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
return v___x_594_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_577_ = stack[0].m_obj;
lean_object* v___y_578_ = stack[1].m_obj;
lean_object* v___y_579_ = stack[2].m_obj;
lean_object* v___y_580_ = stack[3].m_obj;
lean_object* v___y_581_ = stack[4].m_obj;
lean_object* v_res_595_;
v_res_595_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(v_msgData_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
stack->m_obj
 = v_res_595_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0___boxed(lean_object* v_msgData_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(v_msgData_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
return v_res_602_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_603_; double v___x_604_; 
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = lean_float_of_nat(v___x_603_);
return v___x_604_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(lean_object* v_cls_608_, lean_object* v_msg_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_ref_615_; lean_object* v___x_616_; lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_662_; 
v_ref_615_ = lean_ctor_get(v___y_612_, 2);
v___x_616_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(v_msg_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
v_a_617_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_662_ == 0)
{
v___x_619_ = v___x_616_;
v_isShared_620_ = v_isSharedCheck_662_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_616_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_662_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; lean_object* v_traceState_622_; lean_object* v_env_623_; lean_object* v_nextMacroScope_624_; lean_object* v_ngen_625_; lean_object* v_auxDeclNGen_626_; lean_object* v_cache_627_; lean_object* v_recordedDeps_628_; lean_object* v_messages_629_; lean_object* v_infoState_630_; lean_object* v_snapshotTasks_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_661_; 
v___x_621_ = lean_st_ref_take(v___y_613_);
v_traceState_622_ = lean_ctor_get(v___x_621_, 4);
v_env_623_ = lean_ctor_get(v___x_621_, 0);
v_nextMacroScope_624_ = lean_ctor_get(v___x_621_, 1);
v_ngen_625_ = lean_ctor_get(v___x_621_, 2);
v_auxDeclNGen_626_ = lean_ctor_get(v___x_621_, 3);
v_cache_627_ = lean_ctor_get(v___x_621_, 5);
v_recordedDeps_628_ = lean_ctor_get(v___x_621_, 6);
v_messages_629_ = lean_ctor_get(v___x_621_, 7);
v_infoState_630_ = lean_ctor_get(v___x_621_, 8);
v_snapshotTasks_631_ = lean_ctor_get(v___x_621_, 9);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_661_ == 0)
{
v___x_633_ = v___x_621_;
v_isShared_634_ = v_isSharedCheck_661_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_snapshotTasks_631_);
lean_inc(v_infoState_630_);
lean_inc(v_messages_629_);
lean_inc(v_recordedDeps_628_);
lean_inc(v_cache_627_);
lean_inc(v_traceState_622_);
lean_inc(v_auxDeclNGen_626_);
lean_inc(v_ngen_625_);
lean_inc(v_nextMacroScope_624_);
lean_inc(v_env_623_);
lean_dec(v___x_621_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_661_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
uint64_t v_tid_635_; lean_object* v_traces_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_660_; 
v_tid_635_ = lean_ctor_get_uint64(v_traceState_622_, sizeof(void*)*1);
v_traces_636_ = lean_ctor_get(v_traceState_622_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v_traceState_622_);
if (v_isSharedCheck_660_ == 0)
{
v___x_638_ = v_traceState_622_;
v_isShared_639_ = v_isSharedCheck_660_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_traces_636_);
lean_dec(v_traceState_622_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_660_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; lean_object* v___x_641_; double v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_640_ = lean_box(0);
v___x_641_ = lean_box(0);
v___x_642_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0);
v___x_643_ = 0;
v___x_644_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1));
v___x_645_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_645_, 0, v_cls_608_);
lean_ctor_set(v___x_645_, 1, v___x_641_);
lean_ctor_set(v___x_645_, 2, v___x_644_);
lean_ctor_set_float(v___x_645_, sizeof(void*)*3, v___x_642_);
lean_ctor_set_float(v___x_645_, sizeof(void*)*3 + 8, v___x_642_);
lean_ctor_set_uint8(v___x_645_, sizeof(void*)*3 + 16, v___x_643_);
v___x_646_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__2));
v___x_647_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v_a_617_);
lean_ctor_set(v___x_647_, 2, v___x_646_);
lean_inc(v_ref_615_);
v___x_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_648_, 0, v_ref_615_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = l_Lean_PersistentArray_push___redArg(v_traces_636_, v___x_648_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_649_);
v___x_651_ = v___x_638_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_649_);
lean_ctor_set_uint64(v_reuseFailAlloc_659_, sizeof(void*)*1, v_tid_635_);
v___x_651_ = v_reuseFailAlloc_659_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
lean_object* v___x_653_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 4, v___x_651_);
v___x_653_ = v___x_633_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_env_623_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_nextMacroScope_624_);
lean_ctor_set(v_reuseFailAlloc_658_, 2, v_ngen_625_);
lean_ctor_set(v_reuseFailAlloc_658_, 3, v_auxDeclNGen_626_);
lean_ctor_set(v_reuseFailAlloc_658_, 4, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_658_, 5, v_cache_627_);
lean_ctor_set(v_reuseFailAlloc_658_, 6, v_recordedDeps_628_);
lean_ctor_set(v_reuseFailAlloc_658_, 7, v_messages_629_);
lean_ctor_set(v_reuseFailAlloc_658_, 8, v_infoState_630_);
lean_ctor_set(v_reuseFailAlloc_658_, 9, v_snapshotTasks_631_);
v___x_653_ = v_reuseFailAlloc_658_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_654_ = lean_st_ref_put(v___y_613_, v___x_653_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_640_);
v___x_656_ = v___x_619_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_640_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_608_ = stack[0].m_obj;
lean_object* v_msg_609_ = stack[1].m_obj;
lean_object* v___y_610_ = stack[2].m_obj;
lean_object* v___y_611_ = stack[3].m_obj;
lean_object* v___y_612_ = stack[4].m_obj;
lean_object* v___y_613_ = stack[5].m_obj;
lean_object* v_res_663_;
v_res_663_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v_cls_608_, v_msg_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
stack->m_obj
 = v_res_663_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___boxed(lean_object* v_cls_664_, lean_object* v_msg_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v_cls_664_, v_msg_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
return v_res_671_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__4(lean_object* v___x_672_, lean_object* v___f_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_box(0);
lean_inc_ref(v___y_674_);
v___x_686_ = l_Lean_Meta_Sym_DSimp_evalGround___redArg(v___x_672_, v___y_674_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
if (lean_obj_tag(v_a_687_) == 0)
{
uint8_t v_done_688_; 
v_done_688_ = lean_ctor_get_uint8(v_a_687_, 0);
lean_dec_ref_known(v_a_687_, 0);
if (v_done_688_ == 0)
{
lean_object* v___x_689_; 
lean_dec_ref_known(v___x_686_, 1);
v___x_689_ = lean_apply_12(v___f_673_, v___x_685_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, lean_box(0));
return v___x_689_;
}
else
{
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec_ref(v___f_673_);
return v___x_686_;
}
}
else
{
uint8_t v_done_690_; 
lean_dec_ref(v___y_674_);
v_done_690_ = lean_ctor_get_uint8(v_a_687_, sizeof(void*)*1);
if (v_done_690_ == 0)
{
lean_object* v_e_x27_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_709_; 
lean_dec_ref_known(v___x_686_, 1);
v_e_x27_691_ = lean_ctor_get(v_a_687_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v_a_687_);
if (v_isSharedCheck_709_ == 0)
{
v___x_693_ = v_a_687_;
v_isShared_694_ = v_isSharedCheck_709_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_e_x27_691_);
lean_dec(v_a_687_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_709_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; 
lean_inc_ref(v_e_x27_691_);
v___x_695_ = lean_apply_12(v___f_673_, v___x_685_, v_e_x27_691_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, lean_box(0));
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
if (lean_obj_tag(v_a_696_) == 0)
{
lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_707_; 
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v___x_695_, 0);
lean_dec(v_unused_708_);
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_707_;
goto v_resetjp_697_;
}
else
{
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_707_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
uint8_t v_done_700_; lean_object* v___x_702_; 
v_done_700_ = lean_ctor_get_uint8(v_a_696_, 0);
lean_dec_ref_known(v_a_696_, 0);
if (v_isShared_694_ == 0)
{
v___x_702_ = v___x_693_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_e_x27_691_);
v___x_702_ = v_reuseFailAlloc_706_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_704_; 
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*1, v_done_700_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 0, v___x_702_);
v___x_704_ = v___x_698_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_696_, 1);
lean_del_object(v___x_693_);
lean_dec_ref(v_e_x27_691_);
return v___x_695_;
}
}
else
{
lean_del_object(v___x_693_);
lean_dec_ref(v_e_x27_691_);
return v___x_695_;
}
}
}
else
{
lean_dec_ref_known(v_a_687_, 1);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___f_673_);
return v___x_686_;
}
}
}
else
{
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec(v___y_677_);
lean_dec_ref(v___y_676_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec_ref(v___f_673_);
return v___x_686_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_672_ = stack[0].m_obj;
lean_object* v___f_673_ = stack[1].m_obj;
lean_object* v___y_674_ = stack[2].m_obj;
lean_object* v___y_675_ = stack[3].m_obj;
lean_object* v___y_676_ = stack[4].m_obj;
lean_object* v___y_677_ = stack[5].m_obj;
lean_object* v___y_678_ = stack[6].m_obj;
lean_object* v___y_679_ = stack[7].m_obj;
lean_object* v___y_680_ = stack[8].m_obj;
lean_object* v___y_681_ = stack[9].m_obj;
lean_object* v___y_682_ = stack[10].m_obj;
lean_object* v___y_683_ = stack[11].m_obj;
lean_object* v_res_710_;
v_res_710_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__4(v___x_672_, v___f_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
stack->m_obj
 = v_res_710_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__4___boxed(lean_object* v___x_711_, lean_object* v___f_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__4(v___x_711_, v___f_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___x_711_);
return v_res_724_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__3(lean_object* v_x_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__3___closed__0));
v___x_739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
return v___x_739_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_727_ = stack[0].m_obj;
lean_object* v___y_728_ = stack[1].m_obj;
lean_object* v___y_729_ = stack[2].m_obj;
lean_object* v___y_730_ = stack[3].m_obj;
lean_object* v___y_731_ = stack[4].m_obj;
lean_object* v___y_732_ = stack[5].m_obj;
lean_object* v___y_733_ = stack[6].m_obj;
lean_object* v___y_734_ = stack[7].m_obj;
lean_object* v___y_735_ = stack[8].m_obj;
lean_object* v___y_736_ = stack[9].m_obj;
lean_object* v_res_740_;
v_res_740_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__3(v_x_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
stack->m_obj
 = v_res_740_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__3___boxed(lean_object* v_x_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__3(v_x_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v_x_741_);
return v_res_752_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__2(lean_object* v___f_753_, lean_object* v_x_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = lean_box(0);
lean_inc_ref(v___y_755_);
v___x_767_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v___y_755_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
if (lean_obj_tag(v_a_768_) == 0)
{
uint8_t v_done_769_; 
v_done_769_ = lean_ctor_get_uint8(v_a_768_, 0);
lean_dec_ref_known(v_a_768_, 0);
if (v_done_769_ == 0)
{
lean_object* v___x_770_; 
lean_dec_ref_known(v___x_767_, 1);
lean_inc(v___y_764_);
lean_inc_ref(v___y_763_);
lean_inc(v___y_762_);
lean_inc_ref(v___y_761_);
lean_inc(v___y_760_);
lean_inc_ref(v___y_759_);
lean_inc(v___y_758_);
lean_inc_ref(v___y_757_);
lean_inc(v___y_756_);
v___x_770_ = lean_apply_12(v___f_753_, v___x_766_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, lean_box(0));
return v___x_770_;
}
else
{
lean_dec_ref(v___y_755_);
lean_dec_ref(v___f_753_);
return v___x_767_;
}
}
else
{
uint8_t v_done_771_; 
lean_dec_ref(v___y_755_);
v_done_771_ = lean_ctor_get_uint8(v_a_768_, sizeof(void*)*1);
if (v_done_771_ == 0)
{
lean_object* v_e_x27_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_790_; 
lean_dec_ref_known(v___x_767_, 1);
v_e_x27_772_ = lean_ctor_get(v_a_768_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v_a_768_);
if (v_isSharedCheck_790_ == 0)
{
v___x_774_ = v_a_768_;
v_isShared_775_ = v_isSharedCheck_790_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_e_x27_772_);
lean_dec(v_a_768_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_790_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_776_; 
lean_inc(v___y_764_);
lean_inc_ref(v___y_763_);
lean_inc(v___y_762_);
lean_inc_ref(v___y_761_);
lean_inc(v___y_760_);
lean_inc_ref(v___y_759_);
lean_inc(v___y_758_);
lean_inc_ref(v___y_757_);
lean_inc(v___y_756_);
lean_inc_ref(v_e_x27_772_);
v___x_776_ = lean_apply_12(v___f_753_, v___x_766_, v_e_x27_772_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, lean_box(0));
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
if (lean_obj_tag(v_a_777_) == 0)
{
lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_788_; 
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v___x_776_, 0);
lean_dec(v_unused_789_);
v___x_779_ = v___x_776_;
v_isShared_780_ = v_isSharedCheck_788_;
goto v_resetjp_778_;
}
else
{
lean_dec(v___x_776_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_788_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
uint8_t v_done_781_; lean_object* v___x_783_; 
v_done_781_ = lean_ctor_get_uint8(v_a_777_, 0);
lean_dec_ref_known(v_a_777_, 0);
if (v_isShared_775_ == 0)
{
v___x_783_ = v___x_774_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_e_x27_772_);
v___x_783_ = v_reuseFailAlloc_787_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_785_; 
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*1, v_done_781_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_783_);
v___x_785_ = v___x_779_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
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
else
{
lean_dec_ref_known(v_a_777_, 1);
lean_del_object(v___x_774_);
lean_dec_ref(v_e_x27_772_);
return v___x_776_;
}
}
else
{
lean_del_object(v___x_774_);
lean_dec_ref(v_e_x27_772_);
return v___x_776_;
}
}
}
else
{
lean_dec_ref_known(v_a_768_, 1);
lean_dec_ref(v___f_753_);
return v___x_767_;
}
}
}
else
{
lean_dec_ref(v___y_755_);
lean_dec_ref(v___f_753_);
return v___x_767_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_753_ = stack[0].m_obj;
lean_object* v_x_754_ = stack[1].m_obj;
lean_object* v___y_755_ = stack[2].m_obj;
lean_object* v___y_756_ = stack[3].m_obj;
lean_object* v___y_757_ = stack[4].m_obj;
lean_object* v___y_758_ = stack[5].m_obj;
lean_object* v___y_759_ = stack[6].m_obj;
lean_object* v___y_760_ = stack[7].m_obj;
lean_object* v___y_761_ = stack[8].m_obj;
lean_object* v___y_762_ = stack[9].m_obj;
lean_object* v___y_763_ = stack[10].m_obj;
lean_object* v___y_764_ = stack[11].m_obj;
lean_object* v_res_791_;
v_res_791_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__2(v___f_753_, v_x_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
stack->m_obj
 = v_res_791_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__2___boxed(lean_object* v___f_792_, lean_object* v_x_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__2(v___f_792_, v_x_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
return v_res_805_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__1(lean_object* v___f_806_, lean_object* v_x_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_box(0);
lean_inc_ref(v___y_808_);
v___x_820_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_808_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
if (lean_obj_tag(v_a_821_) == 0)
{
uint8_t v_done_822_; 
v_done_822_ = lean_ctor_get_uint8(v_a_821_, 0);
lean_dec_ref_known(v_a_821_, 0);
if (v_done_822_ == 0)
{
lean_object* v___x_823_; 
lean_dec_ref_known(v___x_820_, 1);
lean_inc(v___y_817_);
lean_inc_ref(v___y_816_);
lean_inc(v___y_815_);
lean_inc_ref(v___y_814_);
lean_inc(v___y_813_);
lean_inc_ref(v___y_812_);
lean_inc(v___y_811_);
lean_inc_ref(v___y_810_);
lean_inc(v___y_809_);
v___x_823_ = lean_apply_12(v___f_806_, v___x_819_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, lean_box(0));
return v___x_823_;
}
else
{
lean_dec_ref(v___y_808_);
lean_dec_ref(v___f_806_);
return v___x_820_;
}
}
else
{
uint8_t v_done_824_; 
lean_dec_ref(v___y_808_);
v_done_824_ = lean_ctor_get_uint8(v_a_821_, sizeof(void*)*1);
if (v_done_824_ == 0)
{
lean_object* v_e_x27_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_843_; 
lean_dec_ref_known(v___x_820_, 1);
v_e_x27_825_ = lean_ctor_get(v_a_821_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v_a_821_);
if (v_isSharedCheck_843_ == 0)
{
v___x_827_ = v_a_821_;
v_isShared_828_ = v_isSharedCheck_843_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_e_x27_825_);
lean_dec(v_a_821_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_843_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; 
lean_inc(v___y_817_);
lean_inc_ref(v___y_816_);
lean_inc(v___y_815_);
lean_inc_ref(v___y_814_);
lean_inc(v___y_813_);
lean_inc_ref(v___y_812_);
lean_inc(v___y_811_);
lean_inc_ref(v___y_810_);
lean_inc(v___y_809_);
lean_inc_ref(v_e_x27_825_);
v___x_829_ = lean_apply_12(v___f_806_, v___x_819_, v_e_x27_825_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, lean_box(0));
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
if (lean_obj_tag(v_a_830_) == 0)
{
lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_841_; 
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; 
v_unused_842_ = lean_ctor_get(v___x_829_, 0);
lean_dec(v_unused_842_);
v___x_832_ = v___x_829_;
v_isShared_833_ = v_isSharedCheck_841_;
goto v_resetjp_831_;
}
else
{
lean_dec(v___x_829_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_841_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
uint8_t v_done_834_; lean_object* v___x_836_; 
v_done_834_ = lean_ctor_get_uint8(v_a_830_, 0);
lean_dec_ref_known(v_a_830_, 0);
if (v_isShared_828_ == 0)
{
v___x_836_ = v___x_827_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_e_x27_825_);
v___x_836_ = v_reuseFailAlloc_840_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v___x_838_; 
lean_ctor_set_uint8(v___x_836_, sizeof(void*)*1, v_done_834_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v___x_836_);
v___x_838_ = v___x_832_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_830_, 1);
lean_del_object(v___x_827_);
lean_dec_ref(v_e_x27_825_);
return v___x_829_;
}
}
else
{
lean_del_object(v___x_827_);
lean_dec_ref(v_e_x27_825_);
return v___x_829_;
}
}
}
else
{
lean_dec_ref_known(v_a_821_, 1);
lean_dec_ref(v___f_806_);
return v___x_820_;
}
}
}
else
{
lean_dec_ref(v___y_808_);
lean_dec_ref(v___f_806_);
return v___x_820_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_806_ = stack[0].m_obj;
lean_object* v_x_807_ = stack[1].m_obj;
lean_object* v___y_808_ = stack[2].m_obj;
lean_object* v___y_809_ = stack[3].m_obj;
lean_object* v___y_810_ = stack[4].m_obj;
lean_object* v___y_811_ = stack[5].m_obj;
lean_object* v___y_812_ = stack[6].m_obj;
lean_object* v___y_813_ = stack[7].m_obj;
lean_object* v___y_814_ = stack[8].m_obj;
lean_object* v___y_815_ = stack[9].m_obj;
lean_object* v___y_816_ = stack[10].m_obj;
lean_object* v___y_817_ = stack[11].m_obj;
lean_object* v_res_844_;
v_res_844_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__1(v___f_806_, v_x_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
stack->m_obj
 = v_res_844_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__1___boxed(lean_object* v___f_845_, lean_object* v_x_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__1(v___f_845_, v_x_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v___y_848_);
return v_res_858_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__0(lean_object* v_x_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v___x_871_; 
lean_inc_ref(v___y_860_);
v___x_871_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_860_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
if (lean_obj_tag(v_a_872_) == 0)
{
uint8_t v_done_873_; 
v_done_873_ = lean_ctor_get_uint8(v_a_872_, 0);
lean_dec_ref_known(v_a_872_, 0);
if (v_done_873_ == 0)
{
lean_object* v___x_874_; 
lean_dec_ref_known(v___x_871_, 1);
v___x_874_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteDsimproc___redArg(v___y_860_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
return v___x_874_;
}
else
{
lean_dec_ref(v___y_860_);
return v___x_871_;
}
}
else
{
uint8_t v_done_875_; 
lean_dec_ref(v___y_860_);
v_done_875_ = lean_ctor_get_uint8(v_a_872_, sizeof(void*)*1);
if (v_done_875_ == 0)
{
lean_object* v_e_x27_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_894_; 
lean_dec_ref_known(v___x_871_, 1);
v_e_x27_876_ = lean_ctor_get(v_a_872_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v_a_872_);
if (v_isSharedCheck_894_ == 0)
{
v___x_878_ = v_a_872_;
v_isShared_879_ = v_isSharedCheck_894_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_e_x27_876_);
lean_dec(v_a_872_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_894_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_880_; 
lean_inc_ref(v_e_x27_876_);
v___x_880_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteDsimproc___redArg(v_e_x27_876_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
if (lean_obj_tag(v_a_881_) == 0)
{
lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_892_; 
lean_inc_ref(v_a_881_);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v___x_880_, 0);
lean_dec(v_unused_893_);
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_892_;
goto v_resetjp_882_;
}
else
{
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_892_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
uint8_t v_done_885_; lean_object* v___x_887_; 
v_done_885_ = lean_ctor_get_uint8(v_a_881_, 0);
lean_dec_ref_known(v_a_881_, 0);
if (v_isShared_879_ == 0)
{
v___x_887_ = v___x_878_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_e_x27_876_);
v___x_887_ = v_reuseFailAlloc_891_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_889_; 
lean_ctor_set_uint8(v___x_887_, sizeof(void*)*1, v_done_885_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_887_);
v___x_889_ = v___x_883_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
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
lean_del_object(v___x_878_);
lean_dec_ref(v_e_x27_876_);
return v___x_880_;
}
}
else
{
lean_del_object(v___x_878_);
lean_dec_ref(v_e_x27_876_);
return v___x_880_;
}
}
}
else
{
lean_dec_ref_known(v_a_872_, 1);
return v___x_871_;
}
}
}
else
{
lean_dec_ref(v___y_860_);
return v___x_871_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_859_ = stack[0].m_obj;
lean_object* v___y_860_ = stack[1].m_obj;
lean_object* v___y_861_ = stack[2].m_obj;
lean_object* v___y_862_ = stack[3].m_obj;
lean_object* v___y_863_ = stack[4].m_obj;
lean_object* v___y_864_ = stack[5].m_obj;
lean_object* v___y_865_ = stack[6].m_obj;
lean_object* v___y_866_ = stack[7].m_obj;
lean_object* v___y_867_ = stack[8].m_obj;
lean_object* v___y_868_ = stack[9].m_obj;
lean_object* v___y_869_ = stack[10].m_obj;
lean_object* v_res_895_;
v_res_895_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__0(v_x_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
stack->m_obj
 = v_res_895_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__0___boxed(lean_object* v_x_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__0(v_x_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
return v_res_908_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__9));
v___x_932_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__11));
v___x_933_ = l_Lean_Name_append(v___x_932_, v___x_931_);
return v___x_933_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__14(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__13));
v___x_936_ = l_Lean_stringToMessageData(v___x_935_);
return v___x_936_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(lean_object* v_upperBound_937_, lean_object* v___x_938_, lean_object* v___x_939_, lean_object* v___x_940_, lean_object* v___x_941_, lean_object* v_a_942_, lean_object* v_b_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v___y_957_; lean_object* v___y_980_; uint8_t v___x_983_; 
v___x_983_ = lean_nat_dec_lt(v_a_942_, v_upperBound_937_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; 
lean_dec(v_a_942_);
lean_dec_ref(v___x_941_);
lean_dec_ref(v___x_940_);
lean_dec_ref(v___x_939_);
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v_b_943_);
return v___x_984_;
}
else
{
lean_object* v_snd_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1067_; 
v_snd_985_ = lean_ctor_get(v_b_943_, 1);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_b_943_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; 
v_unused_1068_ = lean_ctor_get(v_b_943_, 0);
lean_dec(v_unused_1068_);
v___x_987_ = v_b_943_;
v_isShared_988_ = v_isSharedCheck_1067_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_snd_985_);
lean_dec(v_b_943_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1067_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___y_993_; lean_object* v___y_994_; lean_object* v___y_1020_; uint8_t v___x_1062_; lean_object* v___x_1063_; 
v___x_989_ = lean_box(0);
v___x_990_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__5));
v___x_991_ = lean_array_fget_borrowed(v___x_938_, v_a_942_);
v___x_1062_ = 0;
lean_inc(v___x_991_);
lean_inc_ref(v___x_939_);
v___x_1063_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v___x_1062_, v___x_990_, v___x_939_, v___x_991_, v___y_945_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; uint8_t v___x_1065_; lean_object* v___x_1066_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref_known(v___x_1063_, 1);
v___x_1065_ = 0;
lean_inc_ref(v___x_941_);
lean_inc_ref(v___x_940_);
v___x_1066_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v___x_1065_, v___x_940_, v___x_941_, v_a_1064_, v___y_945_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
v___y_1020_ = v___x_1066_;
goto v___jp_1019_;
}
else
{
v___y_1020_ = v___x_1063_;
goto v___jp_1019_;
}
v___jp_992_:
{
lean_object* v_toCold_995_; lean_object* v_options_996_; uint8_t v_hasTrace_997_; 
v_toCold_995_ = lean_ctor_get(v___y_953_, 0);
v_options_996_ = lean_ctor_get(v_toCold_995_, 2);
v_hasTrace_997_ = lean_ctor_get_uint8(v_options_996_, sizeof(void*)*1);
if (v_hasTrace_997_ == 0)
{
lean_dec_ref(v___y_993_);
v___y_980_ = v___y_994_;
goto v___jp_979_;
}
else
{
lean_object* v_inheritedTraceOptions_998_; lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v_inheritedTraceOptions_998_ = lean_ctor_get(v_toCold_995_, 11);
v___x_999_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__9));
v___x_1000_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12);
v___x_1001_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_998_, v_options_996_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_dec_ref(v___y_993_);
v___y_980_ = v___y_994_;
goto v___jp_979_;
}
else
{
lean_object* v_type_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v_type_1002_ = lean_ctor_get(v___x_991_, 1);
lean_inc_ref(v_type_1002_);
v___x_1003_ = l_Lean_MessageData_ofExpr(v_type_1002_);
v___x_1004_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__14, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__14_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__14);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = l_Lean_MessageData_ofExpr(v___y_993_);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v___x_999_, v___x_1007_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1008_, 1);
lean_inc(v___y_954_);
lean_inc_ref(v___y_953_);
lean_inc(v___y_952_);
lean_inc_ref(v___y_951_);
lean_inc(v___y_950_);
lean_inc_ref(v___y_949_);
lean_inc(v___y_948_);
lean_inc_ref(v___y_947_);
lean_inc(v___y_946_);
lean_inc(v___y_945_);
lean_inc_ref(v___y_944_);
v___x_1010_ = lean_apply_13(v___y_994_, v_a_1009_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, lean_box(0));
v___y_957_ = v___x_1010_;
goto v___jp_956_;
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec_ref(v___y_994_);
lean_dec(v_a_942_);
lean_dec_ref(v___x_941_);
lean_dec_ref(v___x_940_);
lean_dec_ref(v___x_939_);
v_a_1011_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1008_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1008_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
}
v___jp_1019_:
{
if (lean_obj_tag(v___y_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v_type_1022_; lean_object* v_value_1023_; uint8_t v___x_1024_; 
v_a_1021_ = lean_ctor_get(v___y_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___y_1020_, 1);
v_type_1022_ = lean_ctor_get(v_a_1021_, 1);
v_value_1023_ = lean_ctor_get(v_a_1021_, 2);
lean_inc_ref(v_type_1022_);
v___x_1024_ = l_Lean_Expr_isFalse(v_type_1022_);
if (v___x_1024_ == 0)
{
lean_object* v_type_1025_; lean_object* v___f_1026_; lean_object* v___x_1027_; lean_object* v___f_1028_; uint8_t v___x_1029_; 
lean_del_object(v___x_987_);
v_type_1025_ = lean_ctor_get(v___x_991_, 1);
lean_inc(v_a_1021_);
lean_inc(v_snd_985_);
v___f_1026_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__5___boxed), 16, 3);
lean_closure_set(v___f_1026_, 0, v_snd_985_);
lean_closure_set(v___f_1026_, 1, v_a_1021_);
lean_closure_set(v___f_1026_, 2, v___x_989_);
v___x_1027_ = lean_box(v___x_983_);
v___f_1028_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__6___boxed), 15, 2);
lean_closure_set(v___f_1028_, 0, v___x_1027_);
lean_closure_set(v___f_1028_, 1, v___f_1026_);
v___x_1029_ = lean_expr_eqv(v_type_1025_, v_type_1022_);
if (v___x_1029_ == 0)
{
lean_inc_ref(v_type_1022_);
lean_dec(v_a_1021_);
lean_dec(v_snd_985_);
v___y_993_ = v_type_1022_;
v___y_994_ = v___f_1028_;
goto v___jp_992_;
}
else
{
if (v___x_1024_ == 0)
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
lean_dec_ref(v___f_1028_);
v___x_1030_ = lean_box(0);
v___x_1031_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___lam__5(v_snd_985_, v_a_1021_, v___x_989_, v___x_1030_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
v___y_957_ = v___x_1031_;
goto v___jp_956_;
}
else
{
lean_inc_ref(v_type_1022_);
lean_dec(v_a_1021_);
lean_dec(v_snd_985_);
v___y_993_ = v_type_1022_;
v___y_994_ = v___f_1028_;
goto v___jp_992_;
}
}
}
else
{
lean_object* v___x_1032_; 
lean_inc_ref(v_value_1023_);
lean_dec(v_a_1021_);
lean_dec(v_a_942_);
lean_dec_ref(v___x_941_);
lean_dec_ref(v___x_940_);
lean_dec_ref(v___x_939_);
v___x_1032_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_1023_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
if (lean_obj_tag(v___x_1032_) == 0)
{
lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1044_; 
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1044_ == 0)
{
lean_object* v_unused_1045_; 
v_unused_1045_ = lean_ctor_get(v___x_1032_, 0);
lean_dec(v_unused_1045_);
v___x_1034_ = v___x_1032_;
v_isShared_1035_ = v_isSharedCheck_1044_;
goto v_resetjp_1033_;
}
else
{
lean_dec(v___x_1032_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1044_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
v___x_1036_ = lean_box(v___x_983_);
v___x_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_1037_);
v___x_1039_ = v___x_987_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_snd_985_);
v___x_1039_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___x_1041_; 
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v___x_1039_);
v___x_1041_ = v___x_1034_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
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
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_del_object(v___x_987_);
lean_dec(v_snd_985_);
v_a_1046_ = lean_ctor_get(v___x_1032_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1032_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1032_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1032_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_del_object(v___x_987_);
lean_dec(v_snd_985_);
lean_dec(v_a_942_);
lean_dec_ref(v___x_941_);
lean_dec_ref(v___x_940_);
lean_dec_ref(v___x_939_);
v_a_1054_ = lean_ctor_get(v___y_1020_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___y_1020_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___y_1020_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___y_1020_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
}
v___jp_956_:
{
if (lean_obj_tag(v___y_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_970_; 
v_a_958_ = lean_ctor_get(v___y_957_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___y_957_);
if (v_isSharedCheck_970_ == 0)
{
v___x_960_ = v___y_957_;
v_isShared_961_ = v_isSharedCheck_970_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___y_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_970_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
if (lean_obj_tag(v_a_958_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_964_; 
lean_dec(v_a_942_);
lean_dec_ref(v___x_941_);
lean_dec_ref(v___x_940_);
lean_dec_ref(v___x_939_);
v_a_962_ = lean_ctor_get(v_a_958_, 0);
lean_inc(v_a_962_);
lean_dec_ref_known(v_a_958_, 1);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v_a_962_);
v___x_964_ = v___x_960_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
lean_del_object(v___x_960_);
v_a_966_ = lean_ctor_get(v_a_958_, 0);
lean_inc(v_a_966_);
lean_dec_ref_known(v_a_958_, 1);
v___x_967_ = lean_unsigned_to_nat(1u);
v___x_968_ = lean_nat_add(v_a_942_, v___x_967_);
lean_dec(v_a_942_);
v_a_942_ = v___x_968_;
v_b_943_ = v_a_966_;
goto _start;
}
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
lean_dec(v_a_942_);
lean_dec_ref(v___x_941_);
lean_dec_ref(v___x_940_);
lean_dec_ref(v___x_939_);
v_a_971_ = lean_ctor_get(v___y_957_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___y_957_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___y_957_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___y_957_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
v___jp_979_:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = lean_box(0);
lean_inc(v___y_954_);
lean_inc_ref(v___y_953_);
lean_inc(v___y_952_);
lean_inc_ref(v___y_951_);
lean_inc(v___y_950_);
lean_inc_ref(v___y_949_);
lean_inc(v___y_948_);
lean_inc_ref(v___y_947_);
lean_inc(v___y_946_);
lean_inc(v___y_945_);
lean_inc_ref(v___y_944_);
v___x_982_ = lean_apply_13(v___y_980_, v___x_981_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, lean_box(0));
v___y_957_ = v___x_982_;
goto v___jp_956_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_937_ = stack[0].m_obj;
lean_object* v___x_938_ = stack[1].m_obj;
lean_object* v___x_939_ = stack[2].m_obj;
lean_object* v___x_940_ = stack[3].m_obj;
lean_object* v___x_941_ = stack[4].m_obj;
lean_object* v_a_942_ = stack[5].m_obj;
lean_object* v_b_943_ = stack[6].m_obj;
lean_object* v___y_944_ = stack[7].m_obj;
lean_object* v___y_945_ = stack[8].m_obj;
lean_object* v___y_946_ = stack[9].m_obj;
lean_object* v___y_947_ = stack[10].m_obj;
lean_object* v___y_948_ = stack[11].m_obj;
lean_object* v___y_949_ = stack[12].m_obj;
lean_object* v___y_950_ = stack[13].m_obj;
lean_object* v___y_951_ = stack[14].m_obj;
lean_object* v___y_952_ = stack[15].m_obj;
lean_object* v___y_953_ = stack[16].m_obj;
lean_object* v___y_954_ = stack[17].m_obj;
lean_object* v_res_1069_;
v_res_1069_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v_upperBound_937_, v___x_938_, v___x_939_, v___x_940_, v___x_941_, v_a_942_, v_b_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
stack->m_obj
 = v_res_1069_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_1070_ = _args[0];
lean_object* v___x_1071_ = _args[1];
lean_object* v___x_1072_ = _args[2];
lean_object* v___x_1073_ = _args[3];
lean_object* v___x_1074_ = _args[4];
lean_object* v_a_1075_ = _args[5];
lean_object* v_b_1076_ = _args[6];
lean_object* v___y_1077_ = _args[7];
lean_object* v___y_1078_ = _args[8];
lean_object* v___y_1079_ = _args[9];
lean_object* v___y_1080_ = _args[10];
lean_object* v___y_1081_ = _args[11];
lean_object* v___y_1082_ = _args[12];
lean_object* v___y_1083_ = _args[13];
lean_object* v___y_1084_ = _args[14];
lean_object* v___y_1085_ = _args[15];
lean_object* v___y_1086_ = _args[16];
lean_object* v___y_1087_ = _args[17];
lean_object* v___y_1088_ = _args[18];
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v_upperBound_1070_, v___x_1071_, v___x_1072_, v___x_1073_, v___x_1074_, v_a_1075_, v_b_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec_ref(v___x_1071_);
lean_dec(v_upperBound_1070_);
return v_res_1089_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4(lean_object* v___x_1090_, lean_object* v___x_1091_, lean_object* v___x_1092_, lean_object* v___x_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___x_1106_; lean_object* v_hypotheses_1107_; lean_object* v___x_1108_; lean_object* v_newHyps_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1106_ = lean_st_ref_get(v___y_1095_);
v_hypotheses_1107_ = lean_ctor_get(v___x_1106_, 3);
lean_inc_ref(v_hypotheses_1107_);
lean_dec(v___x_1106_);
v___x_1108_ = lean_array_get_size(v_hypotheses_1107_);
v_newHyps_1109_ = lean_mk_empty_array_with_capacity(v___x_1108_);
v___x_1110_ = lean_box(0);
v___x_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set(v___x_1111_, 1, v_newHyps_1109_);
v___x_1112_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v___x_1108_, v_hypotheses_1107_, v___x_1090_, v___x_1091_, v___x_1092_, v___x_1093_, v___x_1111_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
lean_dec_ref(v_hypotheses_1107_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1142_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1115_ = v___x_1112_;
v_isShared_1116_ = v_isSharedCheck_1142_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1142_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v_fst_1117_; 
v_fst_1117_ = lean_ctor_get(v_a_1113_, 0);
if (lean_obj_tag(v_fst_1117_) == 0)
{
lean_object* v_snd_1118_; lean_object* v___x_1119_; lean_object* v_caches_1120_; lean_object* v_typeAnalysis_1121_; lean_object* v_target_1122_; uint8_t v_didChange_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1136_; 
v_snd_1118_ = lean_ctor_get(v_a_1113_, 1);
lean_inc(v_snd_1118_);
lean_dec(v_a_1113_);
v___x_1119_ = lean_st_ref_take(v___y_1095_);
v_caches_1120_ = lean_ctor_get(v___x_1119_, 0);
v_typeAnalysis_1121_ = lean_ctor_get(v___x_1119_, 1);
v_target_1122_ = lean_ctor_get(v___x_1119_, 2);
v_didChange_1123_ = lean_ctor_get_uint8(v___x_1119_, sizeof(void*)*4);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; 
v_unused_1137_ = lean_ctor_get(v___x_1119_, 3);
lean_dec(v_unused_1137_);
v___x_1125_ = v___x_1119_;
v_isShared_1126_ = v_isSharedCheck_1136_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_target_1122_);
lean_inc(v_typeAnalysis_1121_);
lean_inc(v_caches_1120_);
lean_dec(v___x_1119_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1136_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 3, v_snd_1118_);
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_caches_1120_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_typeAnalysis_1121_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_target_1122_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v_snd_1118_);
lean_ctor_set_uint8(v_reuseFailAlloc_1135_, sizeof(void*)*4, v_didChange_1123_);
v___x_1128_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
lean_object* v___x_1129_; uint8_t v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1129_ = lean_st_ref_put(v___y_1095_, v___x_1128_);
v___x_1130_ = 0;
v___x_1131_ = lean_box(v___x_1130_);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1131_);
v___x_1133_ = v___x_1115_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
else
{
lean_object* v_val_1138_; lean_object* v___x_1140_; 
lean_inc_ref(v_fst_1117_);
lean_dec(v_a_1113_);
v_val_1138_ = lean_ctor_get(v_fst_1117_, 0);
lean_inc(v_val_1138_);
lean_dec_ref_known(v_fst_1117_, 1);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v_val_1138_);
v___x_1140_ = v___x_1115_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_val_1138_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
v_a_1143_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1112_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1112_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1090_ = stack[0].m_obj;
lean_object* v___x_1091_ = stack[1].m_obj;
lean_object* v___x_1092_ = stack[2].m_obj;
lean_object* v___x_1093_ = stack[3].m_obj;
lean_object* v___y_1094_ = stack[4].m_obj;
lean_object* v___y_1095_ = stack[5].m_obj;
lean_object* v___y_1096_ = stack[6].m_obj;
lean_object* v___y_1097_ = stack[7].m_obj;
lean_object* v___y_1098_ = stack[8].m_obj;
lean_object* v___y_1099_ = stack[9].m_obj;
lean_object* v___y_1100_ = stack[10].m_obj;
lean_object* v___y_1101_ = stack[11].m_obj;
lean_object* v___y_1102_ = stack[12].m_obj;
lean_object* v___y_1103_ = stack[13].m_obj;
lean_object* v___y_1104_ = stack[14].m_obj;
lean_object* v_res_1151_;
v_res_1151_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4(v___x_1090_, v___x_1091_, v___x_1092_, v___x_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
stack->m_obj
 = v_res_1151_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4___boxed(lean_object* v___x_1152_, lean_object* v___x_1153_, lean_object* v___x_1154_, lean_object* v___x_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4(v___x_1152_, v___x_1153_, v___x_1154_, v___x_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
return v_res_1168_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8___redArg(lean_object* v_x_1169_){
_start:
{
if (lean_obj_tag(v_x_1169_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
v_a_1171_ = lean_ctor_get(v_x_1169_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_x_1169_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v_x_1169_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v_x_1169_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
lean_ctor_set_tag(v___x_1173_, 1);
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
v_a_1179_ = lean_ctor_get(v_x_1169_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_x_1169_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v_x_1169_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v_x_1169_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
lean_ctor_set_tag(v___x_1181_, 0);
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1169_ = stack[0].m_obj;
lean_object* v_res_1187_;
v_res_1187_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8___redArg(v_x_1169_);
stack->m_obj
 = v_res_1187_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8___redArg___boxed(lean_object* v_x_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8___redArg(v_x_1188_);
return v_res_1190_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__9(lean_object* v_e_1191_){
_start:
{
if (lean_obj_tag(v_e_1191_) == 0)
{
uint8_t v___x_1192_; 
v___x_1192_ = 2;
return v___x_1192_;
}
else
{
uint8_t v___x_1193_; 
v___x_1193_ = 0;
return v___x_1193_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1191_ = stack[0].m_obj;
uint8_t v_res_1194_;
v_res_1194_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__9(v_e_1191_);
stack->m_num = v_res_1194_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__9___boxed(lean_object* v_e_1195_){
_start:
{
uint8_t v_res_1196_; lean_object* v_r_1197_; 
v_res_1196_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__9(v_e_1195_);
lean_dec_ref(v_e_1195_);
v_r_1197_ = lean_box(v_res_1196_);
return v_r_1197_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7_spec__8(size_t v_sz_1198_, size_t v_i_1199_, lean_object* v_bs_1200_){
_start:
{
uint8_t v___x_1201_; 
v___x_1201_ = lean_usize_dec_lt(v_i_1199_, v_sz_1198_);
if (v___x_1201_ == 0)
{
return v_bs_1200_;
}
else
{
lean_object* v_v_1202_; lean_object* v_msg_1203_; lean_object* v___x_1204_; lean_object* v_bs_x27_1205_; size_t v___x_1206_; size_t v___x_1207_; lean_object* v___x_1208_; 
v_v_1202_ = lean_array_uget_borrowed(v_bs_1200_, v_i_1199_);
v_msg_1203_ = lean_ctor_get(v_v_1202_, 1);
lean_inc_ref(v_msg_1203_);
v___x_1204_ = lean_unsigned_to_nat(0u);
v_bs_x27_1205_ = lean_array_uset(v_bs_1200_, v_i_1199_, v___x_1204_);
v___x_1206_ = ((size_t)1ULL);
v___x_1207_ = lean_usize_add(v_i_1199_, v___x_1206_);
v___x_1208_ = lean_array_uset(v_bs_x27_1205_, v_i_1199_, v_msg_1203_);
v_i_1199_ = v___x_1207_;
v_bs_1200_ = v___x_1208_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1198_ = stack[0].m_num;
size_t v_i_1199_ = stack[1].m_num;
lean_object* v_bs_1200_ = stack[2].m_obj;
lean_object* v_res_1210_;
v_res_1210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7_spec__8(v_sz_1198_, v_i_1199_, v_bs_1200_);
stack->m_obj
 = v_res_1210_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7_spec__8___boxed(lean_object* v_sz_1211_, lean_object* v_i_1212_, lean_object* v_bs_1213_){
_start:
{
size_t v_sz_boxed_1214_; size_t v_i_boxed_1215_; lean_object* v_res_1216_; 
v_sz_boxed_1214_ = lean_unbox_usize(v_sz_1211_);
lean_dec(v_sz_1211_);
v_i_boxed_1215_ = lean_unbox_usize(v_i_1212_);
lean_dec(v_i_1212_);
v_res_1216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7_spec__8(v_sz_boxed_1214_, v_i_boxed_1215_, v_bs_1213_);
return v_res_1216_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7___redArg(lean_object* v_oldTraces_1217_, lean_object* v_data_1218_, lean_object* v_ref_1219_, lean_object* v_msg_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_toCold_1226_; lean_object* v_currRecDepth_1227_; lean_object* v_ref_1228_; uint16_t v_optionFlags_1229_; uint8_t v_suppressElabErrors_1230_; uint8_t v_isRecordingDeps_1231_; lean_object* v_ref_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v_traceState_1235_; lean_object* v_traces_1236_; lean_object* v___x_1237_; size_t v_sz_1238_; size_t v___x_1239_; lean_object* v___x_1240_; lean_object* v_msg_1241_; lean_object* v___x_1242_; lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1281_; 
v_toCold_1226_ = lean_ctor_get(v___y_1223_, 0);
v_currRecDepth_1227_ = lean_ctor_get(v___y_1223_, 1);
v_ref_1228_ = lean_ctor_get(v___y_1223_, 2);
v_optionFlags_1229_ = lean_ctor_get_uint16(v___y_1223_, sizeof(void*)*3);
v_suppressElabErrors_1230_ = lean_ctor_get_uint8(v___y_1223_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1231_ = lean_ctor_get_uint8(v___y_1223_, sizeof(void*)*3 + 3);
v_ref_1232_ = l_Lean_replaceRef(v_ref_1219_, v_ref_1228_);
lean_inc(v_currRecDepth_1227_);
lean_inc_ref(v_toCold_1226_);
v___x_1233_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1233_, 0, v_toCold_1226_);
lean_ctor_set(v___x_1233_, 1, v_currRecDepth_1227_);
lean_ctor_set(v___x_1233_, 2, v_ref_1232_);
lean_ctor_set_uint16(v___x_1233_, sizeof(void*)*3, v_optionFlags_1229_);
lean_ctor_set_uint8(v___x_1233_, sizeof(void*)*3 + 2, v_suppressElabErrors_1230_);
lean_ctor_set_uint8(v___x_1233_, sizeof(void*)*3 + 3, v_isRecordingDeps_1231_);
v___x_1234_ = lean_st_ref_get(v___y_1224_);
v_traceState_1235_ = lean_ctor_get(v___x_1234_, 4);
lean_inc_ref(v_traceState_1235_);
lean_dec(v___x_1234_);
v_traces_1236_ = lean_ctor_get(v_traceState_1235_, 0);
lean_inc_ref(v_traces_1236_);
lean_dec_ref(v_traceState_1235_);
v___x_1237_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1236_);
lean_dec_ref(v_traces_1236_);
v_sz_1238_ = lean_array_size(v___x_1237_);
v___x_1239_ = ((size_t)0ULL);
v___x_1240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7_spec__8(v_sz_1238_, v___x_1239_, v___x_1237_);
v_msg_1241_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1241_, 0, v_data_1218_);
lean_ctor_set(v_msg_1241_, 1, v_msg_1220_);
lean_ctor_set(v_msg_1241_, 2, v___x_1240_);
v___x_1242_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(v_msg_1241_, v___y_1221_, v___y_1222_, v___x_1233_, v___y_1224_);
lean_dec_ref_known(v___x_1233_, 3);
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1245_ = v___x_1242_;
v_isShared_1246_ = v_isSharedCheck_1281_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1242_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1281_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v_traceState_1248_; lean_object* v_env_1249_; lean_object* v_nextMacroScope_1250_; lean_object* v_ngen_1251_; lean_object* v_auxDeclNGen_1252_; lean_object* v_cache_1253_; lean_object* v_recordedDeps_1254_; lean_object* v_messages_1255_; lean_object* v_infoState_1256_; lean_object* v_snapshotTasks_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1280_; 
v___x_1247_ = lean_st_ref_take(v___y_1224_);
v_traceState_1248_ = lean_ctor_get(v___x_1247_, 4);
v_env_1249_ = lean_ctor_get(v___x_1247_, 0);
v_nextMacroScope_1250_ = lean_ctor_get(v___x_1247_, 1);
v_ngen_1251_ = lean_ctor_get(v___x_1247_, 2);
v_auxDeclNGen_1252_ = lean_ctor_get(v___x_1247_, 3);
v_cache_1253_ = lean_ctor_get(v___x_1247_, 5);
v_recordedDeps_1254_ = lean_ctor_get(v___x_1247_, 6);
v_messages_1255_ = lean_ctor_get(v___x_1247_, 7);
v_infoState_1256_ = lean_ctor_get(v___x_1247_, 8);
v_snapshotTasks_1257_ = lean_ctor_get(v___x_1247_, 9);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1259_ = v___x_1247_;
v_isShared_1260_ = v_isSharedCheck_1280_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_snapshotTasks_1257_);
lean_inc(v_infoState_1256_);
lean_inc(v_messages_1255_);
lean_inc(v_recordedDeps_1254_);
lean_inc(v_cache_1253_);
lean_inc(v_traceState_1248_);
lean_inc(v_auxDeclNGen_1252_);
lean_inc(v_ngen_1251_);
lean_inc(v_nextMacroScope_1250_);
lean_inc(v_env_1249_);
lean_dec(v___x_1247_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1280_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
uint64_t v_tid_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1278_; 
v_tid_1261_ = lean_ctor_get_uint64(v_traceState_1248_, sizeof(void*)*1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_traceState_1248_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; 
v_unused_1279_ = lean_ctor_get(v_traceState_1248_, 0);
lean_dec(v_unused_1279_);
v___x_1263_ = v_traceState_1248_;
v_isShared_1264_ = v_isSharedCheck_1278_;
goto v_resetjp_1262_;
}
else
{
lean_dec(v_traceState_1248_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1278_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1265_ = lean_box(0);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v_ref_1219_);
lean_ctor_set(v___x_1266_, 1, v_a_1243_);
v___x_1267_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1217_, v___x_1266_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1267_);
v___x_1269_ = v___x_1263_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1267_);
lean_ctor_set_uint64(v_reuseFailAlloc_1277_, sizeof(void*)*1, v_tid_1261_);
v___x_1269_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1271_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 4, v___x_1269_);
v___x_1271_ = v___x_1259_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_env_1249_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_nextMacroScope_1250_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v_ngen_1251_);
lean_ctor_set(v_reuseFailAlloc_1276_, 3, v_auxDeclNGen_1252_);
lean_ctor_set(v_reuseFailAlloc_1276_, 4, v___x_1269_);
lean_ctor_set(v_reuseFailAlloc_1276_, 5, v_cache_1253_);
lean_ctor_set(v_reuseFailAlloc_1276_, 6, v_recordedDeps_1254_);
lean_ctor_set(v_reuseFailAlloc_1276_, 7, v_messages_1255_);
lean_ctor_set(v_reuseFailAlloc_1276_, 8, v_infoState_1256_);
lean_ctor_set(v_reuseFailAlloc_1276_, 9, v_snapshotTasks_1257_);
v___x_1271_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1272_ = lean_st_ref_put(v___y_1224_, v___x_1271_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v___x_1265_);
v___x_1274_ = v___x_1245_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1265_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_1217_ = stack[0].m_obj;
lean_object* v_data_1218_ = stack[1].m_obj;
lean_object* v_ref_1219_ = stack[2].m_obj;
lean_object* v_msg_1220_ = stack[3].m_obj;
lean_object* v___y_1221_ = stack[4].m_obj;
lean_object* v___y_1222_ = stack[5].m_obj;
lean_object* v___y_1223_ = stack[6].m_obj;
lean_object* v___y_1224_ = stack[7].m_obj;
lean_object* v_res_1282_;
v_res_1282_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7___redArg(v_oldTraces_1217_, v_data_1218_, v_ref_1219_, v_msg_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
stack->m_obj
 = v_res_1282_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7___redArg___boxed(lean_object* v_oldTraces_1283_, lean_object* v_data_1284_, lean_object* v_ref_1285_, lean_object* v_msg_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7___redArg(v_oldTraces_1283_, v_data_1284_, v_ref_1285_, v_msg_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__10(lean_object* v_opts_1293_, lean_object* v_opt_1294_){
_start:
{
lean_object* v_name_1295_; lean_object* v_defValue_1296_; lean_object* v_map_1297_; lean_object* v___x_1298_; 
v_name_1295_ = lean_ctor_get(v_opt_1294_, 0);
v_defValue_1296_ = lean_ctor_get(v_opt_1294_, 1);
v_map_1297_ = lean_ctor_get(v_opts_1293_, 0);
v___x_1298_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1297_, v_name_1295_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_inc(v_defValue_1296_);
return v_defValue_1296_;
}
else
{
lean_object* v_val_1299_; 
v_val_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_val_1299_);
lean_dec_ref_known(v___x_1298_, 1);
if (lean_obj_tag(v_val_1299_) == 3)
{
lean_object* v_v_1300_; 
v_v_1300_ = lean_ctor_get(v_val_1299_, 0);
lean_inc(v_v_1300_);
lean_dec_ref_known(v_val_1299_, 1);
return v_v_1300_;
}
else
{
lean_dec(v_val_1299_);
lean_inc(v_defValue_1296_);
return v_defValue_1296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__10___boxed(lean_object* v_opts_1301_, lean_object* v_opt_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__10(v_opts_1301_, v_opt_1302_);
lean_dec_ref(v_opt_1302_);
lean_dec_ref(v_opts_1301_);
return v_res_1303_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__1(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__0));
v___x_1306_ = l_Lean_stringToMessageData(v___x_1305_);
return v___x_1306_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__2(void){
_start:
{
lean_object* v___x_1307_; double v___x_1308_; 
v___x_1307_ = lean_unsigned_to_nat(1000u);
v___x_1308_ = lean_float_of_nat(v___x_1307_);
return v___x_1308_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(lean_object* v_cls_1309_, uint8_t v_collapsed_1310_, lean_object* v_tag_1311_, lean_object* v_opts_1312_, uint8_t v_clsEnabled_1313_, lean_object* v_oldTraces_1314_, lean_object* v_msg_1315_, lean_object* v_resStartStop_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_fst_1329_; lean_object* v_snd_1330_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v_data_1334_; lean_object* v_fst_1337_; lean_object* v_snd_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; lean_object* v___y_1342_; lean_object* v_a_1343_; uint8_t v___y_1358_; double v___y_1390_; 
v_fst_1329_ = lean_ctor_get(v_resStartStop_1316_, 0);
lean_inc(v_fst_1329_);
v_snd_1330_ = lean_ctor_get(v_resStartStop_1316_, 1);
lean_inc(v_snd_1330_);
lean_dec_ref(v_resStartStop_1316_);
v_fst_1337_ = lean_ctor_get(v_snd_1330_, 0);
lean_inc(v_fst_1337_);
v_snd_1338_ = lean_ctor_get(v_snd_1330_, 1);
lean_inc(v_snd_1338_);
lean_dec(v_snd_1330_);
v___x_1339_ = l_Lean_trace_profiler;
v___x_1340_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5(v_opts_1312_, v___x_1339_);
if (v___x_1340_ == 0)
{
v___y_1358_ = v___x_1340_;
goto v___jp_1357_;
}
else
{
lean_object* v___x_1395_; uint8_t v___x_1396_; 
v___x_1395_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1396_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5(v_opts_1312_, v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; lean_object* v___x_1398_; double v___x_1399_; double v___x_1400_; double v___x_1401_; 
v___x_1397_ = l_Lean_trace_profiler_threshold;
v___x_1398_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__10(v_opts_1312_, v___x_1397_);
v___x_1399_ = lean_float_of_nat(v___x_1398_);
v___x_1400_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__2);
v___x_1401_ = lean_float_div(v___x_1399_, v___x_1400_);
v___y_1390_ = v___x_1401_;
goto v___jp_1389_;
}
else
{
lean_object* v___x_1402_; lean_object* v___x_1403_; double v___x_1404_; 
v___x_1402_ = l_Lean_trace_profiler_threshold;
v___x_1403_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__10(v_opts_1312_, v___x_1402_);
v___x_1404_ = lean_float_of_nat(v___x_1403_);
v___y_1390_ = v___x_1404_;
goto v___jp_1389_;
}
}
v___jp_1331_:
{
lean_object* v___x_1335_; 
lean_inc(v___y_1333_);
v___x_1335_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7___redArg(v_oldTraces_1314_, v_data_1334_, v___y_1333_, v___y_1332_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v___x_1336_; 
lean_dec_ref_known(v___x_1335_, 1);
v___x_1336_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8___redArg(v_fst_1329_);
return v___x_1336_;
}
else
{
lean_dec(v_fst_1329_);
return v___x_1335_;
}
}
v___jp_1341_:
{
uint8_t v_result_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; double v___x_1347_; lean_object* v_data_1348_; 
v_result_1344_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__9(v_fst_1329_);
v___x_1345_ = lean_box(v_result_1344_);
v___x_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
v___x_1347_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_1311_);
lean_inc_ref(v___x_1346_);
lean_inc(v_cls_1309_);
v_data_1348_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1348_, 0, v_cls_1309_);
lean_ctor_set(v_data_1348_, 1, v___x_1346_);
lean_ctor_set(v_data_1348_, 2, v_tag_1311_);
lean_ctor_set_float(v_data_1348_, sizeof(void*)*3, v___x_1347_);
lean_ctor_set_float(v_data_1348_, sizeof(void*)*3 + 8, v___x_1347_);
lean_ctor_set_uint8(v_data_1348_, sizeof(void*)*3 + 16, v_collapsed_1310_);
if (v___x_1340_ == 0)
{
lean_dec_ref_known(v___x_1346_, 1);
lean_dec(v_snd_1338_);
lean_dec(v_fst_1337_);
lean_dec_ref(v_tag_1311_);
lean_dec(v_cls_1309_);
v___y_1332_ = v_a_1343_;
v___y_1333_ = v___y_1342_;
v_data_1334_ = v_data_1348_;
goto v___jp_1331_;
}
else
{
lean_object* v_data_1349_; double v___x_1350_; double v___x_1351_; 
lean_dec_ref_known(v_data_1348_, 3);
v_data_1349_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1349_, 0, v_cls_1309_);
lean_ctor_set(v_data_1349_, 1, v___x_1346_);
lean_ctor_set(v_data_1349_, 2, v_tag_1311_);
v___x_1350_ = lean_unbox_float(v_fst_1337_);
lean_dec(v_fst_1337_);
lean_ctor_set_float(v_data_1349_, sizeof(void*)*3, v___x_1350_);
v___x_1351_ = lean_unbox_float(v_snd_1338_);
lean_dec(v_snd_1338_);
lean_ctor_set_float(v_data_1349_, sizeof(void*)*3 + 8, v___x_1351_);
lean_ctor_set_uint8(v_data_1349_, sizeof(void*)*3 + 16, v_collapsed_1310_);
v___y_1332_ = v_a_1343_;
v___y_1333_ = v___y_1342_;
v_data_1334_ = v_data_1349_;
goto v___jp_1331_;
}
}
v___jp_1352_:
{
lean_object* v_ref_1353_; lean_object* v___x_1354_; 
v_ref_1353_ = lean_ctor_get(v___y_1326_, 2);
lean_inc(v___y_1327_);
lean_inc_ref(v___y_1326_);
lean_inc(v___y_1325_);
lean_inc_ref(v___y_1324_);
lean_inc(v___y_1323_);
lean_inc_ref(v___y_1322_);
lean_inc(v___y_1321_);
lean_inc_ref(v___y_1320_);
lean_inc(v___y_1319_);
lean_inc(v___y_1318_);
lean_inc_ref(v___y_1317_);
lean_inc(v_fst_1329_);
v___x_1354_ = lean_apply_13(v_msg_1315_, v_fst_1329_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, lean_box(0));
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1354_, 1);
v___y_1342_ = v_ref_1353_;
v_a_1343_ = v_a_1355_;
goto v___jp_1341_;
}
else
{
lean_object* v___x_1356_; 
lean_dec_ref_known(v___x_1354_, 1);
v___x_1356_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___closed__1);
v___y_1342_ = v_ref_1353_;
v_a_1343_ = v___x_1356_;
goto v___jp_1341_;
}
}
v___jp_1357_:
{
if (v_clsEnabled_1313_ == 0)
{
if (v___y_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v_traceState_1360_; lean_object* v_env_1361_; lean_object* v_nextMacroScope_1362_; lean_object* v_ngen_1363_; lean_object* v_auxDeclNGen_1364_; lean_object* v_cache_1365_; lean_object* v_recordedDeps_1366_; lean_object* v_messages_1367_; lean_object* v_infoState_1368_; lean_object* v_snapshotTasks_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1388_; 
lean_dec(v_snd_1338_);
lean_dec(v_fst_1337_);
lean_dec_ref(v_msg_1315_);
lean_dec_ref(v_tag_1311_);
lean_dec(v_cls_1309_);
v___x_1359_ = lean_st_ref_take(v___y_1327_);
v_traceState_1360_ = lean_ctor_get(v___x_1359_, 4);
v_env_1361_ = lean_ctor_get(v___x_1359_, 0);
v_nextMacroScope_1362_ = lean_ctor_get(v___x_1359_, 1);
v_ngen_1363_ = lean_ctor_get(v___x_1359_, 2);
v_auxDeclNGen_1364_ = lean_ctor_get(v___x_1359_, 3);
v_cache_1365_ = lean_ctor_get(v___x_1359_, 5);
v_recordedDeps_1366_ = lean_ctor_get(v___x_1359_, 6);
v_messages_1367_ = lean_ctor_get(v___x_1359_, 7);
v_infoState_1368_ = lean_ctor_get(v___x_1359_, 8);
v_snapshotTasks_1369_ = lean_ctor_get(v___x_1359_, 9);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1371_ = v___x_1359_;
v_isShared_1372_ = v_isSharedCheck_1388_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_snapshotTasks_1369_);
lean_inc(v_infoState_1368_);
lean_inc(v_messages_1367_);
lean_inc(v_recordedDeps_1366_);
lean_inc(v_cache_1365_);
lean_inc(v_traceState_1360_);
lean_inc(v_auxDeclNGen_1364_);
lean_inc(v_ngen_1363_);
lean_inc(v_nextMacroScope_1362_);
lean_inc(v_env_1361_);
lean_dec(v___x_1359_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1388_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
uint64_t v_tid_1373_; lean_object* v_traces_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1387_; 
v_tid_1373_ = lean_ctor_get_uint64(v_traceState_1360_, sizeof(void*)*1);
v_traces_1374_ = lean_ctor_get(v_traceState_1360_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_traceState_1360_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1376_ = v_traceState_1360_;
v_isShared_1377_ = v_isSharedCheck_1387_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_traces_1374_);
lean_dec(v_traceState_1360_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1387_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1378_; lean_object* v___x_1380_; 
v___x_1378_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1314_, v_traces_1374_);
lean_dec_ref(v_traces_1374_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v___x_1378_);
v___x_1380_ = v___x_1376_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1378_);
lean_ctor_set_uint64(v_reuseFailAlloc_1386_, sizeof(void*)*1, v_tid_1373_);
v___x_1380_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1382_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 4, v___x_1380_);
v___x_1382_ = v___x_1371_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_env_1361_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_nextMacroScope_1362_);
lean_ctor_set(v_reuseFailAlloc_1385_, 2, v_ngen_1363_);
lean_ctor_set(v_reuseFailAlloc_1385_, 3, v_auxDeclNGen_1364_);
lean_ctor_set(v_reuseFailAlloc_1385_, 4, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1385_, 5, v_cache_1365_);
lean_ctor_set(v_reuseFailAlloc_1385_, 6, v_recordedDeps_1366_);
lean_ctor_set(v_reuseFailAlloc_1385_, 7, v_messages_1367_);
lean_ctor_set(v_reuseFailAlloc_1385_, 8, v_infoState_1368_);
lean_ctor_set(v_reuseFailAlloc_1385_, 9, v_snapshotTasks_1369_);
v___x_1382_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1383_ = lean_st_ref_put(v___y_1327_, v___x_1382_);
v___x_1384_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8___redArg(v_fst_1329_);
return v___x_1384_;
}
}
}
}
}
else
{
goto v___jp_1352_;
}
}
else
{
goto v___jp_1352_;
}
}
v___jp_1389_:
{
double v___x_1391_; double v___x_1392_; double v___x_1393_; uint8_t v___x_1394_; 
v___x_1391_ = lean_unbox_float(v_snd_1338_);
v___x_1392_ = lean_unbox_float(v_fst_1337_);
v___x_1393_ = lean_float_sub(v___x_1391_, v___x_1392_);
v___x_1394_ = lean_float_decLt(v___y_1390_, v___x_1393_);
v___y_1358_ = v___x_1394_;
goto v___jp_1357_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1309_ = stack[0].m_obj;
uint8_t v_collapsed_1310_ = stack[1].m_num;
lean_object* v_tag_1311_ = stack[2].m_obj;
lean_object* v_opts_1312_ = stack[3].m_obj;
uint8_t v_clsEnabled_1313_ = stack[4].m_num;
lean_object* v_oldTraces_1314_ = stack[5].m_obj;
lean_object* v_msg_1315_ = stack[6].m_obj;
lean_object* v_resStartStop_1316_ = stack[7].m_obj;
lean_object* v___y_1317_ = stack[8].m_obj;
lean_object* v___y_1318_ = stack[9].m_obj;
lean_object* v___y_1319_ = stack[10].m_obj;
lean_object* v___y_1320_ = stack[11].m_obj;
lean_object* v___y_1321_ = stack[12].m_obj;
lean_object* v___y_1322_ = stack[13].m_obj;
lean_object* v___y_1323_ = stack[14].m_obj;
lean_object* v___y_1324_ = stack[15].m_obj;
lean_object* v___y_1325_ = stack[16].m_obj;
lean_object* v___y_1326_ = stack[17].m_obj;
lean_object* v___y_1327_ = stack[18].m_obj;
lean_object* v_res_1405_;
v_res_1405_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(v_cls_1309_, v_collapsed_1310_, v_tag_1311_, v_opts_1312_, v_clsEnabled_1313_, v_oldTraces_1314_, v_msg_1315_, v_resStartStop_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
stack->m_obj
 = v_res_1405_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___boxed(lean_object** _args){
lean_object* v_cls_1406_ = _args[0];
lean_object* v_collapsed_1407_ = _args[1];
lean_object* v_tag_1408_ = _args[2];
lean_object* v_opts_1409_ = _args[3];
lean_object* v_clsEnabled_1410_ = _args[4];
lean_object* v_oldTraces_1411_ = _args[5];
lean_object* v_msg_1412_ = _args[6];
lean_object* v_resStartStop_1413_ = _args[7];
lean_object* v___y_1414_ = _args[8];
lean_object* v___y_1415_ = _args[9];
lean_object* v___y_1416_ = _args[10];
lean_object* v___y_1417_ = _args[11];
lean_object* v___y_1418_ = _args[12];
lean_object* v___y_1419_ = _args[13];
lean_object* v___y_1420_ = _args[14];
lean_object* v___y_1421_ = _args[15];
lean_object* v___y_1422_ = _args[16];
lean_object* v___y_1423_ = _args[17];
lean_object* v___y_1424_ = _args[18];
lean_object* v___y_1425_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_1426_; uint8_t v_clsEnabled_boxed_1427_; lean_object* v_res_1428_; 
v_collapsed_boxed_1426_ = lean_unbox(v_collapsed_1407_);
v_clsEnabled_boxed_1427_ = lean_unbox(v_clsEnabled_1410_);
v_res_1428_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(v_cls_1406_, v_collapsed_boxed_1426_, v_tag_1408_, v_opts_1409_, v_clsEnabled_boxed_1427_, v_oldTraces_1411_, v_msg_1412_, v_resStartStop_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec_ref(v_opts_1409_);
return v_res_1428_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1430_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___closed__0));
v___x_1431_ = l_Lean_stringToMessageData(v___x_1430_);
return v___x_1431_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3(lean_object* v_as_1432_, size_t v_sz_1433_, size_t v_i_1434_, lean_object* v_b_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_a_1449_; uint8_t v___x_1453_; 
v___x_1453_ = lean_usize_dec_lt(v_i_1434_, v_sz_1433_);
if (v___x_1453_ == 0)
{
lean_object* v___x_1454_; 
v___x_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1454_, 0, v_b_1435_);
return v___x_1454_;
}
else
{
lean_object* v_a_1455_; lean_object* v_toCold_1456_; lean_object* v_options_1457_; lean_object* v_fst_1458_; lean_object* v_snd_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1479_; 
v_a_1455_ = lean_array_uget(v_as_1432_, v_i_1434_);
v_toCold_1456_ = lean_ctor_get(v___y_1445_, 0);
v_options_1457_ = lean_ctor_get(v_toCold_1456_, 2);
v_fst_1458_ = lean_ctor_get(v_a_1455_, 0);
v_snd_1459_ = lean_ctor_get(v_a_1455_, 1);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_a_1455_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1461_ = v_a_1455_;
v_isShared_1462_ = v_isSharedCheck_1479_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_snd_1459_);
lean_inc(v_fst_1458_);
lean_dec(v_a_1455_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1479_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v_inheritedTraceOptions_1463_; uint8_t v_hasTrace_1464_; lean_object* v___x_1465_; 
v_inheritedTraceOptions_1463_ = lean_ctor_get(v_toCold_1456_, 11);
v_hasTrace_1464_ = lean_ctor_get_uint8(v_options_1457_, sizeof(void*)*1);
v___x_1465_ = lean_box(0);
if (v_hasTrace_1464_ == 0)
{
lean_del_object(v___x_1461_);
lean_dec(v_snd_1459_);
lean_dec(v_fst_1458_);
v_a_1449_ = v___x_1465_;
goto v___jp_1448_;
}
else
{
lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v___x_1466_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__9));
v___x_1467_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12);
v___x_1468_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1463_, v_options_1457_, v___x_1467_);
if (v___x_1468_ == 0)
{
lean_del_object(v___x_1461_);
lean_dec(v_snd_1459_);
lean_dec(v_fst_1458_);
v_a_1449_ = v___x_1465_;
goto v___jp_1448_;
}
else
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1469_ = l_Lean_MessageData_ofName(v_fst_1458_);
v___x_1470_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___closed__1);
if (v_isShared_1462_ == 0)
{
lean_ctor_set_tag(v___x_1461_, 7);
lean_ctor_set(v___x_1461_, 1, v___x_1470_);
lean_ctor_set(v___x_1461_, 0, v___x_1469_);
v___x_1472_ = v___x_1461_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v___x_1470_);
v___x_1472_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1473_ = l_Nat_reprFast(v_snd_1459_);
v___x_1474_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
v___x_1475_ = l_Lean_MessageData_ofFormat(v___x_1474_);
v___x_1476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1472_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v___x_1477_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v___x_1466_, v___x_1476_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_dec_ref_known(v___x_1477_, 1);
v_a_1449_ = v___x_1465_;
goto v___jp_1448_;
}
else
{
return v___x_1477_;
}
}
}
}
}
}
v___jp_1448_:
{
size_t v___x_1450_; size_t v___x_1451_; 
v___x_1450_ = ((size_t)1ULL);
v___x_1451_ = lean_usize_add(v_i_1434_, v___x_1450_);
v_i_1434_ = v___x_1451_;
v_b_1435_ = v_a_1449_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1432_ = stack[0].m_obj;
size_t v_sz_1433_ = stack[1].m_num;
size_t v_i_1434_ = stack[2].m_num;
lean_object* v_b_1435_ = stack[3].m_obj;
lean_object* v___y_1436_ = stack[4].m_obj;
lean_object* v___y_1437_ = stack[5].m_obj;
lean_object* v___y_1438_ = stack[6].m_obj;
lean_object* v___y_1439_ = stack[7].m_obj;
lean_object* v___y_1440_ = stack[8].m_obj;
lean_object* v___y_1441_ = stack[9].m_obj;
lean_object* v___y_1442_ = stack[10].m_obj;
lean_object* v___y_1443_ = stack[11].m_obj;
lean_object* v___y_1444_ = stack[12].m_obj;
lean_object* v___y_1445_ = stack[13].m_obj;
lean_object* v___y_1446_ = stack[14].m_obj;
lean_object* v_res_1480_;
v_res_1480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3(v_as_1432_, v_sz_1433_, v_i_1434_, v_b_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
stack->m_obj
 = v_res_1480_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___boxed(lean_object* v_as_1481_, lean_object* v_sz_1482_, lean_object* v_i_1483_, lean_object* v_b_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
size_t v_sz_boxed_1497_; size_t v_i_boxed_1498_; lean_object* v_res_1499_; 
v_sz_boxed_1497_ = lean_unbox_usize(v_sz_1482_);
lean_dec(v_sz_1482_);
v_i_boxed_1498_ = lean_unbox_usize(v_i_1483_);
lean_dec(v_i_1483_);
v_res_1499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3(v_as_1481_, v_sz_boxed_1497_, v_i_boxed_1498_, v_b_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec_ref(v_as_1481_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8(lean_object* v_x_1500_, lean_object* v_x_1501_){
_start:
{
if (lean_obj_tag(v_x_1501_) == 0)
{
return v_x_1500_;
}
else
{
lean_object* v_key_1502_; lean_object* v_value_1503_; lean_object* v_tail_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v_key_1502_ = lean_ctor_get(v_x_1501_, 0);
v_value_1503_ = lean_ctor_get(v_x_1501_, 1);
v_tail_1504_ = lean_ctor_get(v_x_1501_, 2);
lean_inc(v_value_1503_);
lean_inc(v_key_1502_);
v___x_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1505_, 0, v_key_1502_);
lean_ctor_set(v___x_1505_, 1, v_value_1503_);
v___x_1506_ = lean_array_push(v_x_1500_, v___x_1505_);
v_x_1500_ = v___x_1506_;
v_x_1501_ = v_tail_1504_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___boxed(lean_object* v_x_1508_, lean_object* v_x_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8(v_x_1508_, v_x_1509_);
lean_dec(v_x_1509_);
return v_res_1510_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9(lean_object* v_as_1511_, size_t v_i_1512_, size_t v_stop_1513_, lean_object* v_b_1514_){
_start:
{
uint8_t v___x_1515_; 
v___x_1515_ = lean_usize_dec_eq(v_i_1512_, v_stop_1513_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; size_t v___x_1518_; size_t v___x_1519_; 
v___x_1516_ = lean_array_uget_borrowed(v_as_1511_, v_i_1512_);
v___x_1517_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8(v_b_1514_, v___x_1516_);
v___x_1518_ = ((size_t)1ULL);
v___x_1519_ = lean_usize_add(v_i_1512_, v___x_1518_);
v_i_1512_ = v___x_1519_;
v_b_1514_ = v___x_1517_;
goto _start;
}
else
{
return v_b_1514_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1511_ = stack[0].m_obj;
size_t v_i_1512_ = stack[1].m_num;
size_t v_stop_1513_ = stack[2].m_num;
lean_object* v_b_1514_ = stack[3].m_obj;
lean_object* v_res_1521_;
v_res_1521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9(v_as_1511_, v_i_1512_, v_stop_1513_, v_b_1514_);
stack->m_obj
 = v_res_1521_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9___boxed(lean_object* v_as_1522_, lean_object* v_i_1523_, lean_object* v_stop_1524_, lean_object* v_b_1525_){
_start:
{
size_t v_i_boxed_1526_; size_t v_stop_boxed_1527_; lean_object* v_res_1528_; 
v_i_boxed_1526_ = lean_unbox_usize(v_i_1523_);
lean_dec(v_i_1523_);
v_stop_boxed_1527_ = lean_unbox_usize(v_stop_1524_);
lean_dec(v_stop_1524_);
v_res_1528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9(v_as_1522_, v_i_boxed_1526_, v_stop_boxed_1527_, v_b_1525_);
lean_dec_ref(v_as_1522_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12___redArg(lean_object* v_hi_1529_, lean_object* v_pivot_1530_, lean_object* v_as_1531_, lean_object* v_i_1532_, lean_object* v_k_1533_){
_start:
{
uint8_t v___x_1534_; 
v___x_1534_ = lean_nat_dec_lt(v_k_1533_, v_hi_1529_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec(v_k_1533_);
v___x_1535_ = lean_array_fswap(v_as_1531_, v_i_1532_, v_hi_1529_);
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v_i_1532_);
lean_ctor_set(v___x_1536_, 1, v___x_1535_);
return v___x_1536_;
}
else
{
lean_object* v_snd_1537_; lean_object* v___x_1538_; lean_object* v_snd_1539_; uint8_t v___x_1540_; 
v_snd_1537_ = lean_ctor_get(v_pivot_1530_, 1);
v___x_1538_ = lean_array_fget_borrowed(v_as_1531_, v_k_1533_);
v_snd_1539_ = lean_ctor_get(v___x_1538_, 1);
v___x_1540_ = lean_nat_dec_lt(v_snd_1537_, v_snd_1539_);
if (v___x_1540_ == 0)
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = lean_unsigned_to_nat(1u);
v___x_1542_ = lean_nat_add(v_k_1533_, v___x_1541_);
lean_dec(v_k_1533_);
v_k_1533_ = v___x_1542_;
goto _start;
}
else
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1544_ = lean_array_fswap(v_as_1531_, v_i_1532_, v_k_1533_);
v___x_1545_ = lean_unsigned_to_nat(1u);
v___x_1546_ = lean_nat_add(v_i_1532_, v___x_1545_);
lean_dec(v_i_1532_);
v___x_1547_ = lean_nat_add(v_k_1533_, v___x_1545_);
lean_dec(v_k_1533_);
v_as_1531_ = v___x_1544_;
v_i_1532_ = v___x_1546_;
v_k_1533_ = v___x_1547_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12___redArg___boxed(lean_object* v_hi_1549_, lean_object* v_pivot_1550_, lean_object* v_as_1551_, lean_object* v_i_1552_, lean_object* v_k_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12___redArg(v_hi_1549_, v_pivot_1550_, v_as_1551_, v_i_1552_, v_k_1553_);
lean_dec_ref(v_pivot_1550_);
lean_dec(v_hi_1549_);
return v_res_1554_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg___lam__0(lean_object* v_a_1555_, lean_object* v_b_1556_){
_start:
{
lean_object* v_snd_1557_; lean_object* v_snd_1558_; uint8_t v___x_1559_; 
v_snd_1557_ = lean_ctor_get(v_b_1556_, 1);
v_snd_1558_ = lean_ctor_get(v_a_1555_, 1);
v___x_1559_ = lean_nat_dec_lt(v_snd_1557_, v_snd_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1555_ = stack[0].m_obj;
lean_object* v_b_1556_ = stack[1].m_obj;
uint8_t v_res_1560_;
v_res_1560_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg___lam__0(v_a_1555_, v_b_1556_);
stack->m_num = v_res_1560_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg___lam__0___boxed(lean_object* v_a_1561_, lean_object* v_b_1562_){
_start:
{
uint8_t v_res_1563_; lean_object* v_r_1564_; 
v_res_1563_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg___lam__0(v_a_1561_, v_b_1562_);
lean_dec_ref(v_b_1562_);
lean_dec_ref(v_a_1561_);
v_r_1564_ = lean_box(v_res_1563_);
return v_r_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg(lean_object* v_n_1565_, lean_object* v_as_1566_, lean_object* v_lo_1567_, lean_object* v_hi_1568_){
_start:
{
lean_object* v___y_1570_; uint8_t v___x_1580_; 
v___x_1580_ = lean_nat_dec_lt(v_lo_1567_, v_hi_1568_);
if (v___x_1580_ == 0)
{
lean_dec(v_lo_1567_);
return v_as_1566_;
}
else
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v_mid_1583_; lean_object* v___y_1585_; lean_object* v___y_1591_; lean_object* v___x_1596_; lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1581_ = lean_nat_add(v_lo_1567_, v_hi_1568_);
v___x_1582_ = lean_unsigned_to_nat(1u);
v_mid_1583_ = lean_nat_shiftr(v___x_1581_, v___x_1582_);
lean_dec(v___x_1581_);
v___x_1596_ = lean_array_fget_borrowed(v_as_1566_, v_mid_1583_);
v___x_1597_ = lean_array_fget_borrowed(v_as_1566_, v_lo_1567_);
v___x_1598_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg___lam__0(v___x_1596_, v___x_1597_);
if (v___x_1598_ == 0)
{
v___y_1591_ = v_as_1566_;
goto v___jp_1590_;
}
else
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_array_fswap(v_as_1566_, v_lo_1567_, v_mid_1583_);
v___y_1591_ = v___x_1599_;
goto v___jp_1590_;
}
v___jp_1584_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v___x_1586_ = lean_array_fget_borrowed(v___y_1585_, v_mid_1583_);
v___x_1587_ = lean_array_fget_borrowed(v___y_1585_, v_hi_1568_);
v___x_1588_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg___lam__0(v___x_1586_, v___x_1587_);
if (v___x_1588_ == 0)
{
lean_dec(v_mid_1583_);
v___y_1570_ = v___y_1585_;
goto v___jp_1569_;
}
else
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_array_fswap(v___y_1585_, v_mid_1583_, v_hi_1568_);
lean_dec(v_mid_1583_);
v___y_1570_ = v___x_1589_;
goto v___jp_1569_;
}
}
v___jp_1590_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1592_ = lean_array_fget_borrowed(v___y_1591_, v_hi_1568_);
v___x_1593_ = lean_array_fget_borrowed(v___y_1591_, v_lo_1567_);
v___x_1594_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg___lam__0(v___x_1592_, v___x_1593_);
if (v___x_1594_ == 0)
{
v___y_1585_ = v___y_1591_;
goto v___jp_1584_;
}
else
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_array_fswap(v___y_1591_, v_lo_1567_, v_hi_1568_);
v___y_1585_ = v___x_1595_;
goto v___jp_1584_;
}
}
}
v___jp_1569_:
{
lean_object* v_pivot_1571_; lean_object* v___x_1572_; lean_object* v_fst_1573_; lean_object* v_snd_1574_; uint8_t v___x_1575_; 
v_pivot_1571_ = lean_array_fget(v___y_1570_, v_hi_1568_);
lean_inc_n(v_lo_1567_, 2);
v___x_1572_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12___redArg(v_hi_1568_, v_pivot_1571_, v___y_1570_, v_lo_1567_, v_lo_1567_);
lean_dec(v_pivot_1571_);
v_fst_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_fst_1573_);
v_snd_1574_ = lean_ctor_get(v___x_1572_, 1);
lean_inc(v_snd_1574_);
lean_dec_ref(v___x_1572_);
v___x_1575_ = lean_nat_dec_le(v_hi_1568_, v_fst_1573_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1576_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg(v_n_1565_, v_snd_1574_, v_lo_1567_, v_fst_1573_);
v___x_1577_ = lean_unsigned_to_nat(1u);
v___x_1578_ = lean_nat_add(v_fst_1573_, v___x_1577_);
lean_dec(v_fst_1573_);
v_as_1566_ = v___x_1576_;
v_lo_1567_ = v___x_1578_;
goto _start;
}
else
{
lean_dec(v_fst_1573_);
lean_dec(v_lo_1567_);
return v_snd_1574_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg___boxed(lean_object* v_n_1600_, lean_object* v_as_1601_, lean_object* v_lo_1602_, lean_object* v_hi_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg(v_n_1600_, v_as_1601_, v_lo_1602_, v_hi_1603_);
lean_dec(v_hi_1603_);
lean_dec(v_n_1600_);
return v_res_1604_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__3(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = lean_box(0);
v___x_1613_ = lean_unsigned_to_nat(16u);
v___x_1614_ = lean_mk_array(v___x_1613_, v___x_1612_);
return v___x_1614_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__4(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__3, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__3);
v___x_1616_ = lean_unsigned_to_nat(0u);
v___x_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
lean_ctor_set(v___x_1617_, 1, v___x_1615_);
return v___x_1617_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__5(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__4);
v___x_1619_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
lean_ctor_set(v___x_1619_, 2, v___x_1618_);
lean_ctor_set(v___x_1619_, 3, v___x_1618_);
return v___x_1619_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__6(void){
_start:
{
lean_object* v___x_1620_; double v___x_1621_; 
v___x_1620_ = lean_unsigned_to_nat(1000000000u);
v___x_1621_ = lean_float_of_nat(v___x_1620_);
return v___x_1621_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5(lean_object* v___x_1622_, lean_object* v___f_1623_, lean_object* v___f_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(v___x_1622_, v___y_1635_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_config_1638_; lean_object* v_a_1639_; lean_object* v_maxSteps_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___f_1649_; lean_object* v___f_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___f_1653_; lean_object* v___x_1654_; lean_object* v_target_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v_config_1638_ = lean_ctor_get(v___y_1625_, 0);
v_a_1639_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1637_, 1);
v_maxSteps_1640_ = lean_ctor_get(v_config_1638_, 1);
v___x_1641_ = lean_unsigned_to_nat(2u);
lean_inc_n(v_maxSteps_1640_, 2);
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v_maxSteps_1640_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = 1;
v___x_1644_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__0));
v___x_1645_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__2));
v___x_1646_ = lean_unsigned_to_nat(0u);
v___x_1647_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__5);
v___x_1648_ = lean_st_mk_ref(v___x_1647_);
lean_inc(v___x_1648_);
v___f_1649_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2___boxed), 15, 3);
lean_closure_set(v___f_1649_, 0, v___x_1648_);
lean_closure_set(v___f_1649_, 1, v_a_1639_);
lean_closure_set(v___f_1649_, 2, v___x_1645_);
v___f_1650_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3___boxed), 13, 2);
lean_closure_set(v___f_1650_, 0, v___x_1644_);
lean_closure_set(v___f_1650_, 1, v___f_1649_);
v___x_1651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___f_1623_);
lean_ctor_set(v___x_1651_, 1, v___f_1650_);
v___x_1652_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1652_, 0, v_maxSteps_1640_);
lean_ctor_set_uint8(v___x_1652_, sizeof(void*)*1, v___x_1643_);
v___f_1653_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4___boxed), 16, 4);
lean_closure_set(v___f_1653_, 0, v___x_1652_);
lean_closure_set(v___f_1653_, 1, v___x_1651_);
lean_closure_set(v___f_1653_, 2, v___x_1642_);
lean_closure_set(v___f_1653_, 3, v___x_1646_);
v___x_1654_ = lean_st_ref_get(v___y_1626_);
v_target_1655_ = lean_ctor_get(v___x_1654_, 2);
lean_inc_ref(v_target_1655_);
lean_dec(v___x_1654_);
v___x_1656_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_1655_);
lean_dec_ref(v_target_1655_);
v___x_1657_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg(v___x_1656_, v___f_1653_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___y_1660_; lean_object* v_toCold_1677_; lean_object* v_options_1678_; uint8_t v_hasTrace_1679_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
v_toCold_1677_ = lean_ctor_get(v___y_1634_, 0);
v_options_1678_ = lean_ctor_get(v_toCold_1677_, 2);
v_hasTrace_1679_ = lean_ctor_get_uint8(v_options_1678_, sizeof(void*)*1);
if (v_hasTrace_1679_ == 0)
{
lean_dec(v___x_1648_);
lean_dec_ref(v___f_1624_);
return v___x_1657_;
}
else
{
lean_object* v_inheritedTraceOptions_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v_a_1688_; lean_object* v___y_1701_; lean_object* v___y_1702_; lean_object* v___y_1703_; lean_object* v_a_1704_; lean_object* v___y_1707_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v_a_1710_; lean_object* v___y_1720_; lean_object* v___y_1721_; lean_object* v___y_1722_; lean_object* v_a_1723_; 
v_inheritedTraceOptions_1680_ = lean_ctor_get(v_toCold_1677_, 11);
v___x_1681_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__9));
v___x_1682_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___closed__12);
v___x_1683_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1680_, v_options_1678_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_dec(v___x_1648_);
lean_dec_ref(v___f_1624_);
return v___x_1657_;
}
else
{
lean_object* v___x_1725_; lean_object* v___y_1727_; lean_object* v___y_1728_; size_t v___y_1729_; lean_object* v___y_1730_; size_t v___y_1731_; lean_object* v___y_1759_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; lean_object* v___y_1785_; lean_object* v___y_1788_; lean_object* v_statistics_1794_; lean_object* v_size_1795_; lean_object* v_buckets_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1657_, 1);
v___x_1725_ = lean_st_ref_get(v___x_1648_);
lean_dec(v___x_1648_);
v_statistics_1794_ = lean_ctor_get(v___x_1725_, 3);
lean_inc_ref(v_statistics_1794_);
lean_dec(v___x_1725_);
v_size_1795_ = lean_ctor_get(v_statistics_1794_, 0);
lean_inc(v_size_1795_);
v_buckets_1796_ = lean_ctor_get(v_statistics_1794_, 1);
lean_inc_ref(v_buckets_1796_);
lean_dec_ref(v_statistics_1794_);
v___x_1797_ = lean_mk_empty_array_with_capacity(v_size_1795_);
lean_dec(v_size_1795_);
v___x_1798_ = lean_array_get_size(v_buckets_1796_);
v___x_1799_ = lean_nat_dec_lt(v___x_1646_, v___x_1798_);
if (v___x_1799_ == 0)
{
lean_dec_ref(v_buckets_1796_);
v___y_1788_ = v___x_1797_;
goto v___jp_1787_;
}
else
{
size_t v___x_1800_; size_t v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = ((size_t)0ULL);
v___x_1801_ = lean_usize_of_nat(v___x_1798_);
v___x_1802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9(v_buckets_1796_, v___x_1800_, v___x_1801_, v___x_1797_);
lean_dec_ref(v_buckets_1796_);
v___y_1788_ = v___x_1802_;
goto v___jp_1787_;
}
v___jp_1726_:
{
lean_object* v___x_1732_; lean_object* v_a_1733_; lean_object* v___x_1734_; uint8_t v___x_1735_; 
v___x_1732_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___redArg(v___y_1635_);
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref(v___x_1732_);
v___x_1734_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1735_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5(v_options_1678_, v___x_1734_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = lean_io_mono_nanos_now();
v___x_1737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3(v___y_1730_, v___y_1731_, v___y_1729_, v___y_1727_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec_ref(v___y_1730_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_dec_ref_known(v___x_1737_, 1);
v___y_1701_ = v___y_1728_;
v___y_1702_ = v___x_1736_;
v___y_1703_ = v_a_1733_;
v_a_1704_ = v___y_1727_;
goto v___jp_1700_;
}
else
{
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref_known(v___x_1737_, 1);
v___y_1701_ = v___y_1728_;
v___y_1702_ = v___x_1736_;
v___y_1703_ = v_a_1733_;
v_a_1704_ = v_a_1738_;
goto v___jp_1700_;
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
v_a_1739_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1737_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1737_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set_tag(v___x_1741_, 0);
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
v___y_1685_ = v___y_1728_;
v___y_1686_ = v___x_1736_;
v___y_1687_ = v_a_1733_;
v_a_1688_ = v___x_1744_;
goto v___jp_1684_;
}
}
}
}
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = lean_io_get_num_heartbeats();
v___x_1748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3(v___y_1730_, v___y_1731_, v___y_1729_, v___y_1727_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec_ref(v___y_1730_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_dec_ref_known(v___x_1748_, 1);
v___y_1720_ = v___x_1747_;
v___y_1721_ = v___y_1728_;
v___y_1722_ = v_a_1733_;
v_a_1723_ = v___y_1727_;
goto v___jp_1719_;
}
else
{
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref_known(v___x_1748_, 1);
v___y_1720_ = v___x_1747_;
v___y_1721_ = v___y_1728_;
v___y_1722_ = v_a_1733_;
v_a_1723_ = v_a_1749_;
goto v___jp_1719_;
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
v_a_1750_ = lean_ctor_get(v___x_1748_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1748_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1748_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1748_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
lean_ctor_set_tag(v___x_1752_, 0);
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
v___y_1707_ = v___y_1728_;
v___y_1708_ = v___x_1747_;
v___y_1709_ = v_a_1733_;
v_a_1710_ = v___x_1755_;
goto v___jp_1706_;
}
}
}
}
}
}
v___jp_1758_:
{
lean_object* v___x_1760_; size_t v_sz_1761_; size_t v___x_1762_; lean_object* v___x_1763_; 
v___x_1760_ = lean_box(0);
v_sz_1761_ = lean_array_size(v___y_1759_);
v___x_1762_ = ((size_t)0ULL);
v___x_1763_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1));
if (v___x_1683_ == 0)
{
lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = l_Lean_trace_profiler;
v___x_1765_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5(v_options_1678_, v___x_1764_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; 
lean_dec_ref(v___f_1624_);
v___x_1766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3(v___y_1759_, v_sz_1761_, v___x_1762_, v___x_1760_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec_ref(v___y_1759_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; 
v_unused_1774_ = lean_ctor_get(v___x_1766_, 0);
lean_dec(v_unused_1774_);
v___x_1768_ = v___x_1766_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_dec(v___x_1766_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v_a_1658_);
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1658_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
else
{
v___y_1660_ = v___x_1766_;
goto v___jp_1659_;
}
}
else
{
v___y_1727_ = v___x_1760_;
v___y_1728_ = v___x_1763_;
v___y_1729_ = v___x_1762_;
v___y_1730_ = v___y_1759_;
v___y_1731_ = v_sz_1761_;
goto v___jp_1726_;
}
}
else
{
v___y_1727_ = v___x_1760_;
v___y_1728_ = v___x_1763_;
v___y_1729_ = v___x_1762_;
v___y_1730_ = v___y_1759_;
v___y_1731_ = v_sz_1761_;
goto v___jp_1726_;
}
}
v___jp_1775_:
{
lean_object* v___x_1780_; 
v___x_1780_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg(v___y_1777_, v___y_1776_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec(v___y_1777_);
v___y_1759_ = v___x_1780_;
goto v___jp_1758_;
}
v___jp_1781_:
{
uint8_t v___x_1786_; 
v___x_1786_ = lean_nat_dec_le(v___y_1785_, v___y_1783_);
if (v___x_1786_ == 0)
{
lean_dec(v___y_1783_);
lean_inc(v___y_1785_);
v___y_1776_ = v___y_1782_;
v___y_1777_ = v___y_1784_;
v___y_1778_ = v___y_1785_;
v___y_1779_ = v___y_1785_;
goto v___jp_1775_;
}
else
{
v___y_1776_ = v___y_1782_;
v___y_1777_ = v___y_1784_;
v___y_1778_ = v___y_1785_;
v___y_1779_ = v___y_1783_;
goto v___jp_1775_;
}
}
v___jp_1787_:
{
lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1789_ = lean_array_get_size(v___y_1788_);
v___x_1790_ = lean_nat_dec_eq(v___x_1789_, v___x_1646_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v___x_1791_ = lean_unsigned_to_nat(1u);
v___x_1792_ = lean_nat_sub(v___x_1789_, v___x_1791_);
v___x_1793_ = lean_nat_dec_le(v___x_1646_, v___x_1792_);
if (v___x_1793_ == 0)
{
lean_inc(v___x_1792_);
v___y_1782_ = v___y_1788_;
v___y_1783_ = v___x_1792_;
v___y_1784_ = v___x_1789_;
v___y_1785_ = v___x_1792_;
goto v___jp_1781_;
}
else
{
v___y_1782_ = v___y_1788_;
v___y_1783_ = v___x_1792_;
v___y_1784_ = v___x_1789_;
v___y_1785_ = v___x_1646_;
goto v___jp_1781_;
}
}
else
{
v___y_1759_ = v___y_1788_;
goto v___jp_1758_;
}
}
}
v___jp_1684_:
{
lean_object* v___x_1689_; double v___x_1690_; double v___x_1691_; double v___x_1692_; double v___x_1693_; double v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1689_ = lean_io_mono_nanos_now();
v___x_1690_ = lean_float_of_nat(v___y_1686_);
v___x_1691_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__6, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__6);
v___x_1692_ = lean_float_div(v___x_1690_, v___x_1691_);
v___x_1693_ = lean_float_of_nat(v___x_1689_);
v___x_1694_ = lean_float_div(v___x_1693_, v___x_1691_);
v___x_1695_ = lean_box_float(v___x_1692_);
v___x_1696_ = lean_box_float(v___x_1694_);
v___x_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1695_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v_a_1688_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
lean_inc_ref(v___y_1685_);
v___x_1699_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(v___x_1681_, v___x_1643_, v___y_1685_, v_options_1678_, v___x_1683_, v___y_1687_, v___f_1624_, v___x_1698_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
v___y_1660_ = v___x_1699_;
goto v___jp_1659_;
}
v___jp_1700_:
{
lean_object* v___x_1705_; 
v___x_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1705_, 0, v_a_1704_);
v___y_1685_ = v___y_1701_;
v___y_1686_ = v___y_1702_;
v___y_1687_ = v___y_1703_;
v_a_1688_ = v___x_1705_;
goto v___jp_1684_;
}
v___jp_1706_:
{
lean_object* v___x_1711_; double v___x_1712_; double v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1711_ = lean_io_get_num_heartbeats();
v___x_1712_ = lean_float_of_nat(v___y_1708_);
v___x_1713_ = lean_float_of_nat(v___x_1711_);
v___x_1714_ = lean_box_float(v___x_1712_);
v___x_1715_ = lean_box_float(v___x_1713_);
v___x_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1714_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
v___x_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1717_, 0, v_a_1710_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
lean_inc_ref(v___y_1707_);
v___x_1718_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(v___x_1681_, v___x_1643_, v___y_1707_, v_options_1678_, v___x_1683_, v___y_1709_, v___f_1624_, v___x_1717_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
v___y_1660_ = v___x_1718_;
goto v___jp_1659_;
}
v___jp_1719_:
{
lean_object* v___x_1724_; 
v___x_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1724_, 0, v_a_1723_);
v___y_1707_ = v___y_1721_;
v___y_1708_ = v___y_1720_;
v___y_1709_ = v___y_1722_;
v_a_1710_ = v___x_1724_;
goto v___jp_1706_;
}
}
v___jp_1659_:
{
if (lean_obj_tag(v___y_1660_) == 0)
{
lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
v_isSharedCheck_1667_ = !lean_is_exclusive(v___y_1660_);
if (v_isSharedCheck_1667_ == 0)
{
lean_object* v_unused_1668_; 
v_unused_1668_ = lean_ctor_get(v___y_1660_, 0);
lean_dec(v_unused_1668_);
v___x_1662_ = v___y_1660_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_dec(v___y_1660_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v_a_1658_);
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1658_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_dec(v_a_1658_);
v_a_1669_ = lean_ctor_get(v___y_1660_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___y_1660_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___y_1660_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___y_1660_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
}
else
{
lean_dec(v___x_1648_);
lean_dec_ref(v___f_1624_);
return v___x_1657_;
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec_ref(v___f_1624_);
lean_dec_ref(v___f_1623_);
v_a_1803_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1637_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1637_);
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
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1622_ = stack[0].m_obj;
lean_object* v___f_1623_ = stack[1].m_obj;
lean_object* v___f_1624_ = stack[2].m_obj;
lean_object* v___y_1625_ = stack[3].m_obj;
lean_object* v___y_1626_ = stack[4].m_obj;
lean_object* v___y_1627_ = stack[5].m_obj;
lean_object* v___y_1628_ = stack[6].m_obj;
lean_object* v___y_1629_ = stack[7].m_obj;
lean_object* v___y_1630_ = stack[8].m_obj;
lean_object* v___y_1631_ = stack[9].m_obj;
lean_object* v___y_1632_ = stack[10].m_obj;
lean_object* v___y_1633_ = stack[11].m_obj;
lean_object* v___y_1634_ = stack[12].m_obj;
lean_object* v___y_1635_ = stack[13].m_obj;
lean_object* v_res_1811_;
v_res_1811_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5(v___x_1622_, v___f_1623_, v___f_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
stack->m_obj
 = v_res_1811_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___boxed(lean_object* v___x_1812_, lean_object* v___f_1813_, lean_object* v___f_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5(v___x_1812_, v___f_1813_, v___f_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec_ref(v___y_1824_);
lean_dec(v___y_1823_);
lean_dec_ref(v___y_1822_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec_ref(v___x_1812_);
return v_res_1827_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4(void){
_start:
{
lean_object* v___f_1833_; lean_object* v___f_1834_; lean_object* v___x_1835_; lean_object* v___f_1836_; 
v___f_1833_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__0));
v___f_1834_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__1));
v___x_1835_ = l_Lean_Meta_Tactic_BVDecide_bvNormalizeExt;
v___f_1836_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___boxed), 15, 3);
lean_closure_set(v___f_1836_, 0, v___x_1835_);
lean_closure_set(v___f_1836_, 1, v___f_1834_);
lean_closure_set(v___f_1836_, 2, v___f_1833_);
return v___f_1836_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__5(void){
_start:
{
lean_object* v___f_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___f_1837_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4);
v___x_1838_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__3));
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
lean_ctor_set(v___x_1839_, 1, v___f_1837_);
return v___x_1839_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass(void){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__5);
return v___x_1840_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0(lean_object* v_cls_1841_, lean_object* v_msg_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v_cls_1841_, v_msg_1842_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
return v___x_1855_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1841_ = stack[0].m_obj;
lean_object* v_msg_1842_ = stack[1].m_obj;
lean_object* v___y_1843_ = stack[2].m_obj;
lean_object* v___y_1844_ = stack[3].m_obj;
lean_object* v___y_1845_ = stack[4].m_obj;
lean_object* v___y_1846_ = stack[5].m_obj;
lean_object* v___y_1847_ = stack[6].m_obj;
lean_object* v___y_1848_ = stack[7].m_obj;
lean_object* v___y_1849_ = stack[8].m_obj;
lean_object* v___y_1850_ = stack[9].m_obj;
lean_object* v___y_1851_ = stack[10].m_obj;
lean_object* v___y_1852_ = stack[11].m_obj;
lean_object* v___y_1853_ = stack[12].m_obj;
lean_object* v_res_1856_;
v_res_1856_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0(v_cls_1841_, v_msg_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_, v___y_1853_);
stack->m_obj
 = v_res_1856_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___boxed(lean_object* v_cls_1857_, lean_object* v_msg_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0(v_cls_1857_, v_msg_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
return v_res_1871_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1(lean_object* v_upperBound_1872_, lean_object* v___x_1873_, lean_object* v___x_1874_, lean_object* v___x_1875_, lean_object* v___x_1876_, lean_object* v_inst_1877_, lean_object* v_R_1878_, lean_object* v_a_1879_, lean_object* v_b_1880_, lean_object* v_c_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v_upperBound_1872_, v___x_1873_, v___x_1874_, v___x_1875_, v___x_1876_, v_a_1879_, v_b_1880_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
return v___x_1894_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1872_ = stack[0].m_obj;
lean_object* v___x_1873_ = stack[1].m_obj;
lean_object* v___x_1874_ = stack[2].m_obj;
lean_object* v___x_1875_ = stack[3].m_obj;
lean_object* v___x_1876_ = stack[4].m_obj;
lean_object* v_a_1879_ = stack[7].m_obj;
lean_object* v_b_1880_ = stack[8].m_obj;
lean_object* v___y_1882_ = stack[10].m_obj;
lean_object* v___y_1883_ = stack[11].m_obj;
lean_object* v___y_1884_ = stack[12].m_obj;
lean_object* v___y_1885_ = stack[13].m_obj;
lean_object* v___y_1886_ = stack[14].m_obj;
lean_object* v___y_1887_ = stack[15].m_obj;
lean_object* v___y_1888_ = stack[16].m_obj;
lean_object* v___y_1889_ = stack[17].m_obj;
lean_object* v___y_1890_ = stack[18].m_obj;
lean_object* v___y_1891_ = stack[19].m_obj;
lean_object* v___y_1892_ = stack[20].m_obj;
lean_object* v_res_1895_;
v_res_1895_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1(v_upperBound_1872_, v___x_1873_, v___x_1874_, v___x_1875_, v___x_1876_, lean_box(0), lean_box(0), v_a_1879_, v_b_1880_, lean_box(0), v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
stack->m_obj
 = v_res_1895_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_1896_ = _args[0];
lean_object* v___x_1897_ = _args[1];
lean_object* v___x_1898_ = _args[2];
lean_object* v___x_1899_ = _args[3];
lean_object* v___x_1900_ = _args[4];
lean_object* v_inst_1901_ = _args[5];
lean_object* v_R_1902_ = _args[6];
lean_object* v_a_1903_ = _args[7];
lean_object* v_b_1904_ = _args[8];
lean_object* v_c_1905_ = _args[9];
lean_object* v___y_1906_ = _args[10];
lean_object* v___y_1907_ = _args[11];
lean_object* v___y_1908_ = _args[12];
lean_object* v___y_1909_ = _args[13];
lean_object* v___y_1910_ = _args[14];
lean_object* v___y_1911_ = _args[15];
lean_object* v___y_1912_ = _args[16];
lean_object* v___y_1913_ = _args[17];
lean_object* v___y_1914_ = _args[18];
lean_object* v___y_1915_ = _args[19];
lean_object* v___y_1916_ = _args[20];
lean_object* v___y_1917_ = _args[21];
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1(v_upperBound_1896_, v___x_1897_, v___x_1898_, v___x_1899_, v___x_1900_, v_inst_1901_, v_R_1902_, v_a_1903_, v_b_1904_, v_c_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
lean_dec(v___y_1914_);
lean_dec_ref(v___y_1913_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec(v___y_1907_);
lean_dec_ref(v___y_1906_);
lean_dec_ref(v___x_1897_);
lean_dec(v_upperBound_1896_);
return v_res_1918_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8(lean_object* v_00_u03b1_1919_, lean_object* v_x_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8___redArg(v_x_1920_);
return v___x_1933_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1920_ = stack[1].m_obj;
lean_object* v___y_1921_ = stack[2].m_obj;
lean_object* v___y_1922_ = stack[3].m_obj;
lean_object* v___y_1923_ = stack[4].m_obj;
lean_object* v___y_1924_ = stack[5].m_obj;
lean_object* v___y_1925_ = stack[6].m_obj;
lean_object* v___y_1926_ = stack[7].m_obj;
lean_object* v___y_1927_ = stack[8].m_obj;
lean_object* v___y_1928_ = stack[9].m_obj;
lean_object* v___y_1929_ = stack[10].m_obj;
lean_object* v___y_1930_ = stack[11].m_obj;
lean_object* v___y_1931_ = stack[12].m_obj;
lean_object* v_res_1934_;
v_res_1934_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8(lean_box(0), v_x_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
stack->m_obj
 = v_res_1934_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1935_, lean_object* v_x_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__8(v_00_u03b1_1935_, v_x_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7(lean_object* v_n_1950_, lean_object* v_as_1951_, lean_object* v_lo_1952_, lean_object* v_hi_1953_, lean_object* v_w_1954_, lean_object* v_hlo_1955_, lean_object* v_hhi_1956_){
_start:
{
lean_object* v___x_1957_; 
v___x_1957_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___redArg(v_n_1950_, v_as_1951_, v_lo_1952_, v_hi_1953_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___boxed(lean_object* v_n_1958_, lean_object* v_as_1959_, lean_object* v_lo_1960_, lean_object* v_hi_1961_, lean_object* v_w_1962_, lean_object* v_hlo_1963_, lean_object* v_hhi_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7(v_n_1958_, v_as_1959_, v_lo_1960_, v_hi_1961_, v_w_1962_, v_hlo_1963_, v_hhi_1964_);
lean_dec(v_hi_1961_);
lean_dec(v_n_1958_);
return v_res_1965_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7(lean_object* v_oldTraces_1966_, lean_object* v_data_1967_, lean_object* v_ref_1968_, lean_object* v_msg_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v___x_1982_; 
v___x_1982_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7___redArg(v_oldTraces_1966_, v_data_1967_, v_ref_1968_, v_msg_1969_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
return v___x_1982_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_1966_ = stack[0].m_obj;
lean_object* v_data_1967_ = stack[1].m_obj;
lean_object* v_ref_1968_ = stack[2].m_obj;
lean_object* v_msg_1969_ = stack[3].m_obj;
lean_object* v___y_1970_ = stack[4].m_obj;
lean_object* v___y_1971_ = stack[5].m_obj;
lean_object* v___y_1972_ = stack[6].m_obj;
lean_object* v___y_1973_ = stack[7].m_obj;
lean_object* v___y_1974_ = stack[8].m_obj;
lean_object* v___y_1975_ = stack[9].m_obj;
lean_object* v___y_1976_ = stack[10].m_obj;
lean_object* v___y_1977_ = stack[11].m_obj;
lean_object* v___y_1978_ = stack[12].m_obj;
lean_object* v___y_1979_ = stack[13].m_obj;
lean_object* v___y_1980_ = stack[14].m_obj;
lean_object* v_res_1983_;
v_res_1983_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7(v_oldTraces_1966_, v_data_1967_, v_ref_1968_, v_msg_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
stack->m_obj
 = v_res_1983_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7___boxed(lean_object* v_oldTraces_1984_, lean_object* v_data_1985_, lean_object* v_ref_1986_, lean_object* v_msg_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6_spec__7(v_oldTraces_1984_, v_data_1985_, v_ref_1986_, v_msg_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12(lean_object* v_n_2001_, lean_object* v_lo_2002_, lean_object* v_hi_2003_, lean_object* v_hhi_2004_, lean_object* v_pivot_2005_, lean_object* v_as_2006_, lean_object* v_i_2007_, lean_object* v_k_2008_, lean_object* v_ilo_2009_, lean_object* v_ik_2010_, lean_object* v_w_2011_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12___redArg(v_hi_2003_, v_pivot_2005_, v_as_2006_, v_i_2007_, v_k_2008_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12___boxed(lean_object* v_n_2013_, lean_object* v_lo_2014_, lean_object* v_hi_2015_, lean_object* v_hhi_2016_, lean_object* v_pivot_2017_, lean_object* v_as_2018_, lean_object* v_i_2019_, lean_object* v_k_2020_, lean_object* v_ilo_2021_, lean_object* v_ik_2022_, lean_object* v_w_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12(v_n_2013_, v_lo_2014_, v_hi_2015_, v_hhi_2016_, v_pivot_2017_, v_as_2018_, v_i_2019_, v_k_2020_, v_ilo_2021_, v_ik_2022_, v_w_2023_);
lean_dec_ref(v_pivot_2017_);
lean_dec(v_hi_2015_);
lean_dec(v_lo_2014_);
lean_dec(v_n_2013_);
return v_res_2024_;
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

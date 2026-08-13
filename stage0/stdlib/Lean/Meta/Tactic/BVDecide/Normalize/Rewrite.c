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
lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* l_Lean_Meta_Sym_Simp_evalGround___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteDsimproc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_evalGround___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_dsimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_evalGround___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpControl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_bvNormalizeExt;
lean_object* l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__3___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__16_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__16___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__17___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__0_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__1___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__0_value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__1_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__2___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__1_value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__2_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__3___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__3_value;
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__4___boxed, .m_arity = 13, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__2_value)} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__4_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__3_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__7_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__8_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__9_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__9_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__9_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__10_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__11_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "  ==>  "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__13_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__14;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9_spec__11(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__11(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__11___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___boxed(lean_object**);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__2;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_evalGround___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__3_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__3_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__5;
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__17(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__16_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg(lean_object* v_methods_4_, lean_object* v_config_5_, lean_object* v_hyp_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
lean_object* v___x_15_; lean_object* v_rewriteSimpCache_16_; lean_object* v_rewriteDSimpCache_17_; lean_object* v_acCache_18_; lean_object* v_typeAnalysis_19_; lean_object* v_target_20_; lean_object* v_hypotheses_21_; uint8_t v_didChange_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_65_; 
v___x_15_ = lean_st_ref_take(v_a_7_);
v_rewriteSimpCache_16_ = lean_ctor_get(v___x_15_, 0);
v_rewriteDSimpCache_17_ = lean_ctor_get(v___x_15_, 1);
v_acCache_18_ = lean_ctor_get(v___x_15_, 2);
v_typeAnalysis_19_ = lean_ctor_get(v___x_15_, 3);
v_target_20_ = lean_ctor_get(v___x_15_, 4);
v_hypotheses_21_ = lean_ctor_get(v___x_15_, 5);
v_didChange_22_ = lean_ctor_get_uint8(v___x_15_, sizeof(void*)*6);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_65_ == 0)
{
v___x_24_ = v___x_15_;
v_isShared_25_ = v_isSharedCheck_65_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_hypotheses_21_);
lean_inc(v_target_20_);
lean_inc(v_typeAnalysis_19_);
lean_inc(v_acCache_18_);
lean_inc(v_rewriteDSimpCache_17_);
lean_inc(v_rewriteSimpCache_16_);
lean_dec(v___x_15_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_65_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_26_; lean_object* v___x_28_; 
v___x_26_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg___closed__1);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 1, v___x_26_);
v___x_28_ = v___x_24_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_rewriteSimpCache_16_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v___x_26_);
lean_ctor_set(v_reuseFailAlloc_64_, 2, v_acCache_18_);
lean_ctor_set(v_reuseFailAlloc_64_, 3, v_typeAnalysis_19_);
lean_ctor_set(v_reuseFailAlloc_64_, 4, v_target_20_);
lean_ctor_set(v_reuseFailAlloc_64_, 5, v_hypotheses_21_);
lean_ctor_set_uint8(v_reuseFailAlloc_64_, sizeof(void*)*6, v_didChange_22_);
v___x_28_ = v_reuseFailAlloc_64_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
lean_object* v___x_29_; lean_object* v_type_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_29_ = lean_st_ref_set(v_a_7_, v___x_28_);
v_type_30_ = lean_ctor_get(v_hyp_6_, 1);
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v_rewriteDSimpCache_17_);
lean_inc_ref(v_type_30_);
v___x_33_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_DSimp_dsimp___boxed), 11, 1);
lean_closure_set(v___x_33_, 0, v_type_30_);
v___x_34_ = l_Lean_Meta_Sym_DSimp_DSimpM_run___redArg(v___x_33_, v_methods_4_, v_config_5_, v___x_32_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_);
if (lean_obj_tag(v___x_34_) == 0)
{
lean_object* v_a_35_; lean_object* v_fst_36_; lean_object* v_snd_37_; lean_object* v___x_38_; lean_object* v_cache_39_; lean_object* v_rewriteSimpCache_40_; lean_object* v_acCache_41_; lean_object* v_typeAnalysis_42_; lean_object* v_target_43_; lean_object* v_hypotheses_44_; uint8_t v_didChange_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_54_; 
v_a_35_ = lean_ctor_get(v___x_34_, 0);
lean_inc(v_a_35_);
lean_dec_ref_known(v___x_34_, 1);
v_fst_36_ = lean_ctor_get(v_a_35_, 0);
lean_inc(v_fst_36_);
v_snd_37_ = lean_ctor_get(v_a_35_, 1);
lean_inc(v_snd_37_);
lean_dec(v_a_35_);
v___x_38_ = lean_st_ref_take(v_a_7_);
v_cache_39_ = lean_ctor_get(v_snd_37_, 1);
lean_inc_ref(v_cache_39_);
lean_dec(v_snd_37_);
v_rewriteSimpCache_40_ = lean_ctor_get(v___x_38_, 0);
v_acCache_41_ = lean_ctor_get(v___x_38_, 2);
v_typeAnalysis_42_ = lean_ctor_get(v___x_38_, 3);
v_target_43_ = lean_ctor_get(v___x_38_, 4);
v_hypotheses_44_ = lean_ctor_get(v___x_38_, 5);
v_didChange_45_ = lean_ctor_get_uint8(v___x_38_, sizeof(void*)*6);
v_isSharedCheck_54_ = !lean_is_exclusive(v___x_38_);
if (v_isSharedCheck_54_ == 0)
{
lean_object* v_unused_55_; 
v_unused_55_ = lean_ctor_get(v___x_38_, 1);
lean_dec(v_unused_55_);
v___x_47_ = v___x_38_;
v_isShared_48_ = v_isSharedCheck_54_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_hypotheses_44_);
lean_inc(v_target_43_);
lean_inc(v_typeAnalysis_42_);
lean_inc(v_acCache_41_);
lean_inc(v_rewriteSimpCache_40_);
lean_dec(v___x_38_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_54_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 1, v_cache_39_);
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v_rewriteSimpCache_40_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v_cache_39_);
lean_ctor_set(v_reuseFailAlloc_53_, 2, v_acCache_41_);
lean_ctor_set(v_reuseFailAlloc_53_, 3, v_typeAnalysis_42_);
lean_ctor_set(v_reuseFailAlloc_53_, 4, v_target_43_);
lean_ctor_set(v_reuseFailAlloc_53_, 5, v_hypotheses_44_);
lean_ctor_set_uint8(v_reuseFailAlloc_53_, sizeof(void*)*6, v_didChange_45_);
v___x_50_ = v_reuseFailAlloc_53_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_st_ref_set(v_a_7_, v___x_50_);
v___x_52_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applyDSimpResult___redArg(v_hyp_6_, v_fst_36_);
lean_dec(v_fst_36_);
return v___x_52_;
}
}
}
else
{
lean_object* v_a_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_63_; 
lean_dec_ref(v_hyp_6_);
v_a_56_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_63_ == 0)
{
v___x_58_ = v___x_34_;
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_a_56_);
lean_dec(v___x_34_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
if (v_isShared_59_ == 0)
{
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_a_56_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg___boxed(lean_object* v_methods_66_, lean_object* v_config_67_, lean_object* v_hyp_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg(v_methods_66_, v_config_67_, v_hyp_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
lean_dec(v_a_69_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp(lean_object* v_methods_78_, lean_object* v_config_79_, lean_object* v_hyp_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg(v_methods_78_, v_config_79_, v_hyp_80_, v_a_82_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___boxed(lean_object* v_methods_94_, lean_object* v_config_95_, lean_object* v_hyp_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp(v_methods_94_, v_config_95_, v_hyp_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
lean_dec(v_a_99_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
return v_res_109_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__0(void){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_110_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__1(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__0);
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg(lean_object* v_methods_113_, lean_object* v_config_114_, lean_object* v_hyp_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v___x_124_; lean_object* v_rewriteSimpCache_125_; lean_object* v_rewriteDSimpCache_126_; lean_object* v_acCache_127_; lean_object* v_typeAnalysis_128_; lean_object* v_target_129_; lean_object* v_hypotheses_130_; uint8_t v_didChange_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_174_; 
v___x_124_ = lean_st_ref_take(v_a_116_);
v_rewriteSimpCache_125_ = lean_ctor_get(v___x_124_, 0);
v_rewriteDSimpCache_126_ = lean_ctor_get(v___x_124_, 1);
v_acCache_127_ = lean_ctor_get(v___x_124_, 2);
v_typeAnalysis_128_ = lean_ctor_get(v___x_124_, 3);
v_target_129_ = lean_ctor_get(v___x_124_, 4);
v_hypotheses_130_ = lean_ctor_get(v___x_124_, 5);
v_didChange_131_ = lean_ctor_get_uint8(v___x_124_, sizeof(void*)*6);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_174_ == 0)
{
v___x_133_ = v___x_124_;
v_isShared_134_ = v_isSharedCheck_174_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_hypotheses_130_);
lean_inc(v_target_129_);
lean_inc(v_typeAnalysis_128_);
lean_inc(v_acCache_127_);
lean_inc(v_rewriteDSimpCache_126_);
lean_inc(v_rewriteSimpCache_125_);
lean_dec(v___x_124_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_174_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_135_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__1);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 0, v___x_135_);
v___x_137_ = v___x_133_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_rewriteDSimpCache_126_);
lean_ctor_set(v_reuseFailAlloc_173_, 2, v_acCache_127_);
lean_ctor_set(v_reuseFailAlloc_173_, 3, v_typeAnalysis_128_);
lean_ctor_set(v_reuseFailAlloc_173_, 4, v_target_129_);
lean_ctor_set(v_reuseFailAlloc_173_, 5, v_hypotheses_130_);
lean_ctor_set_uint8(v_reuseFailAlloc_173_, sizeof(void*)*6, v_didChange_131_);
v___x_137_ = v_reuseFailAlloc_173_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_138_; lean_object* v_type_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_138_ = lean_st_ref_set(v_a_116_, v___x_137_);
v_type_139_ = lean_ctor_get(v_hyp_115_, 1);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v_rewriteSimpCache_125_);
lean_ctor_set(v___x_141_, 2, v___x_135_);
lean_ctor_set(v___x_141_, 3, v___x_135_);
lean_inc_ref(v_type_139_);
v___x_142_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_142_, 0, v_type_139_);
v___x_143_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_142_, v_methods_113_, v_config_114_, v___x_141_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v_a_144_; lean_object* v_fst_145_; lean_object* v_snd_146_; lean_object* v___x_147_; lean_object* v_persistentCache_148_; lean_object* v_rewriteDSimpCache_149_; lean_object* v_acCache_150_; lean_object* v_typeAnalysis_151_; lean_object* v_target_152_; lean_object* v_hypotheses_153_; uint8_t v_didChange_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_163_; 
v_a_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc(v_a_144_);
lean_dec_ref_known(v___x_143_, 1);
v_fst_145_ = lean_ctor_get(v_a_144_, 0);
lean_inc(v_fst_145_);
v_snd_146_ = lean_ctor_get(v_a_144_, 1);
lean_inc(v_snd_146_);
lean_dec(v_a_144_);
v___x_147_ = lean_st_ref_take(v_a_116_);
v_persistentCache_148_ = lean_ctor_get(v_snd_146_, 1);
lean_inc_ref(v_persistentCache_148_);
lean_dec(v_snd_146_);
v_rewriteDSimpCache_149_ = lean_ctor_get(v___x_147_, 1);
v_acCache_150_ = lean_ctor_get(v___x_147_, 2);
v_typeAnalysis_151_ = lean_ctor_get(v___x_147_, 3);
v_target_152_ = lean_ctor_get(v___x_147_, 4);
v_hypotheses_153_ = lean_ctor_get(v___x_147_, 5);
v_didChange_154_ = lean_ctor_get_uint8(v___x_147_, sizeof(void*)*6);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_163_ == 0)
{
lean_object* v_unused_164_; 
v_unused_164_ = lean_ctor_get(v___x_147_, 0);
lean_dec(v_unused_164_);
v___x_156_ = v___x_147_;
v_isShared_157_ = v_isSharedCheck_163_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_hypotheses_153_);
lean_inc(v_target_152_);
lean_inc(v_typeAnalysis_151_);
lean_inc(v_acCache_150_);
lean_inc(v_rewriteDSimpCache_149_);
lean_dec(v___x_147_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_163_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v_persistentCache_148_);
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_persistentCache_148_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_rewriteDSimpCache_149_);
lean_ctor_set(v_reuseFailAlloc_162_, 2, v_acCache_150_);
lean_ctor_set(v_reuseFailAlloc_162_, 3, v_typeAnalysis_151_);
lean_ctor_set(v_reuseFailAlloc_162_, 4, v_target_152_);
lean_ctor_set(v_reuseFailAlloc_162_, 5, v_hypotheses_153_);
lean_ctor_set_uint8(v_reuseFailAlloc_162_, sizeof(void*)*6, v_didChange_154_);
v___x_159_ = v_reuseFailAlloc_162_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_st_ref_set(v_a_116_, v___x_159_);
v___x_161_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_115_, v_fst_145_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
return v___x_161_;
}
}
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
lean_dec_ref(v_hyp_115_);
v_a_165_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_143_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_143_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___boxed(lean_object* v_methods_175_, lean_object* v_config_176_, lean_object* v_hyp_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg(v_methods_175_, v_config_176_, v_hyp_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp(lean_object* v_methods_187_, lean_object* v_config_188_, lean_object* v_hyp_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg(v_methods_187_, v_config_188_, v_hyp_189_, v_a_191_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___boxed(lean_object* v_methods_203_, lean_object* v_config_204_, lean_object* v_hyp_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp(v_methods_203_, v_config_204_, v_hyp_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
lean_dec(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg___lam__0(lean_object* v_x_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v___x_232_; 
lean_inc(v___y_226_);
lean_inc_ref(v___y_225_);
lean_inc(v___y_224_);
lean_inc_ref(v___y_223_);
lean_inc(v___y_222_);
lean_inc(v___y_221_);
lean_inc_ref(v___y_220_);
v___x_232_ = lean_apply_12(v_x_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, lean_box(0));
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg___lam__0___boxed(lean_object* v_x_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg___lam__0(v_x_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg(lean_object* v_mvarId_247_, lean_object* v_x_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v___f_261_; lean_object* v___x_262_; 
lean_inc(v___y_255_);
lean_inc_ref(v___y_254_);
lean_inc(v___y_253_);
lean_inc_ref(v___y_252_);
lean_inc(v___y_251_);
lean_inc(v___y_250_);
lean_inc_ref(v___y_249_);
v___f_261_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_261_, 0, v_x_248_);
lean_closure_set(v___f_261_, 1, v___y_249_);
lean_closure_set(v___f_261_, 2, v___y_250_);
lean_closure_set(v___f_261_, 3, v___y_251_);
lean_closure_set(v___f_261_, 4, v___y_252_);
lean_closure_set(v___f_261_, 5, v___y_253_);
lean_closure_set(v___f_261_, 6, v___y_254_);
lean_closure_set(v___f_261_, 7, v___y_255_);
v___x_262_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_247_, v___f_261_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
if (lean_obj_tag(v___x_262_) == 0)
{
return v___x_262_;
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_262_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_262_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg___boxed(lean_object* v_mvarId_271_, lean_object* v_x_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg(v_mvarId_271_, v_x_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3(lean_object* v_00_u03b1_286_, lean_object* v_mvarId_287_, lean_object* v_x_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg(v_mvarId_287_, v_x_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___boxed(lean_object* v_00_u03b1_302_, lean_object* v_mvarId_303_, lean_object* v_x_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3(v_00_u03b1_302_, v_mvarId_303_, v_x_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
return v_res_317_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_318_ = lean_unsigned_to_nat(32u);
v___x_319_ = lean_mk_empty_array_with_capacity(v___x_318_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_321_ = ((size_t)5ULL);
v___x_322_ = lean_unsigned_to_nat(0u);
v___x_323_ = lean_unsigned_to_nat(32u);
v___x_324_ = lean_mk_empty_array_with_capacity(v___x_323_);
v___x_325_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__0);
v___x_326_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_324_);
lean_ctor_set(v___x_326_, 2, v___x_322_);
lean_ctor_set(v___x_326_, 3, v___x_322_);
lean_ctor_set_usize(v___x_326_, 4, v___x_321_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg(lean_object* v___y_327_){
_start:
{
lean_object* v___x_329_; lean_object* v_traceState_330_; lean_object* v_traces_331_; lean_object* v___x_332_; lean_object* v_traceState_333_; lean_object* v_env_334_; lean_object* v_nextMacroScope_335_; lean_object* v_ngen_336_; lean_object* v_auxDeclNGen_337_; lean_object* v_cache_338_; lean_object* v_messages_339_; lean_object* v_infoState_340_; lean_object* v_snapshotTasks_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_360_; 
v___x_329_ = lean_st_ref_get(v___y_327_);
v_traceState_330_ = lean_ctor_get(v___x_329_, 4);
lean_inc_ref(v_traceState_330_);
lean_dec(v___x_329_);
v_traces_331_ = lean_ctor_get(v_traceState_330_, 0);
lean_inc_ref(v_traces_331_);
lean_dec_ref(v_traceState_330_);
v___x_332_ = lean_st_ref_take(v___y_327_);
v_traceState_333_ = lean_ctor_get(v___x_332_, 4);
v_env_334_ = lean_ctor_get(v___x_332_, 0);
v_nextMacroScope_335_ = lean_ctor_get(v___x_332_, 1);
v_ngen_336_ = lean_ctor_get(v___x_332_, 2);
v_auxDeclNGen_337_ = lean_ctor_get(v___x_332_, 3);
v_cache_338_ = lean_ctor_get(v___x_332_, 5);
v_messages_339_ = lean_ctor_get(v___x_332_, 6);
v_infoState_340_ = lean_ctor_get(v___x_332_, 7);
v_snapshotTasks_341_ = lean_ctor_get(v___x_332_, 8);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_332_);
if (v_isSharedCheck_360_ == 0)
{
v___x_343_ = v___x_332_;
v_isShared_344_ = v_isSharedCheck_360_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_snapshotTasks_341_);
lean_inc(v_infoState_340_);
lean_inc(v_messages_339_);
lean_inc(v_cache_338_);
lean_inc(v_traceState_333_);
lean_inc(v_auxDeclNGen_337_);
lean_inc(v_ngen_336_);
lean_inc(v_nextMacroScope_335_);
lean_inc(v_env_334_);
lean_dec(v___x_332_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_360_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
uint64_t v_tid_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_358_; 
v_tid_345_ = lean_ctor_get_uint64(v_traceState_333_, sizeof(void*)*1);
v_isSharedCheck_358_ = !lean_is_exclusive(v_traceState_333_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; 
v_unused_359_ = lean_ctor_get(v_traceState_333_, 0);
lean_dec(v_unused_359_);
v___x_347_ = v_traceState_333_;
v_isShared_348_ = v_isSharedCheck_358_;
goto v_resetjp_346_;
}
else
{
lean_dec(v_traceState_333_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_358_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; lean_object* v___x_351_; 
v___x_349_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__1);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_349_);
v___x_351_ = v___x_347_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_349_);
lean_ctor_set_uint64(v_reuseFailAlloc_357_, sizeof(void*)*1, v_tid_345_);
v___x_351_ = v_reuseFailAlloc_357_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_353_; 
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 4, v___x_351_);
v___x_353_ = v___x_343_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_env_334_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_nextMacroScope_335_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_ngen_336_);
lean_ctor_set(v_reuseFailAlloc_356_, 3, v_auxDeclNGen_337_);
lean_ctor_set(v_reuseFailAlloc_356_, 4, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_356_, 5, v_cache_338_);
lean_ctor_set(v_reuseFailAlloc_356_, 6, v_messages_339_);
lean_ctor_set(v_reuseFailAlloc_356_, 7, v_infoState_340_);
lean_ctor_set(v_reuseFailAlloc_356_, 8, v_snapshotTasks_341_);
v___x_353_ = v_reuseFailAlloc_356_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_st_ref_set(v___y_327_, v___x_353_);
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v_traces_331_);
return v___x_355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___boxed(lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg(v___y_361_);
lean_dec(v___y_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5(lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg(v___y_374_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___boxed(lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5(v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
return v_res_389_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(lean_object* v_opts_390_, lean_object* v_opt_391_){
_start:
{
lean_object* v_name_392_; lean_object* v_defValue_393_; lean_object* v_map_394_; lean_object* v___x_395_; 
v_name_392_ = lean_ctor_get(v_opt_391_, 0);
v_defValue_393_ = lean_ctor_get(v_opt_391_, 1);
v_map_394_ = lean_ctor_get(v_opts_390_, 0);
v___x_395_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_394_, v_name_392_);
if (lean_obj_tag(v___x_395_) == 0)
{
uint8_t v___x_396_; 
v___x_396_ = lean_unbox(v_defValue_393_);
return v___x_396_;
}
else
{
lean_object* v_val_397_; 
v_val_397_ = lean_ctor_get(v___x_395_, 0);
lean_inc(v_val_397_);
lean_dec_ref_known(v___x_395_, 1);
if (lean_obj_tag(v_val_397_) == 1)
{
uint8_t v_v_398_; 
v_v_398_ = lean_ctor_get_uint8(v_val_397_, 0);
lean_dec_ref_known(v_val_397_, 0);
return v_v_398_;
}
else
{
uint8_t v___x_399_; 
lean_dec(v_val_397_);
v___x_399_ = lean_unbox(v_defValue_393_);
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___boxed(lean_object* v_opts_400_, lean_object* v_opt_401_){
_start:
{
uint8_t v_res_402_; lean_object* v_r_403_; 
v_res_402_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(v_opts_400_, v_opt_401_);
lean_dec_ref(v_opt_401_);
lean_dec_ref(v_opts_400_);
v_r_403_ = lean_box(v_res_402_);
return v_r_403_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__2(void){
_start:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__1));
v___x_408_ = l_Lean_MessageData_ofFormat(v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(lean_object* v_x_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__2);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___boxed(lean_object* v_x_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(v_x_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec_ref(v_x_424_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1(lean_object* v_e_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_Meta_Sym_Simp_simpControl(v_e_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_480_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_480_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_480_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_480_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
if (lean_obj_tag(v_a_450_) == 0)
{
uint8_t v_contextDependent_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_465_; 
v_contextDependent_454_ = lean_ctor_get_uint8(v_a_450_, 1);
v_isSharedCheck_465_ = !lean_is_exclusive(v_a_450_);
if (v_isSharedCheck_465_ == 0)
{
v___x_456_ = v_a_450_;
v_isShared_457_ = v_isSharedCheck_465_;
goto v_resetjp_455_;
}
else
{
lean_dec(v_a_450_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_465_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
uint8_t v___x_458_; lean_object* v___x_460_; 
v___x_458_ = 0;
if (v_isShared_457_ == 0)
{
v___x_460_ = v___x_456_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_464_, 1, v_contextDependent_454_);
v___x_460_ = v_reuseFailAlloc_464_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_462_; 
lean_ctor_set_uint8(v___x_460_, 0, v___x_458_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_460_);
v___x_462_ = v___x_452_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
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
else
{
lean_object* v_e_x27_466_; lean_object* v_proof_467_; uint8_t v_contextDependent_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_479_; 
v_e_x27_466_ = lean_ctor_get(v_a_450_, 0);
v_proof_467_ = lean_ctor_get(v_a_450_, 1);
v_contextDependent_468_ = lean_ctor_get_uint8(v_a_450_, sizeof(void*)*2 + 1);
v_isSharedCheck_479_ = !lean_is_exclusive(v_a_450_);
if (v_isSharedCheck_479_ == 0)
{
v___x_470_ = v_a_450_;
v_isShared_471_ = v_isSharedCheck_479_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_proof_467_);
lean_inc(v_e_x27_466_);
lean_dec(v_a_450_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_479_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
uint8_t v___x_472_; lean_object* v___x_474_; 
v___x_472_ = 0;
if (v_isShared_471_ == 0)
{
v___x_474_ = v___x_470_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_e_x27_466_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_proof_467_);
lean_ctor_set_uint8(v_reuseFailAlloc_478_, sizeof(void*)*2 + 1, v_contextDependent_468_);
v___x_474_ = v_reuseFailAlloc_478_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_476_; 
lean_ctor_set_uint8(v___x_474_, sizeof(void*)*2, v___x_472_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_474_);
v___x_476_ = v___x_452_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
}
else
{
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___boxed(lean_object* v_e_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1(v_e_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2(lean_object* v_val_493_, lean_object* v_a_494_, lean_object* v___x_495_, lean_object* v_x_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v___x_508_; 
lean_inc_ref(v___y_497_);
v___x_508_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteSimproc(v_val_493_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
if (lean_obj_tag(v_a_509_) == 0)
{
uint8_t v_done_510_; 
v_done_510_ = lean_ctor_get_uint8(v_a_509_, 0);
if (v_done_510_ == 0)
{
uint8_t v_contextDependent_511_; lean_object* v___x_512_; 
lean_dec_ref_known(v___x_508_, 1);
v_contextDependent_511_ = lean_ctor_get_uint8(v_a_509_, 1);
lean_dec_ref_known(v_a_509_, 0);
v___x_512_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_494_, v___x_495_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; uint8_t v___y_515_; 
v_a_513_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_513_);
if (v_contextDependent_511_ == 0)
{
lean_dec(v_a_513_);
return v___x_512_;
}
else
{
if (lean_obj_tag(v_a_513_) == 0)
{
uint8_t v_contextDependent_525_; 
v_contextDependent_525_ = lean_ctor_get_uint8(v_a_513_, 1);
v___y_515_ = v_contextDependent_525_;
goto v___jp_514_;
}
else
{
uint8_t v_contextDependent_526_; 
v_contextDependent_526_ = lean_ctor_get_uint8(v_a_513_, sizeof(void*)*2 + 1);
v___y_515_ = v_contextDependent_526_;
goto v___jp_514_;
}
}
v___jp_514_:
{
if (v___y_515_ == 0)
{
lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_523_; 
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; 
v_unused_524_ = lean_ctor_get(v___x_512_, 0);
lean_dec(v_unused_524_);
v___x_517_ = v___x_512_;
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
else
{
lean_dec(v___x_512_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_523_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_513_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_519_);
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
else
{
lean_dec(v_a_513_);
return v___x_512_;
}
}
}
else
{
return v___x_512_;
}
}
else
{
lean_dec_ref_known(v_a_509_, 0);
lean_dec_ref(v___y_497_);
lean_dec_ref(v___x_495_);
return v___x_508_;
}
}
else
{
uint8_t v_done_527_; 
v_done_527_ = lean_ctor_get_uint8(v_a_509_, sizeof(void*)*2);
if (v_done_527_ == 0)
{
lean_object* v_e_x27_528_; lean_object* v_proof_529_; uint8_t v_contextDependent_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_580_; 
lean_dec_ref_known(v___x_508_, 1);
v_e_x27_528_ = lean_ctor_get(v_a_509_, 0);
v_proof_529_ = lean_ctor_get(v_a_509_, 1);
v_contextDependent_530_ = lean_ctor_get_uint8(v_a_509_, sizeof(void*)*2 + 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v_a_509_);
if (v_isSharedCheck_580_ == 0)
{
v___x_532_ = v_a_509_;
v_isShared_533_ = v_isSharedCheck_580_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_proof_529_);
lean_inc(v_e_x27_528_);
lean_dec(v_a_509_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_580_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; 
lean_inc_ref(v_e_x27_528_);
v___x_534_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_494_, v___x_495_, v_e_x27_528_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_579_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_579_ == 0)
{
v___x_537_ = v___x_534_;
v_isShared_538_ = v_isSharedCheck_579_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_579_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
if (lean_obj_tag(v_a_535_) == 0)
{
uint8_t v_done_539_; uint8_t v_contextDependent_540_; uint8_t v___y_542_; 
lean_dec_ref(v___y_497_);
v_done_539_ = lean_ctor_get_uint8(v_a_535_, 0);
v_contextDependent_540_ = lean_ctor_get_uint8(v_a_535_, 1);
lean_dec_ref_known(v_a_535_, 0);
if (v_contextDependent_530_ == 0)
{
v___y_542_ = v_contextDependent_540_;
goto v___jp_541_;
}
else
{
v___y_542_ = v_contextDependent_530_;
goto v___jp_541_;
}
v___jp_541_:
{
lean_object* v___x_544_; 
if (v_isShared_533_ == 0)
{
v___x_544_ = v___x_532_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_e_x27_528_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_proof_529_);
v___x_544_ = v_reuseFailAlloc_548_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_546_; 
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*2, v_done_539_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*2 + 1, v___y_542_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_544_);
v___x_546_ = v___x_537_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
else
{
lean_object* v_e_x27_549_; lean_object* v_proof_550_; uint8_t v_done_551_; uint8_t v_contextDependent_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_578_; 
lean_del_object(v___x_537_);
lean_del_object(v___x_532_);
v_e_x27_549_ = lean_ctor_get(v_a_535_, 0);
v_proof_550_ = lean_ctor_get(v_a_535_, 1);
v_done_551_ = lean_ctor_get_uint8(v_a_535_, sizeof(void*)*2);
v_contextDependent_552_ = lean_ctor_get_uint8(v_a_535_, sizeof(void*)*2 + 1);
v_isSharedCheck_578_ = !lean_is_exclusive(v_a_535_);
if (v_isSharedCheck_578_ == 0)
{
v___x_554_ = v_a_535_;
v_isShared_555_ = v_isSharedCheck_578_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_proof_550_);
lean_inc(v_e_x27_549_);
lean_dec(v_a_535_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_578_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; 
lean_inc_ref(v_e_x27_549_);
v___x_556_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_497_, v_e_x27_528_, v_proof_529_, v_e_x27_549_, v_proof_550_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_569_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_569_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_569_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_569_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
uint8_t v___y_562_; 
if (v_contextDependent_530_ == 0)
{
v___y_562_ = v_contextDependent_552_;
goto v___jp_561_;
}
else
{
v___y_562_ = v_contextDependent_530_;
goto v___jp_561_;
}
v___jp_561_:
{
lean_object* v___x_564_; 
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v_a_557_);
v___x_564_ = v___x_554_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_e_x27_549_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_a_557_);
lean_ctor_set_uint8(v_reuseFailAlloc_568_, sizeof(void*)*2, v_done_551_);
v___x_564_ = v_reuseFailAlloc_568_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_566_; 
lean_ctor_set_uint8(v___x_564_, sizeof(void*)*2 + 1, v___y_562_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_564_);
v___x_566_ = v___x_559_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_564_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_del_object(v___x_554_);
lean_dec_ref(v_e_x27_549_);
v_a_570_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_556_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_556_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_532_);
lean_dec_ref(v_proof_529_);
lean_dec_ref(v_e_x27_528_);
lean_dec_ref(v___y_497_);
return v___x_534_;
}
}
}
else
{
lean_dec_ref_known(v_a_509_, 2);
lean_dec_ref(v___y_497_);
lean_dec_ref(v___x_495_);
return v___x_508_;
}
}
}
else
{
lean_dec_ref(v___y_497_);
lean_dec_ref(v___x_495_);
return v___x_508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2___boxed(lean_object* v_val_581_, lean_object* v_a_582_, lean_object* v___x_583_, lean_object* v_x_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2(v_val_581_, v_a_582_, v___x_583_, v_x_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v_a_582_);
lean_dec(v_val_581_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3(lean_object* v___x_597_, lean_object* v___f_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v___x_610_; 
lean_inc_ref(v___y_599_);
v___x_610_ = l_Lean_Meta_Sym_Simp_evalGround___redArg(v___x_597_, v___y_599_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_612_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
v___x_612_ = lean_box(0);
if (lean_obj_tag(v_a_611_) == 0)
{
uint8_t v_done_613_; 
v_done_613_ = lean_ctor_get_uint8(v_a_611_, 0);
if (v_done_613_ == 0)
{
uint8_t v_contextDependent_614_; lean_object* v___x_615_; 
lean_dec_ref_known(v___x_610_, 1);
v_contextDependent_614_ = lean_ctor_get_uint8(v_a_611_, 1);
lean_dec_ref_known(v_a_611_, 0);
v___x_615_ = lean_apply_12(v___f_598_, v___x_612_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, lean_box(0));
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; uint8_t v___y_618_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
lean_inc(v_a_616_);
if (v_contextDependent_614_ == 0)
{
lean_dec(v_a_616_);
return v___x_615_;
}
else
{
if (lean_obj_tag(v_a_616_) == 0)
{
uint8_t v_contextDependent_628_; 
v_contextDependent_628_ = lean_ctor_get_uint8(v_a_616_, 1);
v___y_618_ = v_contextDependent_628_;
goto v___jp_617_;
}
else
{
uint8_t v_contextDependent_629_; 
v_contextDependent_629_ = lean_ctor_get_uint8(v_a_616_, sizeof(void*)*2 + 1);
v___y_618_ = v_contextDependent_629_;
goto v___jp_617_;
}
}
v___jp_617_:
{
if (v___y_618_ == 0)
{
lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_626_; 
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; 
v_unused_627_ = lean_ctor_get(v___x_615_, 0);
lean_dec(v_unused_627_);
v___x_620_ = v___x_615_;
v_isShared_621_ = v_isSharedCheck_626_;
goto v_resetjp_619_;
}
else
{
lean_dec(v___x_615_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_626_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_622_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_616_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_622_);
v___x_624_ = v___x_620_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
else
{
lean_dec(v_a_616_);
return v___x_615_;
}
}
}
else
{
return v___x_615_;
}
}
else
{
lean_dec_ref_known(v_a_611_, 0);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec_ref(v___f_598_);
return v___x_610_;
}
}
else
{
uint8_t v_done_630_; 
v_done_630_ = lean_ctor_get_uint8(v_a_611_, sizeof(void*)*2);
if (v_done_630_ == 0)
{
lean_object* v_e_x27_631_; lean_object* v_proof_632_; uint8_t v_contextDependent_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_683_; 
lean_dec_ref_known(v___x_610_, 1);
v_e_x27_631_ = lean_ctor_get(v_a_611_, 0);
v_proof_632_ = lean_ctor_get(v_a_611_, 1);
v_contextDependent_633_ = lean_ctor_get_uint8(v_a_611_, sizeof(void*)*2 + 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v_a_611_);
if (v_isSharedCheck_683_ == 0)
{
v___x_635_ = v_a_611_;
v_isShared_636_ = v_isSharedCheck_683_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_proof_632_);
lean_inc(v_e_x27_631_);
lean_dec(v_a_611_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_683_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; 
lean_inc(v___y_608_);
lean_inc_ref(v___y_607_);
lean_inc(v___y_606_);
lean_inc_ref(v___y_605_);
lean_inc(v___y_604_);
lean_inc_ref(v___y_603_);
lean_inc_ref(v_e_x27_631_);
v___x_637_ = lean_apply_12(v___f_598_, v___x_612_, v_e_x27_631_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, lean_box(0));
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_682_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_682_ == 0)
{
v___x_640_ = v___x_637_;
v_isShared_641_ = v_isSharedCheck_682_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_637_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_682_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
if (lean_obj_tag(v_a_638_) == 0)
{
uint8_t v_done_642_; uint8_t v_contextDependent_643_; uint8_t v___y_645_; 
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec_ref(v___y_599_);
v_done_642_ = lean_ctor_get_uint8(v_a_638_, 0);
v_contextDependent_643_ = lean_ctor_get_uint8(v_a_638_, 1);
lean_dec_ref_known(v_a_638_, 0);
if (v_contextDependent_633_ == 0)
{
v___y_645_ = v_contextDependent_643_;
goto v___jp_644_;
}
else
{
v___y_645_ = v_contextDependent_633_;
goto v___jp_644_;
}
v___jp_644_:
{
lean_object* v___x_647_; 
if (v_isShared_636_ == 0)
{
v___x_647_ = v___x_635_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_e_x27_631_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_proof_632_);
v___x_647_ = v_reuseFailAlloc_651_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_649_; 
lean_ctor_set_uint8(v___x_647_, sizeof(void*)*2, v_done_642_);
lean_ctor_set_uint8(v___x_647_, sizeof(void*)*2 + 1, v___y_645_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_647_);
v___x_649_ = v___x_640_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
else
{
lean_object* v_e_x27_652_; lean_object* v_proof_653_; uint8_t v_done_654_; uint8_t v_contextDependent_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_681_; 
lean_del_object(v___x_640_);
lean_del_object(v___x_635_);
v_e_x27_652_ = lean_ctor_get(v_a_638_, 0);
v_proof_653_ = lean_ctor_get(v_a_638_, 1);
v_done_654_ = lean_ctor_get_uint8(v_a_638_, sizeof(void*)*2);
v_contextDependent_655_ = lean_ctor_get_uint8(v_a_638_, sizeof(void*)*2 + 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v_a_638_);
if (v_isSharedCheck_681_ == 0)
{
v___x_657_ = v_a_638_;
v_isShared_658_ = v_isSharedCheck_681_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_proof_653_);
lean_inc(v_e_x27_652_);
lean_dec(v_a_638_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_681_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; 
lean_inc_ref(v_e_x27_652_);
v___x_659_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_599_, v_e_x27_631_, v_proof_632_, v_e_x27_652_, v_proof_653_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_672_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_672_ == 0)
{
v___x_662_ = v___x_659_;
v_isShared_663_ = v_isSharedCheck_672_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_659_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_672_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
uint8_t v___y_665_; 
if (v_contextDependent_633_ == 0)
{
v___y_665_ = v_contextDependent_655_;
goto v___jp_664_;
}
else
{
v___y_665_ = v_contextDependent_633_;
goto v___jp_664_;
}
v___jp_664_:
{
lean_object* v___x_667_; 
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v_a_660_);
v___x_667_ = v___x_657_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_e_x27_652_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_a_660_);
lean_ctor_set_uint8(v_reuseFailAlloc_671_, sizeof(void*)*2, v_done_654_);
v___x_667_ = v_reuseFailAlloc_671_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_669_; 
lean_ctor_set_uint8(v___x_667_, sizeof(void*)*2 + 1, v___y_665_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_667_);
v___x_669_ = v___x_662_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
lean_del_object(v___x_657_);
lean_dec_ref(v_e_x27_652_);
v_a_673_ = lean_ctor_get(v___x_659_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_659_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_659_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_635_);
lean_dec_ref(v_proof_632_);
lean_dec_ref(v_e_x27_631_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec_ref(v___y_599_);
return v___x_637_;
}
}
}
else
{
lean_dec_ref_known(v_a_611_, 2);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec_ref(v___f_598_);
return v___x_610_;
}
}
}
else
{
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec_ref(v___f_598_);
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3___boxed(lean_object* v___x_684_, lean_object* v___f_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3(v___x_684_, v___f_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec(v___x_684_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__5(lean_object* v_snd_698_, lean_object* v_a_699_, lean_object* v___x_700_, lean_object* v_____r_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_714_ = lean_array_push(v_snd_698_, v_a_699_);
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_700_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v___x_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__5___boxed(lean_object* v_snd_718_, lean_object* v_a_719_, lean_object* v___x_720_, lean_object* v_____r_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__5(v_snd_718_, v_a_719_, v___x_720_, v_____r_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(lean_object* v_msgData_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v___x_741_; lean_object* v_env_742_; lean_object* v___x_743_; lean_object* v_mctx_744_; lean_object* v_lctx_745_; lean_object* v_options_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_741_ = lean_st_ref_get(v___y_739_);
v_env_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc_ref(v_env_742_);
lean_dec(v___x_741_);
v___x_743_ = lean_st_ref_get(v___y_737_);
v_mctx_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc_ref(v_mctx_744_);
lean_dec(v___x_743_);
v_lctx_745_ = lean_ctor_get(v___y_736_, 2);
v_options_746_ = lean_ctor_get(v___y_738_, 2);
lean_inc_ref(v_options_746_);
lean_inc_ref(v_lctx_745_);
v___x_747_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_747_, 0, v_env_742_);
lean_ctor_set(v___x_747_, 1, v_mctx_744_);
lean_ctor_set(v___x_747_, 2, v_lctx_745_);
lean_ctor_set(v___x_747_, 3, v_options_746_);
v___x_748_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
lean_ctor_set(v___x_748_, 1, v_msgData_735_);
v___x_749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0___boxed(lean_object* v_msgData_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(v_msgData_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
return v_res_756_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_757_; double v___x_758_; 
v___x_757_ = lean_unsigned_to_nat(0u);
v___x_758_ = lean_float_of_nat(v___x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(lean_object* v_cls_762_, lean_object* v_msg_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_ref_769_; lean_object* v___x_770_; lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_815_; 
v_ref_769_ = lean_ctor_get(v___y_766_, 5);
v___x_770_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(v_msg_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
v_a_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_815_ == 0)
{
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_815_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_815_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; lean_object* v_traceState_776_; lean_object* v_env_777_; lean_object* v_nextMacroScope_778_; lean_object* v_ngen_779_; lean_object* v_auxDeclNGen_780_; lean_object* v_cache_781_; lean_object* v_messages_782_; lean_object* v_infoState_783_; lean_object* v_snapshotTasks_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_814_; 
v___x_775_ = lean_st_ref_take(v___y_767_);
v_traceState_776_ = lean_ctor_get(v___x_775_, 4);
v_env_777_ = lean_ctor_get(v___x_775_, 0);
v_nextMacroScope_778_ = lean_ctor_get(v___x_775_, 1);
v_ngen_779_ = lean_ctor_get(v___x_775_, 2);
v_auxDeclNGen_780_ = lean_ctor_get(v___x_775_, 3);
v_cache_781_ = lean_ctor_get(v___x_775_, 5);
v_messages_782_ = lean_ctor_get(v___x_775_, 6);
v_infoState_783_ = lean_ctor_get(v___x_775_, 7);
v_snapshotTasks_784_ = lean_ctor_get(v___x_775_, 8);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_814_ == 0)
{
v___x_786_ = v___x_775_;
v_isShared_787_ = v_isSharedCheck_814_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_snapshotTasks_784_);
lean_inc(v_infoState_783_);
lean_inc(v_messages_782_);
lean_inc(v_cache_781_);
lean_inc(v_traceState_776_);
lean_inc(v_auxDeclNGen_780_);
lean_inc(v_ngen_779_);
lean_inc(v_nextMacroScope_778_);
lean_inc(v_env_777_);
lean_dec(v___x_775_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_814_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
uint64_t v_tid_788_; lean_object* v_traces_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_813_; 
v_tid_788_ = lean_ctor_get_uint64(v_traceState_776_, sizeof(void*)*1);
v_traces_789_ = lean_ctor_get(v_traceState_776_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v_traceState_776_);
if (v_isSharedCheck_813_ == 0)
{
v___x_791_ = v_traceState_776_;
v_isShared_792_ = v_isSharedCheck_813_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_traces_789_);
lean_dec(v_traceState_776_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_813_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; double v___x_794_; uint8_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_803_; 
v___x_793_ = lean_box(0);
v___x_794_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0);
v___x_795_ = 0;
v___x_796_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1));
v___x_797_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_797_, 0, v_cls_762_);
lean_ctor_set(v___x_797_, 1, v___x_793_);
lean_ctor_set(v___x_797_, 2, v___x_796_);
lean_ctor_set_float(v___x_797_, sizeof(void*)*3, v___x_794_);
lean_ctor_set_float(v___x_797_, sizeof(void*)*3 + 8, v___x_794_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*3 + 16, v___x_795_);
v___x_798_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__2));
v___x_799_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_799_, 0, v___x_797_);
lean_ctor_set(v___x_799_, 1, v_a_771_);
lean_ctor_set(v___x_799_, 2, v___x_798_);
lean_inc(v_ref_769_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_ref_769_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = l_Lean_PersistentArray_push___redArg(v_traces_789_, v___x_800_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_801_);
v___x_803_ = v___x_791_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_801_);
lean_ctor_set_uint64(v_reuseFailAlloc_812_, sizeof(void*)*1, v_tid_788_);
v___x_803_ = v_reuseFailAlloc_812_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_805_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 4, v___x_803_);
v___x_805_ = v___x_786_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_env_777_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v_nextMacroScope_778_);
lean_ctor_set(v_reuseFailAlloc_811_, 2, v_ngen_779_);
lean_ctor_set(v_reuseFailAlloc_811_, 3, v_auxDeclNGen_780_);
lean_ctor_set(v_reuseFailAlloc_811_, 4, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_811_, 5, v_cache_781_);
lean_ctor_set(v_reuseFailAlloc_811_, 6, v_messages_782_);
lean_ctor_set(v_reuseFailAlloc_811_, 7, v_infoState_783_);
lean_ctor_set(v_reuseFailAlloc_811_, 8, v_snapshotTasks_784_);
v___x_805_ = v_reuseFailAlloc_811_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_806_ = lean_st_ref_set(v___y_767_, v___x_805_);
v___x_807_ = lean_box(0);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_807_);
v___x_809_ = v___x_773_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v___x_807_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___boxed(lean_object* v_cls_816_, lean_object* v_msg_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v_cls_816_, v_msg_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__3(lean_object* v_x_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__3___closed__0));
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__3___boxed(lean_object* v_x_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__3(v_x_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v_x_839_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__1(lean_object* v___f_851_, lean_object* v_x_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___x_864_; 
lean_inc_ref(v___y_853_);
v___x_864_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_853_, v___y_859_, v___y_861_, v___y_862_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_866_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
v___x_866_ = lean_box(0);
if (lean_obj_tag(v_a_865_) == 0)
{
uint8_t v_done_867_; 
v_done_867_ = lean_ctor_get_uint8(v_a_865_, 0);
lean_dec_ref_known(v_a_865_, 0);
if (v_done_867_ == 0)
{
lean_object* v___x_868_; 
lean_dec_ref_known(v___x_864_, 1);
lean_inc(v___y_862_);
lean_inc_ref(v___y_861_);
lean_inc(v___y_860_);
lean_inc_ref(v___y_859_);
lean_inc(v___y_858_);
lean_inc_ref(v___y_857_);
lean_inc(v___y_856_);
lean_inc_ref(v___y_855_);
lean_inc(v___y_854_);
v___x_868_ = lean_apply_12(v___f_851_, v___x_866_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, lean_box(0));
return v___x_868_;
}
else
{
lean_dec_ref(v___y_853_);
lean_dec_ref(v___f_851_);
return v___x_864_;
}
}
else
{
uint8_t v_done_869_; 
lean_dec_ref(v___y_853_);
v_done_869_ = lean_ctor_get_uint8(v_a_865_, sizeof(void*)*1);
if (v_done_869_ == 0)
{
lean_object* v_e_x27_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_888_; 
lean_dec_ref_known(v___x_864_, 1);
v_e_x27_870_ = lean_ctor_get(v_a_865_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v_a_865_);
if (v_isSharedCheck_888_ == 0)
{
v___x_872_ = v_a_865_;
v_isShared_873_ = v_isSharedCheck_888_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_e_x27_870_);
lean_dec(v_a_865_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_888_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; 
lean_inc(v___y_862_);
lean_inc_ref(v___y_861_);
lean_inc(v___y_860_);
lean_inc_ref(v___y_859_);
lean_inc(v___y_858_);
lean_inc_ref(v___y_857_);
lean_inc(v___y_856_);
lean_inc_ref(v___y_855_);
lean_inc(v___y_854_);
lean_inc_ref(v_e_x27_870_);
v___x_874_ = lean_apply_12(v___f_851_, v___x_866_, v_e_x27_870_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, lean_box(0));
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
if (lean_obj_tag(v_a_875_) == 0)
{
lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_886_; 
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; 
v_unused_887_ = lean_ctor_get(v___x_874_, 0);
lean_dec(v_unused_887_);
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_886_;
goto v_resetjp_876_;
}
else
{
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_886_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
uint8_t v_done_879_; lean_object* v___x_881_; 
v_done_879_ = lean_ctor_get_uint8(v_a_875_, 0);
lean_dec_ref_known(v_a_875_, 0);
if (v_isShared_873_ == 0)
{
v___x_881_ = v___x_872_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_e_x27_870_);
v___x_881_ = v_reuseFailAlloc_885_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_883_; 
lean_ctor_set_uint8(v___x_881_, sizeof(void*)*1, v_done_879_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_881_);
v___x_883_ = v___x_877_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_875_, 1);
lean_del_object(v___x_872_);
lean_dec_ref(v_e_x27_870_);
return v___x_874_;
}
}
else
{
lean_del_object(v___x_872_);
lean_dec_ref(v_e_x27_870_);
return v___x_874_;
}
}
}
else
{
lean_dec_ref_known(v_a_865_, 1);
lean_dec_ref(v___f_851_);
return v___x_864_;
}
}
}
else
{
lean_dec_ref(v___y_853_);
lean_dec_ref(v___f_851_);
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__1___boxed(lean_object* v___f_889_, lean_object* v_x_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__1(v___f_889_, v_x_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__2(lean_object* v___f_903_, lean_object* v_x_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; 
lean_inc_ref(v___y_905_);
v___x_916_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v___y_905_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_918_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
v___x_918_ = lean_box(0);
if (lean_obj_tag(v_a_917_) == 0)
{
uint8_t v_done_919_; 
v_done_919_ = lean_ctor_get_uint8(v_a_917_, 0);
lean_dec_ref_known(v_a_917_, 0);
if (v_done_919_ == 0)
{
lean_object* v___x_920_; 
lean_dec_ref_known(v___x_916_, 1);
lean_inc(v___y_914_);
lean_inc_ref(v___y_913_);
lean_inc(v___y_912_);
lean_inc_ref(v___y_911_);
lean_inc(v___y_910_);
lean_inc_ref(v___y_909_);
lean_inc(v___y_908_);
lean_inc_ref(v___y_907_);
lean_inc(v___y_906_);
v___x_920_ = lean_apply_12(v___f_903_, v___x_918_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, lean_box(0));
return v___x_920_;
}
else
{
lean_dec_ref(v___y_905_);
lean_dec_ref(v___f_903_);
return v___x_916_;
}
}
else
{
uint8_t v_done_921_; 
lean_dec_ref(v___y_905_);
v_done_921_ = lean_ctor_get_uint8(v_a_917_, sizeof(void*)*1);
if (v_done_921_ == 0)
{
lean_object* v_e_x27_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_940_; 
lean_dec_ref_known(v___x_916_, 1);
v_e_x27_922_ = lean_ctor_get(v_a_917_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v_a_917_);
if (v_isSharedCheck_940_ == 0)
{
v___x_924_ = v_a_917_;
v_isShared_925_ = v_isSharedCheck_940_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_e_x27_922_);
lean_dec(v_a_917_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_940_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; 
lean_inc(v___y_914_);
lean_inc_ref(v___y_913_);
lean_inc(v___y_912_);
lean_inc_ref(v___y_911_);
lean_inc(v___y_910_);
lean_inc_ref(v___y_909_);
lean_inc(v___y_908_);
lean_inc_ref(v___y_907_);
lean_inc(v___y_906_);
lean_inc_ref(v_e_x27_922_);
v___x_926_ = lean_apply_12(v___f_903_, v___x_918_, v_e_x27_922_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, lean_box(0));
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
lean_inc(v_a_927_);
if (lean_obj_tag(v_a_927_) == 0)
{
lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_938_; 
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; 
v_unused_939_ = lean_ctor_get(v___x_926_, 0);
lean_dec(v_unused_939_);
v___x_929_ = v___x_926_;
v_isShared_930_ = v_isSharedCheck_938_;
goto v_resetjp_928_;
}
else
{
lean_dec(v___x_926_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_938_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
uint8_t v_done_931_; lean_object* v___x_933_; 
v_done_931_ = lean_ctor_get_uint8(v_a_927_, 0);
lean_dec_ref_known(v_a_927_, 0);
if (v_isShared_925_ == 0)
{
v___x_933_ = v___x_924_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_e_x27_922_);
v___x_933_ = v_reuseFailAlloc_937_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_935_; 
lean_ctor_set_uint8(v___x_933_, sizeof(void*)*1, v_done_931_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_933_);
v___x_935_ = v___x_929_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_927_, 1);
lean_del_object(v___x_924_);
lean_dec_ref(v_e_x27_922_);
return v___x_926_;
}
}
else
{
lean_del_object(v___x_924_);
lean_dec_ref(v_e_x27_922_);
return v___x_926_;
}
}
}
else
{
lean_dec_ref_known(v_a_917_, 1);
lean_dec_ref(v___f_903_);
return v___x_916_;
}
}
}
else
{
lean_dec_ref(v___y_905_);
lean_dec_ref(v___f_903_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__2___boxed(lean_object* v___f_941_, lean_object* v_x_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__2(v___f_941_, v_x_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__4(lean_object* v___x_955_, lean_object* v___f_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___x_968_; 
lean_inc_ref(v___y_957_);
v___x_968_ = l_Lean_Meta_Sym_DSimp_evalGround___redArg(v___x_955_, v___y_957_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v_a_969_; lean_object* v___x_970_; 
v_a_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_a_969_);
v___x_970_ = lean_box(0);
if (lean_obj_tag(v_a_969_) == 0)
{
uint8_t v_done_971_; 
v_done_971_ = lean_ctor_get_uint8(v_a_969_, 0);
lean_dec_ref_known(v_a_969_, 0);
if (v_done_971_ == 0)
{
lean_object* v___x_972_; 
lean_dec_ref_known(v___x_968_, 1);
v___x_972_ = lean_apply_12(v___f_956_, v___x_970_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, lean_box(0));
return v___x_972_;
}
else
{
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec_ref(v___f_956_);
return v___x_968_;
}
}
else
{
uint8_t v_done_973_; 
lean_dec_ref(v___y_957_);
v_done_973_ = lean_ctor_get_uint8(v_a_969_, sizeof(void*)*1);
if (v_done_973_ == 0)
{
lean_object* v_e_x27_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_992_; 
lean_dec_ref_known(v___x_968_, 1);
v_e_x27_974_ = lean_ctor_get(v_a_969_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v_a_969_);
if (v_isSharedCheck_992_ == 0)
{
v___x_976_ = v_a_969_;
v_isShared_977_ = v_isSharedCheck_992_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_e_x27_974_);
lean_dec(v_a_969_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_992_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; 
lean_inc_ref(v_e_x27_974_);
v___x_978_ = lean_apply_12(v___f_956_, v___x_970_, v_e_x27_974_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, lean_box(0));
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_a_979_);
if (lean_obj_tag(v_a_979_) == 0)
{
lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_990_; 
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_990_ == 0)
{
lean_object* v_unused_991_; 
v_unused_991_ = lean_ctor_get(v___x_978_, 0);
lean_dec(v_unused_991_);
v___x_981_ = v___x_978_;
v_isShared_982_ = v_isSharedCheck_990_;
goto v_resetjp_980_;
}
else
{
lean_dec(v___x_978_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_990_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
uint8_t v_done_983_; lean_object* v___x_985_; 
v_done_983_ = lean_ctor_get_uint8(v_a_979_, 0);
lean_dec_ref_known(v_a_979_, 0);
if (v_isShared_977_ == 0)
{
v___x_985_ = v___x_976_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_e_x27_974_);
v___x_985_ = v_reuseFailAlloc_989_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_987_; 
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*1, v_done_983_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v___x_985_);
v___x_987_ = v___x_981_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_979_, 1);
lean_del_object(v___x_976_);
lean_dec_ref(v_e_x27_974_);
return v___x_978_;
}
}
else
{
lean_del_object(v___x_976_);
lean_dec_ref(v_e_x27_974_);
return v___x_978_;
}
}
}
else
{
lean_dec_ref_known(v_a_969_, 1);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___f_956_);
return v___x_968_;
}
}
}
else
{
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec_ref(v___f_956_);
return v___x_968_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__4___boxed(lean_object* v___x_993_, lean_object* v___f_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__4(v___x_993_, v___f_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
lean_dec(v___x_993_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__6(uint8_t v___x_1007_, lean_object* v___f_1008_, lean_object* v_____r_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___x_1022_; lean_object* v_rewriteSimpCache_1023_; lean_object* v_rewriteDSimpCache_1024_; lean_object* v_acCache_1025_; lean_object* v_typeAnalysis_1026_; lean_object* v_target_1027_; lean_object* v_hypotheses_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1038_; 
v___x_1022_ = lean_st_ref_take(v___y_1011_);
v_rewriteSimpCache_1023_ = lean_ctor_get(v___x_1022_, 0);
v_rewriteDSimpCache_1024_ = lean_ctor_get(v___x_1022_, 1);
v_acCache_1025_ = lean_ctor_get(v___x_1022_, 2);
v_typeAnalysis_1026_ = lean_ctor_get(v___x_1022_, 3);
v_target_1027_ = lean_ctor_get(v___x_1022_, 4);
v_hypotheses_1028_ = lean_ctor_get(v___x_1022_, 5);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1030_ = v___x_1022_;
v_isShared_1031_ = v_isSharedCheck_1038_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_hypotheses_1028_);
lean_inc(v_target_1027_);
lean_inc(v_typeAnalysis_1026_);
lean_inc(v_acCache_1025_);
lean_inc(v_rewriteDSimpCache_1024_);
lean_inc(v_rewriteSimpCache_1023_);
lean_dec(v___x_1022_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1038_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_rewriteSimpCache_1023_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_rewriteDSimpCache_1024_);
lean_ctor_set(v_reuseFailAlloc_1037_, 2, v_acCache_1025_);
lean_ctor_set(v_reuseFailAlloc_1037_, 3, v_typeAnalysis_1026_);
lean_ctor_set(v_reuseFailAlloc_1037_, 4, v_target_1027_);
lean_ctor_set(v_reuseFailAlloc_1037_, 5, v_hypotheses_1028_);
v___x_1033_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
lean_ctor_set_uint8(v___x_1033_, sizeof(void*)*6, v___x_1007_);
v___x_1034_ = lean_st_ref_set(v___y_1011_, v___x_1033_);
v___x_1035_ = lean_box(0);
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
lean_inc(v___y_1016_);
lean_inc_ref(v___y_1015_);
lean_inc(v___y_1014_);
lean_inc_ref(v___y_1013_);
lean_inc(v___y_1012_);
lean_inc(v___y_1011_);
lean_inc_ref(v___y_1010_);
v___x_1036_ = lean_apply_13(v___f_1008_, v___x_1035_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, lean_box(0));
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__6___boxed(lean_object* v___x_1039_, lean_object* v___f_1040_, lean_object* v_____r_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_){
_start:
{
uint8_t v___x_206820__boxed_1054_; lean_object* v_res_1055_; 
v___x_206820__boxed_1054_ = lean_unbox(v___x_1039_);
v_res_1055_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__6(v___x_206820__boxed_1054_, v___f_1040_, v_____r_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__16_spec__19___redArg(lean_object* v_x_1056_, lean_object* v_x_1057_, lean_object* v_x_1058_, lean_object* v_x_1059_){
_start:
{
lean_object* v_ks_1060_; lean_object* v_vs_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1085_; 
v_ks_1060_ = lean_ctor_get(v_x_1056_, 0);
v_vs_1061_ = lean_ctor_get(v_x_1056_, 1);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_x_1056_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1063_ = v_x_1056_;
v_isShared_1064_ = v_isSharedCheck_1085_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_vs_1061_);
lean_inc(v_ks_1060_);
lean_dec(v_x_1056_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1085_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1065_ = lean_array_get_size(v_ks_1060_);
v___x_1066_ = lean_nat_dec_lt(v_x_1057_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1070_; 
lean_dec(v_x_1057_);
v___x_1067_ = lean_array_push(v_ks_1060_, v_x_1058_);
v___x_1068_ = lean_array_push(v_vs_1061_, v_x_1059_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 1, v___x_1068_);
lean_ctor_set(v___x_1063_, 0, v___x_1067_);
v___x_1070_ = v___x_1063_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1067_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v___x_1068_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
else
{
lean_object* v_k_x27_1072_; uint8_t v___x_1073_; 
v_k_x27_1072_ = lean_array_fget_borrowed(v_ks_1060_, v_x_1057_);
v___x_1073_ = l_Lean_instBEqMVarId_beq(v_x_1058_, v_k_x27_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1075_; 
if (v_isShared_1064_ == 0)
{
v___x_1075_ = v___x_1063_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_ks_1060_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_vs_1061_);
v___x_1075_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_unsigned_to_nat(1u);
v___x_1077_ = lean_nat_add(v_x_1057_, v___x_1076_);
lean_dec(v_x_1057_);
v_x_1056_ = v___x_1075_;
v_x_1057_ = v___x_1077_;
goto _start;
}
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1080_ = lean_array_fset(v_ks_1060_, v_x_1057_, v_x_1058_);
v___x_1081_ = lean_array_fset(v_vs_1061_, v_x_1057_, v_x_1059_);
lean_dec(v_x_1057_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 1, v___x_1081_);
lean_ctor_set(v___x_1063_, 0, v___x_1080_);
v___x_1083_ = v___x_1063_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__16___redArg(lean_object* v_n_1086_, lean_object* v_k_1087_, lean_object* v_v_1088_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = lean_unsigned_to_nat(0u);
v___x_1090_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__16_spec__19___redArg(v_n_1086_, v___x_1089_, v_k_1087_, v_v_1088_);
return v___x_1090_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg(lean_object* v_x_1092_, size_t v_x_1093_, size_t v_x_1094_, lean_object* v_x_1095_, lean_object* v_x_1096_){
_start:
{
if (lean_obj_tag(v_x_1092_) == 0)
{
lean_object* v_es_1097_; size_t v___x_1098_; size_t v___x_1099_; lean_object* v_j_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v_es_1097_ = lean_ctor_get(v_x_1092_, 0);
v___x_1098_ = ((size_t)31ULL);
v___x_1099_ = lean_usize_land(v_x_1093_, v___x_1098_);
v_j_1100_ = lean_usize_to_nat(v___x_1099_);
v___x_1101_ = lean_array_get_size(v_es_1097_);
v___x_1102_ = lean_nat_dec_lt(v_j_1100_, v___x_1101_);
if (v___x_1102_ == 0)
{
lean_dec(v_j_1100_);
lean_dec(v_x_1096_);
lean_dec(v_x_1095_);
return v_x_1092_;
}
else
{
lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1141_; 
lean_inc_ref(v_es_1097_);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_x_1092_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; 
v_unused_1142_ = lean_ctor_get(v_x_1092_, 0);
lean_dec(v_unused_1142_);
v___x_1104_ = v_x_1092_;
v_isShared_1105_ = v_isSharedCheck_1141_;
goto v_resetjp_1103_;
}
else
{
lean_dec(v_x_1092_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1141_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v_v_1106_; lean_object* v___x_1107_; lean_object* v_xs_x27_1108_; lean_object* v___y_1110_; 
v_v_1106_ = lean_array_fget(v_es_1097_, v_j_1100_);
v___x_1107_ = lean_box(0);
v_xs_x27_1108_ = lean_array_fset(v_es_1097_, v_j_1100_, v___x_1107_);
switch(lean_obj_tag(v_v_1106_))
{
case 0:
{
lean_object* v_key_1115_; lean_object* v_val_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1126_; 
v_key_1115_ = lean_ctor_get(v_v_1106_, 0);
v_val_1116_ = lean_ctor_get(v_v_1106_, 1);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_v_1106_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1118_ = v_v_1106_;
v_isShared_1119_ = v_isSharedCheck_1126_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_val_1116_);
lean_inc(v_key_1115_);
lean_dec(v_v_1106_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1126_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
uint8_t v___x_1120_; 
v___x_1120_ = l_Lean_instBEqMVarId_beq(v_x_1095_, v_key_1115_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_del_object(v___x_1118_);
v___x_1121_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1115_, v_val_1116_, v_x_1095_, v_x_1096_);
v___x_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
v___y_1110_ = v___x_1122_;
goto v___jp_1109_;
}
else
{
lean_object* v___x_1124_; 
lean_dec(v_val_1116_);
lean_dec(v_key_1115_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 1, v_x_1096_);
lean_ctor_set(v___x_1118_, 0, v_x_1095_);
v___x_1124_ = v___x_1118_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_x_1095_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_x_1096_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
v___y_1110_ = v___x_1124_;
goto v___jp_1109_;
}
}
}
}
case 1:
{
lean_object* v_node_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1139_; 
v_node_1127_ = lean_ctor_get(v_v_1106_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_v_1106_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1129_ = v_v_1106_;
v_isShared_1130_ = v_isSharedCheck_1139_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_node_1127_);
lean_dec(v_v_1106_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1139_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
size_t v___x_1131_; size_t v___x_1132_; size_t v___x_1133_; size_t v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1131_ = ((size_t)5ULL);
v___x_1132_ = lean_usize_shift_right(v_x_1093_, v___x_1131_);
v___x_1133_ = ((size_t)1ULL);
v___x_1134_ = lean_usize_add(v_x_1094_, v___x_1133_);
v___x_1135_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg(v_node_1127_, v___x_1132_, v___x_1134_, v_x_1095_, v_x_1096_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1135_);
v___x_1137_ = v___x_1129_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
v___y_1110_ = v___x_1137_;
goto v___jp_1109_;
}
}
}
default: 
{
lean_object* v___x_1140_; 
v___x_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1140_, 0, v_x_1095_);
lean_ctor_set(v___x_1140_, 1, v_x_1096_);
v___y_1110_ = v___x_1140_;
goto v___jp_1109_;
}
}
v___jp_1109_:
{
lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1111_ = lean_array_fset(v_xs_x27_1108_, v_j_1100_, v___y_1110_);
lean_dec(v_j_1100_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1111_);
v___x_1113_ = v___x_1104_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1111_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
else
{
lean_object* v_ks_1143_; lean_object* v_vs_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1164_; 
v_ks_1143_ = lean_ctor_get(v_x_1092_, 0);
v_vs_1144_ = lean_ctor_get(v_x_1092_, 1);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_x_1092_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1146_ = v_x_1092_;
v_isShared_1147_ = v_isSharedCheck_1164_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_vs_1144_);
lean_inc(v_ks_1143_);
lean_dec(v_x_1092_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1164_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1149_; 
if (v_isShared_1147_ == 0)
{
v___x_1149_ = v___x_1146_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_ks_1143_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_vs_1144_);
v___x_1149_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v_newNode_1150_; uint8_t v___y_1152_; size_t v___x_1158_; uint8_t v___x_1159_; 
v_newNode_1150_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__16___redArg(v___x_1149_, v_x_1095_, v_x_1096_);
v___x_1158_ = ((size_t)7ULL);
v___x_1159_ = lean_usize_dec_le(v___x_1158_, v_x_1094_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; uint8_t v___x_1162_; 
v___x_1160_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1150_);
v___x_1161_ = lean_unsigned_to_nat(4u);
v___x_1162_ = lean_nat_dec_lt(v___x_1160_, v___x_1161_);
lean_dec(v___x_1160_);
v___y_1152_ = v___x_1162_;
goto v___jp_1151_;
}
else
{
v___y_1152_ = v___x_1159_;
goto v___jp_1151_;
}
v___jp_1151_:
{
if (v___y_1152_ == 0)
{
lean_object* v_ks_1153_; lean_object* v_vs_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v_ks_1153_ = lean_ctor_get(v_newNode_1150_, 0);
lean_inc_ref(v_ks_1153_);
v_vs_1154_ = lean_ctor_get(v_newNode_1150_, 1);
lean_inc_ref(v_vs_1154_);
lean_dec_ref(v_newNode_1150_);
v___x_1155_ = lean_unsigned_to_nat(0u);
v___x_1156_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg___closed__0);
v___x_1157_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__17___redArg(v_x_1094_, v_ks_1153_, v_vs_1154_, v___x_1155_, v___x_1156_);
lean_dec_ref(v_vs_1154_);
lean_dec_ref(v_ks_1153_);
return v___x_1157_;
}
else
{
return v_newNode_1150_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__17___redArg(size_t v_depth_1165_, lean_object* v_keys_1166_, lean_object* v_vals_1167_, lean_object* v_i_1168_, lean_object* v_entries_1169_){
_start:
{
lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = lean_array_get_size(v_keys_1166_);
v___x_1171_ = lean_nat_dec_lt(v_i_1168_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_dec(v_i_1168_);
return v_entries_1169_;
}
else
{
lean_object* v_k_1172_; lean_object* v_v_1173_; uint64_t v___x_1174_; size_t v_h_1175_; size_t v___x_1176_; lean_object* v___x_1177_; size_t v___x_1178_; size_t v___x_1179_; size_t v___x_1180_; size_t v_h_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v_k_1172_ = lean_array_fget_borrowed(v_keys_1166_, v_i_1168_);
v_v_1173_ = lean_array_fget_borrowed(v_vals_1167_, v_i_1168_);
v___x_1174_ = l_Lean_instHashableMVarId_hash(v_k_1172_);
v_h_1175_ = lean_uint64_to_usize(v___x_1174_);
v___x_1176_ = ((size_t)5ULL);
v___x_1177_ = lean_unsigned_to_nat(1u);
v___x_1178_ = ((size_t)1ULL);
v___x_1179_ = lean_usize_sub(v_depth_1165_, v___x_1178_);
v___x_1180_ = lean_usize_mul(v___x_1176_, v___x_1179_);
v_h_1181_ = lean_usize_shift_right(v_h_1175_, v___x_1180_);
v___x_1182_ = lean_nat_add(v_i_1168_, v___x_1177_);
lean_dec(v_i_1168_);
lean_inc(v_v_1173_);
lean_inc(v_k_1172_);
v___x_1183_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg(v_entries_1169_, v_h_1181_, v_depth_1165_, v_k_1172_, v_v_1173_);
v_i_1168_ = v___x_1182_;
v_entries_1169_ = v___x_1183_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__17___redArg___boxed(lean_object* v_depth_1185_, lean_object* v_keys_1186_, lean_object* v_vals_1187_, lean_object* v_i_1188_, lean_object* v_entries_1189_){
_start:
{
size_t v_depth_boxed_1190_; lean_object* v_res_1191_; 
v_depth_boxed_1190_ = lean_unbox_usize(v_depth_1185_);
lean_dec(v_depth_1185_);
v_res_1191_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__17___redArg(v_depth_boxed_1190_, v_keys_1186_, v_vals_1187_, v_i_1188_, v_entries_1189_);
lean_dec_ref(v_vals_1187_);
lean_dec_ref(v_keys_1186_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_x_1192_, lean_object* v_x_1193_, lean_object* v_x_1194_, lean_object* v_x_1195_, lean_object* v_x_1196_){
_start:
{
size_t v_x_206964__boxed_1197_; size_t v_x_206965__boxed_1198_; lean_object* v_res_1199_; 
v_x_206964__boxed_1197_ = lean_unbox_usize(v_x_1193_);
lean_dec(v_x_1193_);
v_x_206965__boxed_1198_ = lean_unbox_usize(v_x_1194_);
lean_dec(v_x_1194_);
v_res_1199_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg(v_x_1192_, v_x_206964__boxed_1197_, v_x_206965__boxed_1198_, v_x_1195_, v_x_1196_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2___redArg(lean_object* v_x_1200_, lean_object* v_x_1201_, lean_object* v_x_1202_){
_start:
{
uint64_t v___x_1203_; size_t v___x_1204_; size_t v___x_1205_; lean_object* v___x_1206_; 
v___x_1203_ = l_Lean_instHashableMVarId_hash(v_x_1201_);
v___x_1204_ = lean_uint64_to_usize(v___x_1203_);
v___x_1205_ = ((size_t)1ULL);
v___x_1206_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg(v_x_1200_, v___x_1204_, v___x_1205_, v_x_1201_, v_x_1202_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(lean_object* v_mvarId_1207_, lean_object* v_val_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v___x_1211_; lean_object* v_mctx_1212_; lean_object* v_cache_1213_; lean_object* v_zetaDeltaFVarIds_1214_; lean_object* v_postponed_1215_; lean_object* v_diag_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1244_; 
v___x_1211_ = lean_st_ref_take(v___y_1209_);
v_mctx_1212_ = lean_ctor_get(v___x_1211_, 0);
v_cache_1213_ = lean_ctor_get(v___x_1211_, 1);
v_zetaDeltaFVarIds_1214_ = lean_ctor_get(v___x_1211_, 2);
v_postponed_1215_ = lean_ctor_get(v___x_1211_, 3);
v_diag_1216_ = lean_ctor_get(v___x_1211_, 4);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1218_ = v___x_1211_;
v_isShared_1219_ = v_isSharedCheck_1244_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_diag_1216_);
lean_inc(v_postponed_1215_);
lean_inc(v_zetaDeltaFVarIds_1214_);
lean_inc(v_cache_1213_);
lean_inc(v_mctx_1212_);
lean_dec(v___x_1211_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1244_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v_depth_1220_; lean_object* v_levelAssignDepth_1221_; lean_object* v_lmvarCounter_1222_; lean_object* v_mvarCounter_1223_; lean_object* v_lDecls_1224_; lean_object* v_decls_1225_; lean_object* v_userNames_1226_; lean_object* v_lAssignment_1227_; lean_object* v_eAssignment_1228_; lean_object* v_dAssignment_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1243_; 
v_depth_1220_ = lean_ctor_get(v_mctx_1212_, 0);
v_levelAssignDepth_1221_ = lean_ctor_get(v_mctx_1212_, 1);
v_lmvarCounter_1222_ = lean_ctor_get(v_mctx_1212_, 2);
v_mvarCounter_1223_ = lean_ctor_get(v_mctx_1212_, 3);
v_lDecls_1224_ = lean_ctor_get(v_mctx_1212_, 4);
v_decls_1225_ = lean_ctor_get(v_mctx_1212_, 5);
v_userNames_1226_ = lean_ctor_get(v_mctx_1212_, 6);
v_lAssignment_1227_ = lean_ctor_get(v_mctx_1212_, 7);
v_eAssignment_1228_ = lean_ctor_get(v_mctx_1212_, 8);
v_dAssignment_1229_ = lean_ctor_get(v_mctx_1212_, 9);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_mctx_1212_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1231_ = v_mctx_1212_;
v_isShared_1232_ = v_isSharedCheck_1243_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_dAssignment_1229_);
lean_inc(v_eAssignment_1228_);
lean_inc(v_lAssignment_1227_);
lean_inc(v_userNames_1226_);
lean_inc(v_decls_1225_);
lean_inc(v_lDecls_1224_);
lean_inc(v_mvarCounter_1223_);
lean_inc(v_lmvarCounter_1222_);
lean_inc(v_levelAssignDepth_1221_);
lean_inc(v_depth_1220_);
lean_dec(v_mctx_1212_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1243_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1233_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2___redArg(v_eAssignment_1228_, v_mvarId_1207_, v_val_1208_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 8, v___x_1233_);
v___x_1235_ = v___x_1231_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_depth_1220_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_levelAssignDepth_1221_);
lean_ctor_set(v_reuseFailAlloc_1242_, 2, v_lmvarCounter_1222_);
lean_ctor_set(v_reuseFailAlloc_1242_, 3, v_mvarCounter_1223_);
lean_ctor_set(v_reuseFailAlloc_1242_, 4, v_lDecls_1224_);
lean_ctor_set(v_reuseFailAlloc_1242_, 5, v_decls_1225_);
lean_ctor_set(v_reuseFailAlloc_1242_, 6, v_userNames_1226_);
lean_ctor_set(v_reuseFailAlloc_1242_, 7, v_lAssignment_1227_);
lean_ctor_set(v_reuseFailAlloc_1242_, 8, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1242_, 9, v_dAssignment_1229_);
v___x_1235_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1237_; 
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v___x_1235_);
v___x_1237_ = v___x_1218_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_cache_1213_);
lean_ctor_set(v_reuseFailAlloc_1241_, 2, v_zetaDeltaFVarIds_1214_);
lean_ctor_set(v_reuseFailAlloc_1241_, 3, v_postponed_1215_);
lean_ctor_set(v_reuseFailAlloc_1241_, 4, v_diag_1216_);
v___x_1237_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___x_1238_ = lean_st_ref_set(v___y_1209_, v___x_1237_);
v___x_1239_ = lean_box(0);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
return v___x_1240_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___boxed(lean_object* v_mvarId_1245_, lean_object* v_val_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v_mvarId_1245_, v_val_1246_, v___y_1247_);
lean_dec(v___y_1247_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0(lean_object* v_x_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; 
lean_inc_ref(v___y_1251_);
v___x_1262_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_1251_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
if (lean_obj_tag(v_a_1263_) == 0)
{
uint8_t v_done_1264_; 
v_done_1264_ = lean_ctor_get_uint8(v_a_1263_, 0);
lean_dec_ref_known(v_a_1263_, 0);
if (v_done_1264_ == 0)
{
lean_object* v___x_1265_; 
lean_dec_ref_known(v___x_1262_, 1);
v___x_1265_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteDsimproc___redArg(v___y_1251_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
return v___x_1265_;
}
else
{
lean_dec_ref(v___y_1251_);
return v___x_1262_;
}
}
else
{
uint8_t v_done_1266_; 
lean_dec_ref(v___y_1251_);
v_done_1266_ = lean_ctor_get_uint8(v_a_1263_, sizeof(void*)*1);
if (v_done_1266_ == 0)
{
lean_object* v_e_x27_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1285_; 
lean_dec_ref_known(v___x_1262_, 1);
v_e_x27_1267_ = lean_ctor_get(v_a_1263_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_a_1263_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1269_ = v_a_1263_;
v_isShared_1270_ = v_isSharedCheck_1285_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_e_x27_1267_);
lean_dec(v_a_1263_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1285_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; 
lean_inc_ref(v_e_x27_1267_);
v___x_1271_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteDsimproc___redArg(v_e_x27_1267_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
if (lean_obj_tag(v_a_1272_) == 0)
{
lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1283_; 
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1283_ == 0)
{
lean_object* v_unused_1284_; 
v_unused_1284_ = lean_ctor_get(v___x_1271_, 0);
lean_dec(v_unused_1284_);
v___x_1274_ = v___x_1271_;
v_isShared_1275_ = v_isSharedCheck_1283_;
goto v_resetjp_1273_;
}
else
{
lean_dec(v___x_1271_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1283_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
uint8_t v_done_1276_; lean_object* v___x_1278_; 
v_done_1276_ = lean_ctor_get_uint8(v_a_1272_, 0);
lean_dec_ref_known(v_a_1272_, 0);
if (v_isShared_1270_ == 0)
{
v___x_1278_ = v___x_1269_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_e_x27_1267_);
v___x_1278_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1280_; 
lean_ctor_set_uint8(v___x_1278_, sizeof(void*)*1, v_done_1276_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1278_);
v___x_1280_ = v___x_1274_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_1272_, 1);
lean_del_object(v___x_1269_);
lean_dec_ref(v_e_x27_1267_);
return v___x_1271_;
}
}
else
{
lean_del_object(v___x_1269_);
lean_dec_ref(v_e_x27_1267_);
return v___x_1271_;
}
}
}
else
{
lean_dec_ref_known(v_a_1263_, 1);
return v___x_1262_;
}
}
}
else
{
lean_dec_ref(v___y_1251_);
return v___x_1262_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0___boxed(lean_object* v_x_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0(v_x_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
lean_dec(v___y_1290_);
lean_dec_ref(v___y_1289_);
lean_dec(v___y_1288_);
return v_res_1298_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12(void){
_start:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1321_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__9));
v___x_1322_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__11));
v___x_1323_ = l_Lean_Name_append(v___x_1322_, v___x_1321_);
return v___x_1323_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__14(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__13));
v___x_1326_ = l_Lean_stringToMessageData(v___x_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg(lean_object* v_upperBound_1327_, lean_object* v___x_1328_, lean_object* v___x_1329_, lean_object* v___x_1330_, lean_object* v___x_1331_, lean_object* v_a_1332_, lean_object* v_b_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v___y_1347_; lean_object* v___y_1370_; uint8_t v___x_1373_; 
v___x_1373_ = lean_nat_dec_lt(v_a_1332_, v_upperBound_1327_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; 
lean_dec(v_a_1332_);
lean_dec_ref(v___x_1331_);
lean_dec_ref(v___x_1330_);
lean_dec_ref(v___x_1329_);
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v_b_1333_);
return v___x_1374_;
}
else
{
lean_object* v_snd_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1457_; 
v_snd_1375_ = lean_ctor_get(v_b_1333_, 1);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_b_1333_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; 
v_unused_1458_ = lean_ctor_get(v_b_1333_, 0);
lean_dec(v_unused_1458_);
v___x_1377_ = v_b_1333_;
v_isShared_1378_ = v_isSharedCheck_1457_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_snd_1375_);
lean_dec(v_b_1333_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1457_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1409_; lean_object* v___x_1454_; 
v___x_1379_ = lean_box(0);
v___x_1380_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__5));
v___x_1381_ = lean_array_fget_borrowed(v___x_1328_, v_a_1332_);
lean_inc(v___x_1381_);
lean_inc_ref(v___x_1329_);
v___x_1454_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg(v___x_1380_, v___x_1329_, v___x_1381_, v___y_1335_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1456_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref_known(v___x_1454_, 1);
lean_inc_ref(v___x_1331_);
lean_inc_ref(v___x_1330_);
v___x_1456_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg(v___x_1330_, v___x_1331_, v_a_1455_, v___y_1335_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
v___y_1409_ = v___x_1456_;
goto v___jp_1408_;
}
else
{
v___y_1409_ = v___x_1454_;
goto v___jp_1408_;
}
v___jp_1382_:
{
lean_object* v_options_1385_; uint8_t v_hasTrace_1386_; 
v_options_1385_ = lean_ctor_get(v___y_1343_, 2);
v_hasTrace_1386_ = lean_ctor_get_uint8(v_options_1385_, sizeof(void*)*1);
if (v_hasTrace_1386_ == 0)
{
lean_dec_ref(v___y_1384_);
v___y_1370_ = v___y_1383_;
goto v___jp_1369_;
}
else
{
lean_object* v_inheritedTraceOptions_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v_inheritedTraceOptions_1387_ = lean_ctor_get(v___y_1343_, 13);
v___x_1388_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__9));
v___x_1389_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12);
v___x_1390_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1387_, v_options_1385_, v___x_1389_);
if (v___x_1390_ == 0)
{
lean_dec_ref(v___y_1384_);
v___y_1370_ = v___y_1383_;
goto v___jp_1369_;
}
else
{
lean_object* v_type_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v_type_1391_ = lean_ctor_get(v___x_1381_, 1);
lean_inc_ref(v_type_1391_);
v___x_1392_ = l_Lean_MessageData_ofExpr(v_type_1391_);
v___x_1393_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__14, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__14_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__14);
v___x_1394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1392_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = l_Lean_MessageData_ofExpr(v___y_1384_);
v___x_1396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1394_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
v___x_1397_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v___x_1388_, v___x_1396_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; lean_object* v___x_1399_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1397_, 1);
lean_inc(v___y_1344_);
lean_inc_ref(v___y_1343_);
lean_inc(v___y_1342_);
lean_inc_ref(v___y_1341_);
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
lean_inc(v___y_1338_);
lean_inc_ref(v___y_1337_);
lean_inc(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc_ref(v___y_1334_);
v___x_1399_ = lean_apply_13(v___y_1383_, v_a_1398_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, lean_box(0));
v___y_1347_ = v___x_1399_;
goto v___jp_1346_;
}
else
{
lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1407_; 
lean_dec_ref(v___y_1383_);
lean_dec(v_a_1332_);
lean_dec_ref(v___x_1331_);
lean_dec_ref(v___x_1330_);
lean_dec_ref(v___x_1329_);
v_a_1400_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1402_ = v___x_1397_;
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1397_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1407_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1405_; 
if (v_isShared_1403_ == 0)
{
v___x_1405_ = v___x_1402_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v_a_1400_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
}
}
v___jp_1408_:
{
if (lean_obj_tag(v___y_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v_type_1411_; lean_object* v_value_1412_; uint8_t v___x_1413_; 
v_a_1410_ = lean_ctor_get(v___y_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___y_1409_, 1);
v_type_1411_ = lean_ctor_get(v_a_1410_, 1);
v_value_1412_ = lean_ctor_get(v_a_1410_, 2);
lean_inc_ref(v_type_1411_);
v___x_1413_ = l_Lean_Expr_isFalse(v_type_1411_);
if (v___x_1413_ == 0)
{
lean_object* v_type_1414_; lean_object* v___f_1415_; lean_object* v___x_1416_; lean_object* v___f_1417_; uint8_t v___x_1418_; 
lean_del_object(v___x_1377_);
v_type_1414_ = lean_ctor_get(v___x_1381_, 1);
lean_inc(v_a_1410_);
lean_inc(v_snd_1375_);
v___f_1415_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__5___boxed), 16, 3);
lean_closure_set(v___f_1415_, 0, v_snd_1375_);
lean_closure_set(v___f_1415_, 1, v_a_1410_);
lean_closure_set(v___f_1415_, 2, v___x_1379_);
v___x_1416_ = lean_box(v___x_1373_);
v___f_1417_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__6___boxed), 15, 2);
lean_closure_set(v___f_1417_, 0, v___x_1416_);
lean_closure_set(v___f_1417_, 1, v___f_1415_);
v___x_1418_ = lean_expr_eqv(v_type_1414_, v_type_1411_);
if (v___x_1418_ == 0)
{
lean_inc_ref(v_type_1411_);
lean_dec(v_a_1410_);
lean_dec(v_snd_1375_);
v___y_1383_ = v___f_1417_;
v___y_1384_ = v_type_1411_;
goto v___jp_1382_;
}
else
{
if (v___x_1413_ == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
lean_dec_ref(v___f_1417_);
v___x_1419_ = lean_box(0);
v___x_1420_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__5(v_snd_1375_, v_a_1410_, v___x_1379_, v___x_1419_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
v___y_1347_ = v___x_1420_;
goto v___jp_1346_;
}
else
{
lean_inc_ref(v_type_1411_);
lean_dec(v_a_1410_);
lean_dec(v_snd_1375_);
v___y_1383_ = v___f_1417_;
v___y_1384_ = v_type_1411_;
goto v___jp_1382_;
}
}
}
else
{
lean_object* v___x_1421_; lean_object* v_target_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
lean_inc_ref(v_value_1412_);
lean_dec(v_a_1410_);
lean_dec(v_a_1332_);
lean_dec_ref(v___x_1331_);
lean_dec_ref(v___x_1330_);
lean_dec_ref(v___x_1329_);
v___x_1421_ = lean_st_ref_get(v___y_1335_);
v_target_1422_ = lean_ctor_get(v___x_1421_, 4);
lean_inc_ref(v_target_1422_);
lean_dec(v___x_1421_);
v___x_1423_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_1422_);
lean_dec_ref(v_target_1422_);
v___x_1424_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v___x_1423_, v_value_1412_, v___y_1342_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1436_; 
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1436_ == 0)
{
lean_object* v_unused_1437_; 
v_unused_1437_ = lean_ctor_get(v___x_1424_, 0);
lean_dec(v_unused_1437_);
v___x_1426_ = v___x_1424_;
v_isShared_1427_ = v_isSharedCheck_1436_;
goto v_resetjp_1425_;
}
else
{
lean_dec(v___x_1424_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1436_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1431_; 
v___x_1428_ = lean_box(v___x_1413_);
v___x_1429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 0, v___x_1429_);
v___x_1431_ = v___x_1377_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_snd_1375_);
v___x_1431_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1433_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1431_);
v___x_1433_ = v___x_1426_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_del_object(v___x_1377_);
lean_dec(v_snd_1375_);
v_a_1438_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1424_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1424_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_del_object(v___x_1377_);
lean_dec(v_snd_1375_);
lean_dec(v_a_1332_);
lean_dec_ref(v___x_1331_);
lean_dec_ref(v___x_1330_);
lean_dec_ref(v___x_1329_);
v_a_1446_ = lean_ctor_get(v___y_1409_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___y_1409_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___y_1409_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___y_1409_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
}
}
v___jp_1346_:
{
if (lean_obj_tag(v___y_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1360_; 
v_a_1348_ = lean_ctor_get(v___y_1347_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___y_1347_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1350_ = v___y_1347_;
v_isShared_1351_ = v_isSharedCheck_1360_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___y_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1360_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
if (lean_obj_tag(v_a_1348_) == 0)
{
lean_object* v_a_1352_; lean_object* v___x_1354_; 
lean_dec(v_a_1332_);
lean_dec_ref(v___x_1331_);
lean_dec_ref(v___x_1330_);
lean_dec_ref(v___x_1329_);
v_a_1352_ = lean_ctor_get(v_a_1348_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v_a_1348_, 1);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v_a_1352_);
v___x_1354_ = v___x_1350_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_del_object(v___x_1350_);
v_a_1356_ = lean_ctor_get(v_a_1348_, 0);
lean_inc(v_a_1356_);
lean_dec_ref_known(v_a_1348_, 1);
v___x_1357_ = lean_unsigned_to_nat(1u);
v___x_1358_ = lean_nat_add(v_a_1332_, v___x_1357_);
lean_dec(v_a_1332_);
v_a_1332_ = v___x_1358_;
v_b_1333_ = v_a_1356_;
goto _start;
}
}
}
else
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec(v_a_1332_);
lean_dec_ref(v___x_1331_);
lean_dec_ref(v___x_1330_);
lean_dec_ref(v___x_1329_);
v_a_1361_ = lean_ctor_get(v___y_1347_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___y_1347_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___y_1347_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___y_1347_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
}
v___jp_1369_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1371_ = lean_box(0);
lean_inc(v___y_1344_);
lean_inc_ref(v___y_1343_);
lean_inc(v___y_1342_);
lean_inc_ref(v___y_1341_);
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
lean_inc(v___y_1338_);
lean_inc_ref(v___y_1337_);
lean_inc(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc_ref(v___y_1334_);
v___x_1372_ = lean_apply_13(v___y_1370_, v___x_1371_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, lean_box(0));
v___y_1347_ = v___x_1372_;
goto v___jp_1346_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_1459_ = _args[0];
lean_object* v___x_1460_ = _args[1];
lean_object* v___x_1461_ = _args[2];
lean_object* v___x_1462_ = _args[3];
lean_object* v___x_1463_ = _args[4];
lean_object* v_a_1464_ = _args[5];
lean_object* v_b_1465_ = _args[6];
lean_object* v___y_1466_ = _args[7];
lean_object* v___y_1467_ = _args[8];
lean_object* v___y_1468_ = _args[9];
lean_object* v___y_1469_ = _args[10];
lean_object* v___y_1470_ = _args[11];
lean_object* v___y_1471_ = _args[12];
lean_object* v___y_1472_ = _args[13];
lean_object* v___y_1473_ = _args[14];
lean_object* v___y_1474_ = _args[15];
lean_object* v___y_1475_ = _args[16];
lean_object* v___y_1476_ = _args[17];
lean_object* v___y_1477_ = _args[18];
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg(v_upperBound_1459_, v___x_1460_, v___x_1461_, v___x_1462_, v___x_1463_, v_a_1464_, v_b_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec_ref(v___x_1460_);
lean_dec(v_upperBound_1459_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4(lean_object* v___x_1479_, lean_object* v___x_1480_, lean_object* v___x_1481_, lean_object* v___x_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v___x_1495_; lean_object* v_hypotheses_1496_; lean_object* v___x_1497_; lean_object* v_newHyps_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1495_ = lean_st_ref_get(v___y_1484_);
v_hypotheses_1496_ = lean_ctor_get(v___x_1495_, 5);
lean_inc_ref(v_hypotheses_1496_);
lean_dec(v___x_1495_);
v___x_1497_ = lean_array_get_size(v_hypotheses_1496_);
v_newHyps_1498_ = lean_mk_empty_array_with_capacity(v___x_1497_);
v___x_1499_ = lean_box(0);
v___x_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
lean_ctor_set(v___x_1500_, 1, v_newHyps_1498_);
v___x_1501_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg(v___x_1497_, v_hypotheses_1496_, v___x_1479_, v___x_1480_, v___x_1481_, v___x_1482_, v___x_1500_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec_ref(v_hypotheses_1496_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1533_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1533_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1533_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v_fst_1506_; 
v_fst_1506_ = lean_ctor_get(v_a_1502_, 0);
if (lean_obj_tag(v_fst_1506_) == 0)
{
lean_object* v_snd_1507_; lean_object* v___x_1508_; lean_object* v_rewriteSimpCache_1509_; lean_object* v_rewriteDSimpCache_1510_; lean_object* v_acCache_1511_; lean_object* v_typeAnalysis_1512_; lean_object* v_target_1513_; uint8_t v_didChange_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1527_; 
v_snd_1507_ = lean_ctor_get(v_a_1502_, 1);
lean_inc(v_snd_1507_);
lean_dec(v_a_1502_);
v___x_1508_ = lean_st_ref_take(v___y_1484_);
v_rewriteSimpCache_1509_ = lean_ctor_get(v___x_1508_, 0);
v_rewriteDSimpCache_1510_ = lean_ctor_get(v___x_1508_, 1);
v_acCache_1511_ = lean_ctor_get(v___x_1508_, 2);
v_typeAnalysis_1512_ = lean_ctor_get(v___x_1508_, 3);
v_target_1513_ = lean_ctor_get(v___x_1508_, 4);
v_didChange_1514_ = lean_ctor_get_uint8(v___x_1508_, sizeof(void*)*6);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1527_ == 0)
{
lean_object* v_unused_1528_; 
v_unused_1528_ = lean_ctor_get(v___x_1508_, 5);
lean_dec(v_unused_1528_);
v___x_1516_ = v___x_1508_;
v_isShared_1517_ = v_isSharedCheck_1527_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_target_1513_);
lean_inc(v_typeAnalysis_1512_);
lean_inc(v_acCache_1511_);
lean_inc(v_rewriteDSimpCache_1510_);
lean_inc(v_rewriteSimpCache_1509_);
lean_dec(v___x_1508_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1527_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
lean_object* v___x_1519_; 
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 5, v_snd_1507_);
v___x_1519_ = v___x_1516_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_rewriteSimpCache_1509_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_rewriteDSimpCache_1510_);
lean_ctor_set(v_reuseFailAlloc_1526_, 2, v_acCache_1511_);
lean_ctor_set(v_reuseFailAlloc_1526_, 3, v_typeAnalysis_1512_);
lean_ctor_set(v_reuseFailAlloc_1526_, 4, v_target_1513_);
lean_ctor_set(v_reuseFailAlloc_1526_, 5, v_snd_1507_);
lean_ctor_set_uint8(v_reuseFailAlloc_1526_, sizeof(void*)*6, v_didChange_1514_);
v___x_1519_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1520_; uint8_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1524_; 
v___x_1520_ = lean_st_ref_set(v___y_1484_, v___x_1519_);
v___x_1521_ = 0;
v___x_1522_ = lean_box(v___x_1521_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1522_);
v___x_1524_ = v___x_1504_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v___x_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
else
{
lean_object* v_val_1529_; lean_object* v___x_1531_; 
lean_inc_ref(v_fst_1506_);
lean_dec(v_a_1502_);
v_val_1529_ = lean_ctor_get(v_fst_1506_, 0);
lean_inc(v_val_1529_);
lean_dec_ref_known(v_fst_1506_, 1);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v_val_1529_);
v___x_1531_ = v___x_1504_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_val_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
v_a_1534_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v___x_1501_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1501_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4___boxed(lean_object* v___x_1542_, lean_object* v___x_1543_, lean_object* v___x_1544_, lean_object* v___x_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4(v___x_1542_, v___x_1543_, v___x_1544_, v___x_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9_spec__11(size_t v_sz_1559_, size_t v_i_1560_, lean_object* v_bs_1561_){
_start:
{
uint8_t v___x_1562_; 
v___x_1562_ = lean_usize_dec_lt(v_i_1560_, v_sz_1559_);
if (v___x_1562_ == 0)
{
return v_bs_1561_;
}
else
{
lean_object* v_v_1563_; lean_object* v_msg_1564_; lean_object* v___x_1565_; lean_object* v_bs_x27_1566_; size_t v___x_1567_; size_t v___x_1568_; lean_object* v___x_1569_; 
v_v_1563_ = lean_array_uget_borrowed(v_bs_1561_, v_i_1560_);
v_msg_1564_ = lean_ctor_get(v_v_1563_, 1);
lean_inc_ref(v_msg_1564_);
v___x_1565_ = lean_unsigned_to_nat(0u);
v_bs_x27_1566_ = lean_array_uset(v_bs_1561_, v_i_1560_, v___x_1565_);
v___x_1567_ = ((size_t)1ULL);
v___x_1568_ = lean_usize_add(v_i_1560_, v___x_1567_);
v___x_1569_ = lean_array_uset(v_bs_x27_1566_, v_i_1560_, v_msg_1564_);
v_i_1560_ = v___x_1568_;
v_bs_1561_ = v___x_1569_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9_spec__11___boxed(lean_object* v_sz_1571_, lean_object* v_i_1572_, lean_object* v_bs_1573_){
_start:
{
size_t v_sz_boxed_1574_; size_t v_i_boxed_1575_; lean_object* v_res_1576_; 
v_sz_boxed_1574_ = lean_unbox_usize(v_sz_1571_);
lean_dec(v_sz_1571_);
v_i_boxed_1575_ = lean_unbox_usize(v_i_1572_);
lean_dec(v_i_1572_);
v_res_1576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9_spec__11(v_sz_boxed_1574_, v_i_boxed_1575_, v_bs_1573_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9___redArg(lean_object* v_oldTraces_1577_, lean_object* v_data_1578_, lean_object* v_ref_1579_, lean_object* v_msg_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_fileName_1586_; lean_object* v_fileMap_1587_; lean_object* v_options_1588_; lean_object* v_currRecDepth_1589_; lean_object* v_maxRecDepth_1590_; lean_object* v_ref_1591_; lean_object* v_currNamespace_1592_; lean_object* v_openDecls_1593_; lean_object* v_initHeartbeats_1594_; lean_object* v_maxHeartbeats_1595_; lean_object* v_quotContext_1596_; lean_object* v_currMacroScope_1597_; uint8_t v_diag_1598_; lean_object* v_cancelTk_x3f_1599_; uint8_t v_suppressElabErrors_1600_; lean_object* v_inheritedTraceOptions_1601_; lean_object* v___x_1602_; lean_object* v_traceState_1603_; lean_object* v_traces_1604_; lean_object* v_ref_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; size_t v_sz_1608_; size_t v___x_1609_; lean_object* v___x_1610_; lean_object* v_msg_1611_; lean_object* v___x_1612_; lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1650_; 
v_fileName_1586_ = lean_ctor_get(v___y_1583_, 0);
v_fileMap_1587_ = lean_ctor_get(v___y_1583_, 1);
v_options_1588_ = lean_ctor_get(v___y_1583_, 2);
v_currRecDepth_1589_ = lean_ctor_get(v___y_1583_, 3);
v_maxRecDepth_1590_ = lean_ctor_get(v___y_1583_, 4);
v_ref_1591_ = lean_ctor_get(v___y_1583_, 5);
v_currNamespace_1592_ = lean_ctor_get(v___y_1583_, 6);
v_openDecls_1593_ = lean_ctor_get(v___y_1583_, 7);
v_initHeartbeats_1594_ = lean_ctor_get(v___y_1583_, 8);
v_maxHeartbeats_1595_ = lean_ctor_get(v___y_1583_, 9);
v_quotContext_1596_ = lean_ctor_get(v___y_1583_, 10);
v_currMacroScope_1597_ = lean_ctor_get(v___y_1583_, 11);
v_diag_1598_ = lean_ctor_get_uint8(v___y_1583_, sizeof(void*)*14);
v_cancelTk_x3f_1599_ = lean_ctor_get(v___y_1583_, 12);
v_suppressElabErrors_1600_ = lean_ctor_get_uint8(v___y_1583_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1601_ = lean_ctor_get(v___y_1583_, 13);
v___x_1602_ = lean_st_ref_get(v___y_1584_);
v_traceState_1603_ = lean_ctor_get(v___x_1602_, 4);
lean_inc_ref(v_traceState_1603_);
lean_dec(v___x_1602_);
v_traces_1604_ = lean_ctor_get(v_traceState_1603_, 0);
lean_inc_ref(v_traces_1604_);
lean_dec_ref(v_traceState_1603_);
v_ref_1605_ = l_Lean_replaceRef(v_ref_1579_, v_ref_1591_);
lean_inc_ref(v_inheritedTraceOptions_1601_);
lean_inc(v_cancelTk_x3f_1599_);
lean_inc(v_currMacroScope_1597_);
lean_inc(v_quotContext_1596_);
lean_inc(v_maxHeartbeats_1595_);
lean_inc(v_initHeartbeats_1594_);
lean_inc(v_openDecls_1593_);
lean_inc(v_currNamespace_1592_);
lean_inc(v_maxRecDepth_1590_);
lean_inc(v_currRecDepth_1589_);
lean_inc_ref(v_options_1588_);
lean_inc_ref(v_fileMap_1587_);
lean_inc_ref(v_fileName_1586_);
v___x_1606_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1606_, 0, v_fileName_1586_);
lean_ctor_set(v___x_1606_, 1, v_fileMap_1587_);
lean_ctor_set(v___x_1606_, 2, v_options_1588_);
lean_ctor_set(v___x_1606_, 3, v_currRecDepth_1589_);
lean_ctor_set(v___x_1606_, 4, v_maxRecDepth_1590_);
lean_ctor_set(v___x_1606_, 5, v_ref_1605_);
lean_ctor_set(v___x_1606_, 6, v_currNamespace_1592_);
lean_ctor_set(v___x_1606_, 7, v_openDecls_1593_);
lean_ctor_set(v___x_1606_, 8, v_initHeartbeats_1594_);
lean_ctor_set(v___x_1606_, 9, v_maxHeartbeats_1595_);
lean_ctor_set(v___x_1606_, 10, v_quotContext_1596_);
lean_ctor_set(v___x_1606_, 11, v_currMacroScope_1597_);
lean_ctor_set(v___x_1606_, 12, v_cancelTk_x3f_1599_);
lean_ctor_set(v___x_1606_, 13, v_inheritedTraceOptions_1601_);
lean_ctor_set_uint8(v___x_1606_, sizeof(void*)*14, v_diag_1598_);
lean_ctor_set_uint8(v___x_1606_, sizeof(void*)*14 + 1, v_suppressElabErrors_1600_);
v___x_1607_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1604_);
lean_dec_ref(v_traces_1604_);
v_sz_1608_ = lean_array_size(v___x_1607_);
v___x_1609_ = ((size_t)0ULL);
v___x_1610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9_spec__11(v_sz_1608_, v___x_1609_, v___x_1607_);
v_msg_1611_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1611_, 0, v_data_1578_);
lean_ctor_set(v_msg_1611_, 1, v_msg_1580_);
lean_ctor_set(v_msg_1611_, 2, v___x_1610_);
v___x_1612_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(v_msg_1611_, v___y_1581_, v___y_1582_, v___x_1606_, v___y_1584_);
lean_dec_ref_known(v___x_1606_, 14);
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1615_ = v___x_1612_;
v_isShared_1616_ = v_isSharedCheck_1650_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1612_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1650_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1617_; lean_object* v_traceState_1618_; lean_object* v_env_1619_; lean_object* v_nextMacroScope_1620_; lean_object* v_ngen_1621_; lean_object* v_auxDeclNGen_1622_; lean_object* v_cache_1623_; lean_object* v_messages_1624_; lean_object* v_infoState_1625_; lean_object* v_snapshotTasks_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1649_; 
v___x_1617_ = lean_st_ref_take(v___y_1584_);
v_traceState_1618_ = lean_ctor_get(v___x_1617_, 4);
v_env_1619_ = lean_ctor_get(v___x_1617_, 0);
v_nextMacroScope_1620_ = lean_ctor_get(v___x_1617_, 1);
v_ngen_1621_ = lean_ctor_get(v___x_1617_, 2);
v_auxDeclNGen_1622_ = lean_ctor_get(v___x_1617_, 3);
v_cache_1623_ = lean_ctor_get(v___x_1617_, 5);
v_messages_1624_ = lean_ctor_get(v___x_1617_, 6);
v_infoState_1625_ = lean_ctor_get(v___x_1617_, 7);
v_snapshotTasks_1626_ = lean_ctor_get(v___x_1617_, 8);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1628_ = v___x_1617_;
v_isShared_1629_ = v_isSharedCheck_1649_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_snapshotTasks_1626_);
lean_inc(v_infoState_1625_);
lean_inc(v_messages_1624_);
lean_inc(v_cache_1623_);
lean_inc(v_traceState_1618_);
lean_inc(v_auxDeclNGen_1622_);
lean_inc(v_ngen_1621_);
lean_inc(v_nextMacroScope_1620_);
lean_inc(v_env_1619_);
lean_dec(v___x_1617_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1649_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
uint64_t v_tid_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1647_; 
v_tid_1630_ = lean_ctor_get_uint64(v_traceState_1618_, sizeof(void*)*1);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_traceState_1618_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; 
v_unused_1648_ = lean_ctor_get(v_traceState_1618_, 0);
lean_dec(v_unused_1648_);
v___x_1632_ = v_traceState_1618_;
v_isShared_1633_ = v_isSharedCheck_1647_;
goto v_resetjp_1631_;
}
else
{
lean_dec(v_traceState_1618_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1647_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1637_; 
v___x_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1634_, 0, v_ref_1579_);
lean_ctor_set(v___x_1634_, 1, v_a_1613_);
v___x_1635_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1577_, v___x_1634_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v___x_1635_);
v___x_1637_ = v___x_1632_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1635_);
lean_ctor_set_uint64(v_reuseFailAlloc_1646_, sizeof(void*)*1, v_tid_1630_);
v___x_1637_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1639_; 
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 4, v___x_1637_);
v___x_1639_ = v___x_1628_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_env_1619_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_nextMacroScope_1620_);
lean_ctor_set(v_reuseFailAlloc_1645_, 2, v_ngen_1621_);
lean_ctor_set(v_reuseFailAlloc_1645_, 3, v_auxDeclNGen_1622_);
lean_ctor_set(v_reuseFailAlloc_1645_, 4, v___x_1637_);
lean_ctor_set(v_reuseFailAlloc_1645_, 5, v_cache_1623_);
lean_ctor_set(v_reuseFailAlloc_1645_, 6, v_messages_1624_);
lean_ctor_set(v_reuseFailAlloc_1645_, 7, v_infoState_1625_);
lean_ctor_set(v_reuseFailAlloc_1645_, 8, v_snapshotTasks_1626_);
v___x_1639_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1640_ = lean_st_ref_set(v___y_1584_, v___x_1639_);
v___x_1641_ = lean_box(0);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 0, v___x_1641_);
v___x_1643_ = v___x_1615_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9___redArg___boxed(lean_object* v_oldTraces_1651_, lean_object* v_data_1652_, lean_object* v_ref_1653_, lean_object* v_msg_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9___redArg(v_oldTraces_1651_, v_data_1652_, v_ref_1653_, v_msg_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
return v_res_1660_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__11(lean_object* v_e_1661_){
_start:
{
if (lean_obj_tag(v_e_1661_) == 0)
{
uint8_t v___x_1662_; 
v___x_1662_ = 2;
return v___x_1662_;
}
else
{
uint8_t v___x_1663_; 
v___x_1663_ = 0;
return v___x_1663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__11___boxed(lean_object* v_e_1664_){
_start:
{
uint8_t v_res_1665_; lean_object* v_r_1666_; 
v_res_1665_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__11(v_e_1664_);
lean_dec_ref(v_e_1664_);
v_r_1666_ = lean_box(v_res_1665_);
return v_r_1666_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10___redArg(lean_object* v_x_1667_){
_start:
{
if (lean_obj_tag(v_x_1667_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
v_a_1669_ = lean_ctor_get(v_x_1667_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_x_1667_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v_x_1667_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v_x_1667_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set_tag(v___x_1671_, 1);
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
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
v_a_1677_ = lean_ctor_get(v_x_1667_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_x_1667_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v_x_1667_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v_x_1667_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
lean_ctor_set_tag(v___x_1679_, 0);
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10___redArg___boxed(lean_object* v_x_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10___redArg(v_x_1685_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12(lean_object* v_opts_1688_, lean_object* v_opt_1689_){
_start:
{
lean_object* v_name_1690_; lean_object* v_defValue_1691_; lean_object* v_map_1692_; lean_object* v___x_1693_; 
v_name_1690_ = lean_ctor_get(v_opt_1689_, 0);
v_defValue_1691_ = lean_ctor_get(v_opt_1689_, 1);
v_map_1692_ = lean_ctor_get(v_opts_1688_, 0);
v___x_1693_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1692_, v_name_1690_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_inc(v_defValue_1691_);
return v_defValue_1691_;
}
else
{
lean_object* v_val_1694_; 
v_val_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_val_1694_);
lean_dec_ref_known(v___x_1693_, 1);
if (lean_obj_tag(v_val_1694_) == 3)
{
lean_object* v_v_1695_; 
v_v_1695_ = lean_ctor_get(v_val_1694_, 0);
lean_inc(v_v_1695_);
lean_dec_ref_known(v_val_1694_, 1);
return v_v_1695_;
}
else
{
lean_dec(v_val_1694_);
lean_inc(v_defValue_1691_);
return v_defValue_1691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12___boxed(lean_object* v_opts_1696_, lean_object* v_opt_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12(v_opts_1696_, v_opt_1697_);
lean_dec_ref(v_opt_1697_);
lean_dec_ref(v_opts_1696_);
return v_res_1698_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__1(void){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__0));
v___x_1701_ = l_Lean_stringToMessageData(v___x_1700_);
return v___x_1701_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__2(void){
_start:
{
lean_object* v___x_1702_; double v___x_1703_; 
v___x_1702_ = lean_unsigned_to_nat(1000u);
v___x_1703_ = lean_float_of_nat(v___x_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7(lean_object* v_cls_1704_, uint8_t v_collapsed_1705_, lean_object* v_tag_1706_, lean_object* v_opts_1707_, uint8_t v_clsEnabled_1708_, lean_object* v_oldTraces_1709_, lean_object* v_msg_1710_, lean_object* v_resStartStop_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_fst_1724_; lean_object* v_snd_1725_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v_data_1729_; lean_object* v_fst_1732_; lean_object* v_snd_1733_; lean_object* v___x_1734_; uint8_t v___x_1735_; lean_object* v___y_1737_; lean_object* v_a_1738_; uint8_t v___y_1753_; double v___y_1784_; 
v_fst_1724_ = lean_ctor_get(v_resStartStop_1711_, 0);
lean_inc(v_fst_1724_);
v_snd_1725_ = lean_ctor_get(v_resStartStop_1711_, 1);
lean_inc(v_snd_1725_);
lean_dec_ref(v_resStartStop_1711_);
v_fst_1732_ = lean_ctor_get(v_snd_1725_, 0);
lean_inc(v_fst_1732_);
v_snd_1733_ = lean_ctor_get(v_snd_1725_, 1);
lean_inc(v_snd_1733_);
lean_dec(v_snd_1725_);
v___x_1734_ = l_Lean_trace_profiler;
v___x_1735_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(v_opts_1707_, v___x_1734_);
if (v___x_1735_ == 0)
{
v___y_1753_ = v___x_1735_;
goto v___jp_1752_;
}
else
{
lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1789_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1790_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(v_opts_1707_, v___x_1789_);
if (v___x_1790_ == 0)
{
lean_object* v___x_1791_; lean_object* v___x_1792_; double v___x_1793_; double v___x_1794_; double v___x_1795_; 
v___x_1791_ = l_Lean_trace_profiler_threshold;
v___x_1792_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12(v_opts_1707_, v___x_1791_);
v___x_1793_ = lean_float_of_nat(v___x_1792_);
v___x_1794_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__2);
v___x_1795_ = lean_float_div(v___x_1793_, v___x_1794_);
v___y_1784_ = v___x_1795_;
goto v___jp_1783_;
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; double v___x_1798_; 
v___x_1796_ = l_Lean_trace_profiler_threshold;
v___x_1797_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12(v_opts_1707_, v___x_1796_);
v___x_1798_ = lean_float_of_nat(v___x_1797_);
v___y_1784_ = v___x_1798_;
goto v___jp_1783_;
}
}
v___jp_1726_:
{
lean_object* v___x_1730_; 
lean_inc(v___y_1727_);
v___x_1730_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9___redArg(v_oldTraces_1709_, v_data_1729_, v___y_1727_, v___y_1728_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v___x_1731_; 
lean_dec_ref_known(v___x_1730_, 1);
v___x_1731_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10___redArg(v_fst_1724_);
return v___x_1731_;
}
else
{
lean_dec(v_fst_1724_);
return v___x_1730_;
}
}
v___jp_1736_:
{
uint8_t v_result_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; double v___x_1742_; lean_object* v_data_1743_; 
v_result_1739_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__11(v_fst_1724_);
v___x_1740_ = lean_box(v_result_1739_);
v___x_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1740_);
v___x_1742_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_1706_);
lean_inc_ref(v___x_1741_);
lean_inc(v_cls_1704_);
v_data_1743_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1743_, 0, v_cls_1704_);
lean_ctor_set(v_data_1743_, 1, v___x_1741_);
lean_ctor_set(v_data_1743_, 2, v_tag_1706_);
lean_ctor_set_float(v_data_1743_, sizeof(void*)*3, v___x_1742_);
lean_ctor_set_float(v_data_1743_, sizeof(void*)*3 + 8, v___x_1742_);
lean_ctor_set_uint8(v_data_1743_, sizeof(void*)*3 + 16, v_collapsed_1705_);
if (v___x_1735_ == 0)
{
lean_dec_ref_known(v___x_1741_, 1);
lean_dec(v_snd_1733_);
lean_dec(v_fst_1732_);
lean_dec_ref(v_tag_1706_);
lean_dec(v_cls_1704_);
v___y_1727_ = v___y_1737_;
v___y_1728_ = v_a_1738_;
v_data_1729_ = v_data_1743_;
goto v___jp_1726_;
}
else
{
lean_object* v_data_1744_; double v___x_1745_; double v___x_1746_; 
lean_dec_ref_known(v_data_1743_, 3);
v_data_1744_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1744_, 0, v_cls_1704_);
lean_ctor_set(v_data_1744_, 1, v___x_1741_);
lean_ctor_set(v_data_1744_, 2, v_tag_1706_);
v___x_1745_ = lean_unbox_float(v_fst_1732_);
lean_dec(v_fst_1732_);
lean_ctor_set_float(v_data_1744_, sizeof(void*)*3, v___x_1745_);
v___x_1746_ = lean_unbox_float(v_snd_1733_);
lean_dec(v_snd_1733_);
lean_ctor_set_float(v_data_1744_, sizeof(void*)*3 + 8, v___x_1746_);
lean_ctor_set_uint8(v_data_1744_, sizeof(void*)*3 + 16, v_collapsed_1705_);
v___y_1727_ = v___y_1737_;
v___y_1728_ = v_a_1738_;
v_data_1729_ = v_data_1744_;
goto v___jp_1726_;
}
}
v___jp_1747_:
{
lean_object* v_ref_1748_; lean_object* v___x_1749_; 
v_ref_1748_ = lean_ctor_get(v___y_1721_, 5);
lean_inc(v___y_1722_);
lean_inc_ref(v___y_1721_);
lean_inc(v___y_1720_);
lean_inc_ref(v___y_1719_);
lean_inc(v___y_1718_);
lean_inc_ref(v___y_1717_);
lean_inc(v___y_1716_);
lean_inc_ref(v___y_1715_);
lean_inc(v___y_1714_);
lean_inc(v___y_1713_);
lean_inc_ref(v___y_1712_);
lean_inc(v_fst_1724_);
v___x_1749_ = lean_apply_13(v_msg_1710_, v_fst_1724_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, lean_box(0));
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v___y_1737_ = v_ref_1748_;
v_a_1738_ = v_a_1750_;
goto v___jp_1736_;
}
else
{
lean_object* v___x_1751_; 
lean_dec_ref_known(v___x_1749_, 1);
v___x_1751_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__1);
v___y_1737_ = v_ref_1748_;
v_a_1738_ = v___x_1751_;
goto v___jp_1736_;
}
}
v___jp_1752_:
{
if (v_clsEnabled_1708_ == 0)
{
if (v___y_1753_ == 0)
{
lean_object* v___x_1754_; lean_object* v_traceState_1755_; lean_object* v_env_1756_; lean_object* v_nextMacroScope_1757_; lean_object* v_ngen_1758_; lean_object* v_auxDeclNGen_1759_; lean_object* v_cache_1760_; lean_object* v_messages_1761_; lean_object* v_infoState_1762_; lean_object* v_snapshotTasks_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1782_; 
lean_dec(v_snd_1733_);
lean_dec(v_fst_1732_);
lean_dec_ref(v_msg_1710_);
lean_dec_ref(v_tag_1706_);
lean_dec(v_cls_1704_);
v___x_1754_ = lean_st_ref_take(v___y_1722_);
v_traceState_1755_ = lean_ctor_get(v___x_1754_, 4);
v_env_1756_ = lean_ctor_get(v___x_1754_, 0);
v_nextMacroScope_1757_ = lean_ctor_get(v___x_1754_, 1);
v_ngen_1758_ = lean_ctor_get(v___x_1754_, 2);
v_auxDeclNGen_1759_ = lean_ctor_get(v___x_1754_, 3);
v_cache_1760_ = lean_ctor_get(v___x_1754_, 5);
v_messages_1761_ = lean_ctor_get(v___x_1754_, 6);
v_infoState_1762_ = lean_ctor_get(v___x_1754_, 7);
v_snapshotTasks_1763_ = lean_ctor_get(v___x_1754_, 8);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1765_ = v___x_1754_;
v_isShared_1766_ = v_isSharedCheck_1782_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_snapshotTasks_1763_);
lean_inc(v_infoState_1762_);
lean_inc(v_messages_1761_);
lean_inc(v_cache_1760_);
lean_inc(v_traceState_1755_);
lean_inc(v_auxDeclNGen_1759_);
lean_inc(v_ngen_1758_);
lean_inc(v_nextMacroScope_1757_);
lean_inc(v_env_1756_);
lean_dec(v___x_1754_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1782_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
uint64_t v_tid_1767_; lean_object* v_traces_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1781_; 
v_tid_1767_ = lean_ctor_get_uint64(v_traceState_1755_, sizeof(void*)*1);
v_traces_1768_ = lean_ctor_get(v_traceState_1755_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v_traceState_1755_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1770_ = v_traceState_1755_;
v_isShared_1771_ = v_isSharedCheck_1781_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_traces_1768_);
lean_dec(v_traceState_1755_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1781_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1772_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1709_, v_traces_1768_);
lean_dec_ref(v_traces_1768_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1772_);
v___x_1774_ = v___x_1770_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1772_);
lean_ctor_set_uint64(v_reuseFailAlloc_1780_, sizeof(void*)*1, v_tid_1767_);
v___x_1774_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1776_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 4, v___x_1774_);
v___x_1776_ = v___x_1765_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_env_1756_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_nextMacroScope_1757_);
lean_ctor_set(v_reuseFailAlloc_1779_, 2, v_ngen_1758_);
lean_ctor_set(v_reuseFailAlloc_1779_, 3, v_auxDeclNGen_1759_);
lean_ctor_set(v_reuseFailAlloc_1779_, 4, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1779_, 5, v_cache_1760_);
lean_ctor_set(v_reuseFailAlloc_1779_, 6, v_messages_1761_);
lean_ctor_set(v_reuseFailAlloc_1779_, 7, v_infoState_1762_);
lean_ctor_set(v_reuseFailAlloc_1779_, 8, v_snapshotTasks_1763_);
v___x_1776_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = lean_st_ref_set(v___y_1722_, v___x_1776_);
v___x_1778_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10___redArg(v_fst_1724_);
return v___x_1778_;
}
}
}
}
}
else
{
goto v___jp_1747_;
}
}
else
{
goto v___jp_1747_;
}
}
v___jp_1783_:
{
double v___x_1785_; double v___x_1786_; double v___x_1787_; uint8_t v___x_1788_; 
v___x_1785_ = lean_unbox_float(v_snd_1733_);
v___x_1786_ = lean_unbox_float(v_fst_1732_);
v___x_1787_ = lean_float_sub(v___x_1785_, v___x_1786_);
v___x_1788_ = lean_float_decLt(v___y_1784_, v___x_1787_);
v___y_1753_ = v___x_1788_;
goto v___jp_1752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___boxed(lean_object** _args){
lean_object* v_cls_1799_ = _args[0];
lean_object* v_collapsed_1800_ = _args[1];
lean_object* v_tag_1801_ = _args[2];
lean_object* v_opts_1802_ = _args[3];
lean_object* v_clsEnabled_1803_ = _args[4];
lean_object* v_oldTraces_1804_ = _args[5];
lean_object* v_msg_1805_ = _args[6];
lean_object* v_resStartStop_1806_ = _args[7];
lean_object* v___y_1807_ = _args[8];
lean_object* v___y_1808_ = _args[9];
lean_object* v___y_1809_ = _args[10];
lean_object* v___y_1810_ = _args[11];
lean_object* v___y_1811_ = _args[12];
lean_object* v___y_1812_ = _args[13];
lean_object* v___y_1813_ = _args[14];
lean_object* v___y_1814_ = _args[15];
lean_object* v___y_1815_ = _args[16];
lean_object* v___y_1816_ = _args[17];
lean_object* v___y_1817_ = _args[18];
lean_object* v___y_1818_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_1819_; uint8_t v_clsEnabled_boxed_1820_; lean_object* v_res_1821_; 
v_collapsed_boxed_1819_ = lean_unbox(v_collapsed_1800_);
v_clsEnabled_boxed_1820_ = lean_unbox(v_clsEnabled_1803_);
v_res_1821_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7(v_cls_1799_, v_collapsed_boxed_1819_, v_tag_1801_, v_opts_1802_, v_clsEnabled_boxed_1820_, v_oldTraces_1804_, v_msg_1805_, v_resStartStop_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec_ref(v___y_1810_);
lean_dec(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec_ref(v_opts_1802_);
return v_res_1821_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___closed__0));
v___x_1824_ = l_Lean_stringToMessageData(v___x_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4(lean_object* v_as_1825_, size_t v_sz_1826_, size_t v_i_1827_, lean_object* v_b_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_a_1842_; uint8_t v___x_1846_; 
v___x_1846_ = lean_usize_dec_lt(v_i_1827_, v_sz_1826_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_b_1828_);
return v___x_1847_;
}
else
{
lean_object* v_a_1848_; lean_object* v_options_1849_; lean_object* v_fst_1850_; lean_object* v_snd_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1871_; 
v_a_1848_ = lean_array_uget(v_as_1825_, v_i_1827_);
v_options_1849_ = lean_ctor_get(v___y_1838_, 2);
v_fst_1850_ = lean_ctor_get(v_a_1848_, 0);
v_snd_1851_ = lean_ctor_get(v_a_1848_, 1);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_a_1848_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1853_ = v_a_1848_;
v_isShared_1854_ = v_isSharedCheck_1871_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_snd_1851_);
lean_inc(v_fst_1850_);
lean_dec(v_a_1848_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1871_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v_inheritedTraceOptions_1855_; uint8_t v_hasTrace_1856_; lean_object* v___x_1857_; 
v_inheritedTraceOptions_1855_ = lean_ctor_get(v___y_1838_, 13);
v_hasTrace_1856_ = lean_ctor_get_uint8(v_options_1849_, sizeof(void*)*1);
v___x_1857_ = lean_box(0);
if (v_hasTrace_1856_ == 0)
{
lean_del_object(v___x_1853_);
lean_dec(v_snd_1851_);
lean_dec(v_fst_1850_);
v_a_1842_ = v___x_1857_;
goto v___jp_1841_;
}
else
{
lean_object* v___x_1858_; lean_object* v___x_1859_; uint8_t v___x_1860_; 
v___x_1858_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__9));
v___x_1859_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12);
v___x_1860_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1855_, v_options_1849_, v___x_1859_);
if (v___x_1860_ == 0)
{
lean_del_object(v___x_1853_);
lean_dec(v_snd_1851_);
lean_dec(v_fst_1850_);
v_a_1842_ = v___x_1857_;
goto v___jp_1841_;
}
else
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1861_ = l_Lean_MessageData_ofName(v_fst_1850_);
v___x_1862_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___closed__1);
if (v_isShared_1854_ == 0)
{
lean_ctor_set_tag(v___x_1853_, 7);
lean_ctor_set(v___x_1853_, 1, v___x_1862_);
lean_ctor_set(v___x_1853_, 0, v___x_1861_);
v___x_1864_ = v___x_1853_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1865_ = l_Nat_reprFast(v_snd_1851_);
v___x_1866_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
v___x_1867_ = l_Lean_MessageData_ofFormat(v___x_1866_);
v___x_1868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1864_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v___x_1869_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v___x_1858_, v___x_1868_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_dec_ref_known(v___x_1869_, 1);
v_a_1842_ = v___x_1857_;
goto v___jp_1841_;
}
else
{
return v___x_1869_;
}
}
}
}
}
}
v___jp_1841_:
{
size_t v___x_1843_; size_t v___x_1844_; 
v___x_1843_ = ((size_t)1ULL);
v___x_1844_ = lean_usize_add(v_i_1827_, v___x_1843_);
v_i_1827_ = v___x_1844_;
v_b_1828_ = v_a_1842_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___boxed(lean_object* v_as_1872_, lean_object* v_sz_1873_, lean_object* v_i_1874_, lean_object* v_b_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
size_t v_sz_boxed_1888_; size_t v_i_boxed_1889_; lean_object* v_res_1890_; 
v_sz_boxed_1888_ = lean_unbox_usize(v_sz_1873_);
lean_dec(v_sz_1873_);
v_i_boxed_1889_ = lean_unbox_usize(v_i_1874_);
lean_dec(v_i_1874_);
v_res_1890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4(v_as_1872_, v_sz_boxed_1888_, v_i_boxed_1889_, v_b_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_);
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
lean_dec_ref(v_as_1872_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9(lean_object* v_x_1891_, lean_object* v_x_1892_){
_start:
{
if (lean_obj_tag(v_x_1892_) == 0)
{
return v_x_1891_;
}
else
{
lean_object* v_key_1893_; lean_object* v_value_1894_; lean_object* v_tail_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v_key_1893_ = lean_ctor_get(v_x_1892_, 0);
v_value_1894_ = lean_ctor_get(v_x_1892_, 1);
v_tail_1895_ = lean_ctor_get(v_x_1892_, 2);
lean_inc(v_value_1894_);
lean_inc(v_key_1893_);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v_key_1893_);
lean_ctor_set(v___x_1896_, 1, v_value_1894_);
v___x_1897_ = lean_array_push(v_x_1891_, v___x_1896_);
v_x_1891_ = v___x_1897_;
v_x_1892_ = v_tail_1895_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9___boxed(lean_object* v_x_1899_, lean_object* v_x_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9(v_x_1899_, v_x_1900_);
lean_dec(v_x_1900_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__10(lean_object* v_as_1902_, size_t v_i_1903_, size_t v_stop_1904_, lean_object* v_b_1905_){
_start:
{
uint8_t v___x_1906_; 
v___x_1906_ = lean_usize_dec_eq(v_i_1903_, v_stop_1904_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; lean_object* v___x_1908_; size_t v___x_1909_; size_t v___x_1910_; 
v___x_1907_ = lean_array_uget_borrowed(v_as_1902_, v_i_1903_);
v___x_1908_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9(v_b_1905_, v___x_1907_);
v___x_1909_ = ((size_t)1ULL);
v___x_1910_ = lean_usize_add(v_i_1903_, v___x_1909_);
v_i_1903_ = v___x_1910_;
v_b_1905_ = v___x_1908_;
goto _start;
}
else
{
return v_b_1905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__10___boxed(lean_object* v_as_1912_, lean_object* v_i_1913_, lean_object* v_stop_1914_, lean_object* v_b_1915_){
_start:
{
size_t v_i_boxed_1916_; size_t v_stop_boxed_1917_; lean_object* v_res_1918_; 
v_i_boxed_1916_ = lean_unbox_usize(v_i_1913_);
lean_dec(v_i_1913_);
v_stop_boxed_1917_ = lean_unbox_usize(v_stop_1914_);
lean_dec(v_stop_1914_);
v_res_1918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__10(v_as_1912_, v_i_boxed_1916_, v_stop_boxed_1917_, v_b_1915_);
lean_dec_ref(v_as_1912_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8_spec__14___redArg(lean_object* v_hi_1919_, lean_object* v_pivot_1920_, lean_object* v_as_1921_, lean_object* v_i_1922_, lean_object* v_k_1923_){
_start:
{
uint8_t v___x_1924_; 
v___x_1924_ = lean_nat_dec_lt(v_k_1923_, v_hi_1919_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1926_; 
lean_dec(v_k_1923_);
v___x_1925_ = lean_array_fswap(v_as_1921_, v_i_1922_, v_hi_1919_);
v___x_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1926_, 0, v_i_1922_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
return v___x_1926_;
}
else
{
lean_object* v_snd_1927_; lean_object* v___x_1928_; lean_object* v_snd_1929_; uint8_t v___x_1930_; 
v_snd_1927_ = lean_ctor_get(v_pivot_1920_, 1);
v___x_1928_ = lean_array_fget_borrowed(v_as_1921_, v_k_1923_);
v_snd_1929_ = lean_ctor_get(v___x_1928_, 1);
v___x_1930_ = lean_nat_dec_lt(v_snd_1927_, v_snd_1929_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = lean_unsigned_to_nat(1u);
v___x_1932_ = lean_nat_add(v_k_1923_, v___x_1931_);
lean_dec(v_k_1923_);
v_k_1923_ = v___x_1932_;
goto _start;
}
else
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1934_ = lean_array_fswap(v_as_1921_, v_i_1922_, v_k_1923_);
v___x_1935_ = lean_unsigned_to_nat(1u);
v___x_1936_ = lean_nat_add(v_i_1922_, v___x_1935_);
lean_dec(v_i_1922_);
v___x_1937_ = lean_nat_add(v_k_1923_, v___x_1935_);
lean_dec(v_k_1923_);
v_as_1921_ = v___x_1934_;
v_i_1922_ = v___x_1936_;
v_k_1923_ = v___x_1937_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8_spec__14___redArg___boxed(lean_object* v_hi_1939_, lean_object* v_pivot_1940_, lean_object* v_as_1941_, lean_object* v_i_1942_, lean_object* v_k_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8_spec__14___redArg(v_hi_1939_, v_pivot_1940_, v_as_1941_, v_i_1942_, v_k_1943_);
lean_dec_ref(v_pivot_1940_);
lean_dec(v_hi_1939_);
return v_res_1944_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg___lam__0(lean_object* v_a_1945_, lean_object* v_b_1946_){
_start:
{
lean_object* v_snd_1947_; lean_object* v_snd_1948_; uint8_t v___x_1949_; 
v_snd_1947_ = lean_ctor_get(v_b_1946_, 1);
v_snd_1948_ = lean_ctor_get(v_a_1945_, 1);
v___x_1949_ = lean_nat_dec_lt(v_snd_1947_, v_snd_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg___lam__0___boxed(lean_object* v_a_1950_, lean_object* v_b_1951_){
_start:
{
uint8_t v_res_1952_; lean_object* v_r_1953_; 
v_res_1952_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg___lam__0(v_a_1950_, v_b_1951_);
lean_dec_ref(v_b_1951_);
lean_dec_ref(v_a_1950_);
v_r_1953_ = lean_box(v_res_1952_);
return v_r_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg(lean_object* v_n_1954_, lean_object* v_as_1955_, lean_object* v_lo_1956_, lean_object* v_hi_1957_){
_start:
{
lean_object* v___y_1959_; uint8_t v___x_1969_; 
v___x_1969_ = lean_nat_dec_lt(v_lo_1956_, v_hi_1957_);
if (v___x_1969_ == 0)
{
lean_dec(v_lo_1956_);
return v_as_1955_;
}
else
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v_mid_1972_; lean_object* v___y_1974_; lean_object* v___y_1980_; lean_object* v___x_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v___x_1970_ = lean_nat_add(v_lo_1956_, v_hi_1957_);
v___x_1971_ = lean_unsigned_to_nat(1u);
v_mid_1972_ = lean_nat_shiftr(v___x_1970_, v___x_1971_);
lean_dec(v___x_1970_);
v___x_1985_ = lean_array_fget_borrowed(v_as_1955_, v_mid_1972_);
v___x_1986_ = lean_array_fget_borrowed(v_as_1955_, v_lo_1956_);
v___x_1987_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg___lam__0(v___x_1985_, v___x_1986_);
if (v___x_1987_ == 0)
{
v___y_1980_ = v_as_1955_;
goto v___jp_1979_;
}
else
{
lean_object* v___x_1988_; 
v___x_1988_ = lean_array_fswap(v_as_1955_, v_lo_1956_, v_mid_1972_);
v___y_1980_ = v___x_1988_;
goto v___jp_1979_;
}
v___jp_1973_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1975_ = lean_array_fget_borrowed(v___y_1974_, v_mid_1972_);
v___x_1976_ = lean_array_fget_borrowed(v___y_1974_, v_hi_1957_);
v___x_1977_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg___lam__0(v___x_1975_, v___x_1976_);
if (v___x_1977_ == 0)
{
lean_dec(v_mid_1972_);
v___y_1959_ = v___y_1974_;
goto v___jp_1958_;
}
else
{
lean_object* v___x_1978_; 
v___x_1978_ = lean_array_fswap(v___y_1974_, v_mid_1972_, v_hi_1957_);
lean_dec(v_mid_1972_);
v___y_1959_ = v___x_1978_;
goto v___jp_1958_;
}
}
v___jp_1979_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1981_ = lean_array_fget_borrowed(v___y_1980_, v_hi_1957_);
v___x_1982_ = lean_array_fget_borrowed(v___y_1980_, v_lo_1956_);
v___x_1983_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg___lam__0(v___x_1981_, v___x_1982_);
if (v___x_1983_ == 0)
{
v___y_1974_ = v___y_1980_;
goto v___jp_1973_;
}
else
{
lean_object* v___x_1984_; 
v___x_1984_ = lean_array_fswap(v___y_1980_, v_lo_1956_, v_hi_1957_);
v___y_1974_ = v___x_1984_;
goto v___jp_1973_;
}
}
}
v___jp_1958_:
{
lean_object* v_pivot_1960_; lean_object* v___x_1961_; lean_object* v_fst_1962_; lean_object* v_snd_1963_; uint8_t v___x_1964_; 
v_pivot_1960_ = lean_array_fget(v___y_1959_, v_hi_1957_);
lean_inc_n(v_lo_1956_, 2);
v___x_1961_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8_spec__14___redArg(v_hi_1957_, v_pivot_1960_, v___y_1959_, v_lo_1956_, v_lo_1956_);
lean_dec(v_pivot_1960_);
v_fst_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_fst_1962_);
v_snd_1963_ = lean_ctor_get(v___x_1961_, 1);
lean_inc(v_snd_1963_);
lean_dec_ref(v___x_1961_);
v___x_1964_ = lean_nat_dec_le(v_hi_1957_, v_fst_1962_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1965_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg(v_n_1954_, v_snd_1963_, v_lo_1956_, v_fst_1962_);
v___x_1966_ = lean_unsigned_to_nat(1u);
v___x_1967_ = lean_nat_add(v_fst_1962_, v___x_1966_);
lean_dec(v_fst_1962_);
v_as_1955_ = v___x_1965_;
v_lo_1956_ = v___x_1967_;
goto _start;
}
else
{
lean_dec(v_fst_1962_);
lean_dec(v_lo_1956_);
return v_snd_1963_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg___boxed(lean_object* v_n_1989_, lean_object* v_as_1990_, lean_object* v_lo_1991_, lean_object* v_hi_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg(v_n_1989_, v_as_1990_, v_lo_1991_, v_hi_1992_);
lean_dec(v_hi_1992_);
lean_dec(v_n_1989_);
return v_res_1993_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__0(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1994_ = lean_box(0);
v___x_1995_ = lean_unsigned_to_nat(16u);
v___x_1996_ = lean_mk_array(v___x_1995_, v___x_1994_);
return v___x_1996_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1997_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__0);
v___x_1998_ = lean_unsigned_to_nat(0u);
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
lean_ctor_set(v___x_1999_, 1, v___x_1997_);
return v___x_1999_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__2(void){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__1);
v___x_2001_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
lean_ctor_set(v___x_2001_, 2, v___x_2000_);
lean_ctor_set(v___x_2001_, 3, v___x_2000_);
return v___x_2001_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__5(void){
_start:
{
lean_object* v___x_2006_; double v___x_2007_; 
v___x_2006_ = lean_unsigned_to_nat(1000000000u);
v___x_2007_ = lean_float_of_nat(v___x_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5(lean_object* v___x_2008_, lean_object* v___f_2009_, lean_object* v___f_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(v___x_2008_, v___y_2021_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v_config_2028_; lean_object* v_maxSteps_2029_; lean_object* v___x_2030_; lean_object* v_target_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___f_2036_; lean_object* v___f_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; lean_object* v___x_2040_; lean_object* v___f_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
v___x_2025_ = lean_unsigned_to_nat(0u);
v___x_2026_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__2);
v___x_2027_ = lean_st_mk_ref(v___x_2026_);
v_config_2028_ = lean_ctor_get(v___y_2011_, 0);
v_maxSteps_2029_ = lean_ctor_get(v_config_2028_, 1);
v___x_2030_ = lean_st_ref_get(v___y_2012_);
v_target_2031_ = lean_ctor_get(v___x_2030_, 4);
lean_inc_ref(v_target_2031_);
lean_dec(v___x_2030_);
v___x_2032_ = lean_unsigned_to_nat(2u);
lean_inc_n(v_maxSteps_2029_, 2);
v___x_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2033_, 0, v_maxSteps_2029_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v___x_2034_ = lean_unsigned_to_nat(255u);
v___x_2035_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__4));
lean_inc(v___x_2027_);
v___f_2036_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2___boxed), 15, 3);
lean_closure_set(v___f_2036_, 0, v___x_2027_);
lean_closure_set(v___f_2036_, 1, v_a_2024_);
lean_closure_set(v___f_2036_, 2, v___x_2035_);
v___f_2037_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3___boxed), 13, 2);
lean_closure_set(v___f_2037_, 0, v___x_2034_);
lean_closure_set(v___f_2037_, 1, v___f_2036_);
v___x_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___f_2009_);
lean_ctor_set(v___x_2038_, 1, v___f_2037_);
v___x_2039_ = 1;
v___x_2040_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2040_, 0, v_maxSteps_2029_);
lean_ctor_set_uint8(v___x_2040_, sizeof(void*)*1, v___x_2039_);
v___f_2041_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4___boxed), 16, 4);
lean_closure_set(v___f_2041_, 0, v___x_2040_);
lean_closure_set(v___f_2041_, 1, v___x_2038_);
lean_closure_set(v___f_2041_, 2, v___x_2033_);
lean_closure_set(v___f_2041_, 3, v___x_2025_);
v___x_2042_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_2031_);
lean_dec_ref(v_target_2031_);
v___x_2043_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg(v___x_2042_, v___f_2041_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___y_2046_; lean_object* v_options_2063_; uint8_t v_hasTrace_2064_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
v_options_2063_ = lean_ctor_get(v___y_2020_, 2);
v_hasTrace_2064_ = lean_ctor_get_uint8(v_options_2063_, sizeof(void*)*1);
if (v_hasTrace_2064_ == 0)
{
lean_dec(v_a_2044_);
lean_dec(v___x_2027_);
lean_dec_ref(v___f_2010_);
return v___x_2043_;
}
else
{
lean_object* v_inheritedTraceOptions_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; lean_object* v_a_2073_; lean_object* v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v_a_2089_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v_a_2095_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v_a_2108_; 
v_inheritedTraceOptions_2065_ = lean_ctor_get(v___y_2020_, 13);
v___x_2066_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__9));
v___x_2067_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12);
v___x_2068_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2065_, v_options_2063_, v___x_2067_);
if (v___x_2068_ == 0)
{
lean_dec(v_a_2044_);
lean_dec(v___x_2027_);
lean_dec_ref(v___f_2010_);
return v___x_2043_;
}
else
{
lean_object* v___x_2110_; lean_object* v___y_2112_; size_t v___y_2113_; size_t v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2144_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___y_2173_; lean_object* v_statistics_2179_; lean_object* v_size_2180_; lean_object* v_buckets_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
lean_dec_ref_known(v___x_2043_, 1);
v___x_2110_ = lean_st_ref_get(v___x_2027_);
lean_dec(v___x_2027_);
v_statistics_2179_ = lean_ctor_get(v___x_2110_, 3);
lean_inc_ref(v_statistics_2179_);
lean_dec(v___x_2110_);
v_size_2180_ = lean_ctor_get(v_statistics_2179_, 0);
lean_inc(v_size_2180_);
v_buckets_2181_ = lean_ctor_get(v_statistics_2179_, 1);
lean_inc_ref(v_buckets_2181_);
lean_dec_ref(v_statistics_2179_);
v___x_2182_ = lean_mk_empty_array_with_capacity(v_size_2180_);
lean_dec(v_size_2180_);
v___x_2183_ = lean_array_get_size(v_buckets_2181_);
v___x_2184_ = lean_nat_dec_lt(v___x_2025_, v___x_2183_);
if (v___x_2184_ == 0)
{
lean_dec_ref(v_buckets_2181_);
v___y_2173_ = v___x_2182_;
goto v___jp_2172_;
}
else
{
uint8_t v___x_2185_; 
v___x_2185_ = lean_nat_dec_le(v___x_2183_, v___x_2183_);
if (v___x_2185_ == 0)
{
if (v___x_2184_ == 0)
{
lean_dec_ref(v_buckets_2181_);
v___y_2173_ = v___x_2182_;
goto v___jp_2172_;
}
else
{
size_t v___x_2186_; size_t v___x_2187_; lean_object* v___x_2188_; 
v___x_2186_ = ((size_t)0ULL);
v___x_2187_ = lean_usize_of_nat(v___x_2183_);
v___x_2188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__10(v_buckets_2181_, v___x_2186_, v___x_2187_, v___x_2182_);
lean_dec_ref(v_buckets_2181_);
v___y_2173_ = v___x_2188_;
goto v___jp_2172_;
}
}
else
{
size_t v___x_2189_; size_t v___x_2190_; lean_object* v___x_2191_; 
v___x_2189_ = ((size_t)0ULL);
v___x_2190_ = lean_usize_of_nat(v___x_2183_);
v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__10(v_buckets_2181_, v___x_2189_, v___x_2190_, v___x_2182_);
lean_dec_ref(v_buckets_2181_);
v___y_2173_ = v___x_2191_;
goto v___jp_2172_;
}
}
v___jp_2111_:
{
lean_object* v___x_2117_; lean_object* v_a_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2117_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg(v___y_2021_);
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_a_2118_);
lean_dec_ref(v___x_2117_);
v___x_2119_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2120_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(v_options_2063_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = lean_io_mono_nanos_now();
v___x_2122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4(v___y_2115_, v___y_2114_, v___y_2113_, v___y_2116_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
lean_dec_ref(v___y_2115_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_dec_ref_known(v___x_2122_, 1);
v___y_2086_ = v___y_2112_;
v___y_2087_ = v___x_2121_;
v___y_2088_ = v_a_2118_;
v_a_2089_ = v___y_2116_;
goto v___jp_2085_;
}
else
{
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v___y_2086_ = v___y_2112_;
v___y_2087_ = v___x_2121_;
v___y_2088_ = v_a_2118_;
v_a_2089_ = v_a_2123_;
goto v___jp_2085_;
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
v_a_2124_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2122_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2122_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
lean_ctor_set_tag(v___x_2126_, 0);
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
v___y_2070_ = v___y_2112_;
v___y_2071_ = v___x_2121_;
v___y_2072_ = v_a_2118_;
v_a_2073_ = v___x_2129_;
goto v___jp_2069_;
}
}
}
}
}
else
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = lean_io_get_num_heartbeats();
v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4(v___y_2115_, v___y_2114_, v___y_2113_, v___y_2116_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
lean_dec_ref(v___y_2115_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_dec_ref_known(v___x_2133_, 1);
v___y_2105_ = v___y_2112_;
v___y_2106_ = v___x_2132_;
v___y_2107_ = v_a_2118_;
v_a_2108_ = v___y_2116_;
goto v___jp_2104_;
}
else
{
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2133_, 1);
v___y_2105_ = v___y_2112_;
v___y_2106_ = v___x_2132_;
v___y_2107_ = v_a_2118_;
v_a_2108_ = v_a_2134_;
goto v___jp_2104_;
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
v_a_2135_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2133_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2133_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
lean_ctor_set_tag(v___x_2137_, 0);
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
v___y_2092_ = v___y_2112_;
v___y_2093_ = v___x_2132_;
v___y_2094_ = v_a_2118_;
v_a_2095_ = v___x_2140_;
goto v___jp_2091_;
}
}
}
}
}
}
v___jp_2143_:
{
lean_object* v___x_2145_; size_t v_sz_2146_; size_t v___x_2147_; lean_object* v___x_2148_; 
v___x_2145_ = lean_box(0);
v_sz_2146_ = lean_array_size(v___y_2144_);
v___x_2147_ = ((size_t)0ULL);
v___x_2148_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1));
if (v___x_2068_ == 0)
{
lean_object* v___x_2149_; uint8_t v___x_2150_; 
v___x_2149_ = l_Lean_trace_profiler;
v___x_2150_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(v_options_2063_, v___x_2149_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; 
lean_dec_ref(v___f_2010_);
v___x_2151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4(v___y_2144_, v_sz_2146_, v___x_2147_, v___x_2145_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
lean_dec_ref(v___y_2144_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2158_ == 0)
{
lean_object* v_unused_2159_; 
v_unused_2159_ = lean_ctor_get(v___x_2151_, 0);
lean_dec(v_unused_2159_);
v___x_2153_ = v___x_2151_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_dec(v___x_2151_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 0, v_a_2044_);
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2044_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
else
{
v___y_2046_ = v___x_2151_;
goto v___jp_2045_;
}
}
else
{
v___y_2112_ = v___x_2148_;
v___y_2113_ = v___x_2147_;
v___y_2114_ = v_sz_2146_;
v___y_2115_ = v___y_2144_;
v___y_2116_ = v___x_2145_;
goto v___jp_2111_;
}
}
else
{
v___y_2112_ = v___x_2148_;
v___y_2113_ = v___x_2147_;
v___y_2114_ = v_sz_2146_;
v___y_2115_ = v___y_2144_;
v___y_2116_ = v___x_2145_;
goto v___jp_2111_;
}
}
v___jp_2160_:
{
lean_object* v___x_2165_; 
v___x_2165_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg(v___y_2163_, v___y_2162_, v___y_2161_, v___y_2164_);
lean_dec(v___y_2164_);
lean_dec(v___y_2163_);
v___y_2144_ = v___x_2165_;
goto v___jp_2143_;
}
v___jp_2166_:
{
uint8_t v___x_2171_; 
v___x_2171_ = lean_nat_dec_le(v___y_2170_, v___y_2167_);
if (v___x_2171_ == 0)
{
lean_dec(v___y_2167_);
lean_inc(v___y_2170_);
v___y_2161_ = v___y_2170_;
v___y_2162_ = v___y_2168_;
v___y_2163_ = v___y_2169_;
v___y_2164_ = v___y_2170_;
goto v___jp_2160_;
}
else
{
v___y_2161_ = v___y_2170_;
v___y_2162_ = v___y_2168_;
v___y_2163_ = v___y_2169_;
v___y_2164_ = v___y_2167_;
goto v___jp_2160_;
}
}
v___jp_2172_:
{
lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2174_ = lean_array_get_size(v___y_2173_);
v___x_2175_ = lean_nat_dec_eq(v___x_2174_, v___x_2025_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2176_ = lean_unsigned_to_nat(1u);
v___x_2177_ = lean_nat_sub(v___x_2174_, v___x_2176_);
v___x_2178_ = lean_nat_dec_le(v___x_2025_, v___x_2177_);
if (v___x_2178_ == 0)
{
lean_inc(v___x_2177_);
v___y_2167_ = v___x_2177_;
v___y_2168_ = v___y_2173_;
v___y_2169_ = v___x_2174_;
v___y_2170_ = v___x_2177_;
goto v___jp_2166_;
}
else
{
v___y_2167_ = v___x_2177_;
v___y_2168_ = v___y_2173_;
v___y_2169_ = v___x_2174_;
v___y_2170_ = v___x_2025_;
goto v___jp_2166_;
}
}
else
{
v___y_2144_ = v___y_2173_;
goto v___jp_2143_;
}
}
}
v___jp_2069_:
{
lean_object* v___x_2074_; double v___x_2075_; double v___x_2076_; double v___x_2077_; double v___x_2078_; double v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2074_ = lean_io_mono_nanos_now();
v___x_2075_ = lean_float_of_nat(v___y_2071_);
v___x_2076_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__5);
v___x_2077_ = lean_float_div(v___x_2075_, v___x_2076_);
v___x_2078_ = lean_float_of_nat(v___x_2074_);
v___x_2079_ = lean_float_div(v___x_2078_, v___x_2076_);
v___x_2080_ = lean_box_float(v___x_2077_);
v___x_2081_ = lean_box_float(v___x_2079_);
v___x_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2080_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2083_, 0, v_a_2073_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
lean_inc_ref(v___y_2070_);
v___x_2084_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7(v___x_2066_, v___x_2039_, v___y_2070_, v_options_2063_, v___x_2068_, v___y_2072_, v___f_2010_, v___x_2083_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
v___y_2046_ = v___x_2084_;
goto v___jp_2045_;
}
v___jp_2085_:
{
lean_object* v___x_2090_; 
v___x_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2090_, 0, v_a_2089_);
v___y_2070_ = v___y_2086_;
v___y_2071_ = v___y_2087_;
v___y_2072_ = v___y_2088_;
v_a_2073_ = v___x_2090_;
goto v___jp_2069_;
}
v___jp_2091_:
{
lean_object* v___x_2096_; double v___x_2097_; double v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2096_ = lean_io_get_num_heartbeats();
v___x_2097_ = lean_float_of_nat(v___y_2093_);
v___x_2098_ = lean_float_of_nat(v___x_2096_);
v___x_2099_ = lean_box_float(v___x_2097_);
v___x_2100_ = lean_box_float(v___x_2098_);
v___x_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2099_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
v___x_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2102_, 0, v_a_2095_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
lean_inc_ref(v___y_2092_);
v___x_2103_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7(v___x_2066_, v___x_2039_, v___y_2092_, v_options_2063_, v___x_2068_, v___y_2094_, v___f_2010_, v___x_2102_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
v___y_2046_ = v___x_2103_;
goto v___jp_2045_;
}
v___jp_2104_:
{
lean_object* v___x_2109_; 
v___x_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2109_, 0, v_a_2108_);
v___y_2092_ = v___y_2105_;
v___y_2093_ = v___y_2106_;
v___y_2094_ = v___y_2107_;
v_a_2095_ = v___x_2109_;
goto v___jp_2091_;
}
}
v___jp_2045_:
{
if (lean_obj_tag(v___y_2046_) == 0)
{
lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
v_isSharedCheck_2053_ = !lean_is_exclusive(v___y_2046_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; 
v_unused_2054_ = lean_ctor_get(v___y_2046_, 0);
lean_dec(v_unused_2054_);
v___x_2048_ = v___y_2046_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_dec(v___y_2046_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v_a_2044_);
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2044_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec(v_a_2044_);
v_a_2055_ = lean_ctor_get(v___y_2046_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___y_2046_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___y_2046_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___y_2046_);
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
lean_dec(v___x_2027_);
lean_dec_ref(v___f_2010_);
return v___x_2043_;
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec_ref(v___f_2010_);
lean_dec_ref(v___f_2009_);
v_a_2192_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2023_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2023_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___boxed(lean_object* v___x_2200_, lean_object* v___f_2201_, lean_object* v___f_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5(v___x_2200_, v___f_2201_, v___f_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec_ref(v___x_2200_);
return v_res_2215_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4(void){
_start:
{
lean_object* v___f_2221_; lean_object* v___f_2222_; lean_object* v___x_2223_; lean_object* v___f_2224_; 
v___f_2221_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__0));
v___f_2222_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__1));
v___x_2223_ = l_Lean_Meta_Tactic_BVDecide_bvNormalizeExt;
v___f_2224_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___boxed), 15, 3);
lean_closure_set(v___f_2224_, 0, v___x_2223_);
lean_closure_set(v___f_2224_, 1, v___f_2222_);
lean_closure_set(v___f_2224_, 2, v___f_2221_);
return v___f_2224_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__5(void){
_start:
{
lean_object* v___f_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___f_2225_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4);
v___x_2226_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__3));
v___x_2227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
lean_ctor_set(v___x_2227_, 1, v___f_2225_);
return v___x_2227_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass(void){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__5);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0(lean_object* v_cls_2229_, lean_object* v_msg_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v___x_2243_; 
v___x_2243_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v_cls_2229_, v_msg_2230_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___boxed(lean_object* v_cls_2244_, lean_object* v_msg_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0(v_cls_2244_, v_msg_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1(lean_object* v_mvarId_2259_, lean_object* v_val_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v_mvarId_2259_, v_val_2260_, v___y_2269_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___boxed(lean_object* v_mvarId_2274_, lean_object* v_val_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1(v_mvarId_2274_, v_val_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2(lean_object* v_upperBound_2289_, lean_object* v___x_2290_, lean_object* v___x_2291_, lean_object* v___x_2292_, lean_object* v___x_2293_, lean_object* v_inst_2294_, lean_object* v_R_2295_, lean_object* v_a_2296_, lean_object* v_b_2297_, lean_object* v_c_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg(v_upperBound_2289_, v___x_2290_, v___x_2291_, v___x_2292_, v___x_2293_, v_a_2296_, v_b_2297_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_2312_ = _args[0];
lean_object* v___x_2313_ = _args[1];
lean_object* v___x_2314_ = _args[2];
lean_object* v___x_2315_ = _args[3];
lean_object* v___x_2316_ = _args[4];
lean_object* v_inst_2317_ = _args[5];
lean_object* v_R_2318_ = _args[6];
lean_object* v_a_2319_ = _args[7];
lean_object* v_b_2320_ = _args[8];
lean_object* v_c_2321_ = _args[9];
lean_object* v___y_2322_ = _args[10];
lean_object* v___y_2323_ = _args[11];
lean_object* v___y_2324_ = _args[12];
lean_object* v___y_2325_ = _args[13];
lean_object* v___y_2326_ = _args[14];
lean_object* v___y_2327_ = _args[15];
lean_object* v___y_2328_ = _args[16];
lean_object* v___y_2329_ = _args[17];
lean_object* v___y_2330_ = _args[18];
lean_object* v___y_2331_ = _args[19];
lean_object* v___y_2332_ = _args[20];
lean_object* v___y_2333_ = _args[21];
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2(v_upperBound_2312_, v___x_2313_, v___x_2314_, v___x_2315_, v___x_2316_, v_inst_2317_, v_R_2318_, v_a_2319_, v_b_2320_, v_c_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec_ref(v___x_2313_);
lean_dec(v_upperBound_2312_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10(lean_object* v_00_u03b1_2335_, lean_object* v_x_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10___redArg(v_x_2336_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2350_, lean_object* v_x_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10(v_00_u03b1_2350_, v_x_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8(lean_object* v_n_2365_, lean_object* v_as_2366_, lean_object* v_lo_2367_, lean_object* v_hi_2368_, lean_object* v_w_2369_, lean_object* v_hlo_2370_, lean_object* v_hhi_2371_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg(v_n_2365_, v_as_2366_, v_lo_2367_, v_hi_2368_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___boxed(lean_object* v_n_2373_, lean_object* v_as_2374_, lean_object* v_lo_2375_, lean_object* v_hi_2376_, lean_object* v_w_2377_, lean_object* v_hlo_2378_, lean_object* v_hhi_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8(v_n_2373_, v_as_2374_, v_lo_2375_, v_hi_2376_, v_w_2377_, v_hlo_2378_, v_hhi_2379_);
lean_dec(v_hi_2376_);
lean_dec(v_n_2373_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2(lean_object* v_00_u03b2_2381_, lean_object* v_x_2382_, lean_object* v_x_2383_, lean_object* v_x_2384_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2___redArg(v_x_2382_, v_x_2383_, v_x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9(lean_object* v_oldTraces_2386_, lean_object* v_data_2387_, lean_object* v_ref_2388_, lean_object* v_msg_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9___redArg(v_oldTraces_2386_, v_data_2387_, v_ref_2388_, v_msg_2389_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9___boxed(lean_object* v_oldTraces_2403_, lean_object* v_data_2404_, lean_object* v_ref_2405_, lean_object* v_msg_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9(v_oldTraces_2403_, v_data_2404_, v_ref_2405_, v_msg_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8_spec__14(lean_object* v_n_2420_, lean_object* v_lo_2421_, lean_object* v_hi_2422_, lean_object* v_hhi_2423_, lean_object* v_pivot_2424_, lean_object* v_as_2425_, lean_object* v_i_2426_, lean_object* v_k_2427_, lean_object* v_ilo_2428_, lean_object* v_ik_2429_, lean_object* v_w_2430_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8_spec__14___redArg(v_hi_2422_, v_pivot_2424_, v_as_2425_, v_i_2426_, v_k_2427_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8_spec__14___boxed(lean_object* v_n_2432_, lean_object* v_lo_2433_, lean_object* v_hi_2434_, lean_object* v_hhi_2435_, lean_object* v_pivot_2436_, lean_object* v_as_2437_, lean_object* v_i_2438_, lean_object* v_k_2439_, lean_object* v_ilo_2440_, lean_object* v_ik_2441_, lean_object* v_w_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8_spec__14(v_n_2432_, v_lo_2433_, v_hi_2434_, v_hhi_2435_, v_pivot_2436_, v_as_2437_, v_i_2438_, v_k_2439_, v_ilo_2440_, v_ik_2441_, v_w_2442_);
lean_dec_ref(v_pivot_2436_);
lean_dec(v_hi_2434_);
lean_dec(v_lo_2433_);
lean_dec(v_n_2432_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2444_, lean_object* v_x_2445_, size_t v_x_2446_, size_t v_x_2447_, lean_object* v_x_2448_, lean_object* v_x_2449_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg(v_x_2445_, v_x_2446_, v_x_2447_, v_x_2448_, v_x_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2451_, lean_object* v_x_2452_, lean_object* v_x_2453_, lean_object* v_x_2454_, lean_object* v_x_2455_, lean_object* v_x_2456_){
_start:
{
size_t v_x_208992__boxed_2457_; size_t v_x_208993__boxed_2458_; lean_object* v_res_2459_; 
v_x_208992__boxed_2457_ = lean_unbox_usize(v_x_2453_);
lean_dec(v_x_2453_);
v_x_208993__boxed_2458_ = lean_unbox_usize(v_x_2454_);
lean_dec(v_x_2454_);
v_res_2459_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6(v_00_u03b2_2451_, v_x_2452_, v_x_208992__boxed_2457_, v_x_208993__boxed_2458_, v_x_2455_, v_x_2456_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__16(lean_object* v_00_u03b2_2460_, lean_object* v_n_2461_, lean_object* v_k_2462_, lean_object* v_v_2463_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__16___redArg(v_n_2461_, v_k_2462_, v_v_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__17(lean_object* v_00_u03b2_2465_, size_t v_depth_2466_, lean_object* v_keys_2467_, lean_object* v_vals_2468_, lean_object* v_heq_2469_, lean_object* v_i_2470_, lean_object* v_entries_2471_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__17___redArg(v_depth_2466_, v_keys_2467_, v_vals_2468_, v_i_2470_, v_entries_2471_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__17___boxed(lean_object* v_00_u03b2_2473_, lean_object* v_depth_2474_, lean_object* v_keys_2475_, lean_object* v_vals_2476_, lean_object* v_heq_2477_, lean_object* v_i_2478_, lean_object* v_entries_2479_){
_start:
{
size_t v_depth_boxed_2480_; lean_object* v_res_2481_; 
v_depth_boxed_2480_ = lean_unbox_usize(v_depth_2474_);
lean_dec(v_depth_2474_);
v_res_2481_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__17(v_00_u03b2_2473_, v_depth_boxed_2480_, v_keys_2475_, v_vals_2476_, v_heq_2477_, v_i_2478_, v_entries_2479_);
lean_dec_ref(v_vals_2476_);
lean_dec_ref(v_keys_2475_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__16_spec__19(lean_object* v_00_u03b2_2482_, lean_object* v_x_2483_, lean_object* v_x_2484_, lean_object* v_x_2485_, lean_object* v_x_2486_){
_start:
{
lean_object* v___x_2487_; 
v___x_2487_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__16_spec__19___redArg(v_x_2483_, v_x_2484_, v_x_2485_, v_x_2486_);
return v___x_2487_;
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

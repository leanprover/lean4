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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "rewriteRules simproc statistics:"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___boxed(lean_object**);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_15_; lean_object* v_rewriteSimpCache_16_; lean_object* v_rewriteDSimpCache_17_; lean_object* v_acCache_18_; lean_object* v_typeAnalysis_19_; lean_object* v_goal_20_; lean_object* v_hypotheses_21_; uint8_t v_didChange_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_65_; 
v___x_15_ = lean_st_ref_take(v_a_7_);
v_rewriteSimpCache_16_ = lean_ctor_get(v___x_15_, 0);
v_rewriteDSimpCache_17_ = lean_ctor_get(v___x_15_, 1);
v_acCache_18_ = lean_ctor_get(v___x_15_, 2);
v_typeAnalysis_19_ = lean_ctor_get(v___x_15_, 3);
v_goal_20_ = lean_ctor_get(v___x_15_, 4);
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
lean_inc(v_goal_20_);
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
lean_ctor_set(v_reuseFailAlloc_64_, 4, v_goal_20_);
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
lean_object* v_a_35_; lean_object* v_fst_36_; lean_object* v_snd_37_; lean_object* v___x_38_; lean_object* v_cache_39_; lean_object* v_rewriteSimpCache_40_; lean_object* v_acCache_41_; lean_object* v_typeAnalysis_42_; lean_object* v_goal_43_; lean_object* v_hypotheses_44_; uint8_t v_didChange_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_54_; 
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
v_goal_43_ = lean_ctor_get(v___x_38_, 4);
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
lean_inc(v_goal_43_);
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
lean_ctor_set(v_reuseFailAlloc_53_, 4, v_goal_43_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp(lean_object* v_methods_78_, lean_object* v_config_79_, lean_object* v_hyp_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg(v_methods_78_, v_config_79_, v_hyp_80_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___boxed(lean_object* v_methods_91_, lean_object* v_config_92_, lean_object* v_hyp_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp(v_methods_91_, v_config_92_, v_hyp_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
return v_res_103_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__0(void){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_104_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__1(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__0);
v___x_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg(lean_object* v_methods_107_, lean_object* v_config_108_, lean_object* v_hyp_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_){
_start:
{
lean_object* v___x_118_; lean_object* v_rewriteSimpCache_119_; lean_object* v_rewriteDSimpCache_120_; lean_object* v_acCache_121_; lean_object* v_typeAnalysis_122_; lean_object* v_goal_123_; lean_object* v_hypotheses_124_; uint8_t v_didChange_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_168_; 
v___x_118_ = lean_st_ref_take(v_a_110_);
v_rewriteSimpCache_119_ = lean_ctor_get(v___x_118_, 0);
v_rewriteDSimpCache_120_ = lean_ctor_get(v___x_118_, 1);
v_acCache_121_ = lean_ctor_get(v___x_118_, 2);
v_typeAnalysis_122_ = lean_ctor_get(v___x_118_, 3);
v_goal_123_ = lean_ctor_get(v___x_118_, 4);
v_hypotheses_124_ = lean_ctor_get(v___x_118_, 5);
v_didChange_125_ = lean_ctor_get_uint8(v___x_118_, sizeof(void*)*6);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_168_ == 0)
{
v___x_127_ = v___x_118_;
v_isShared_128_ = v_isSharedCheck_168_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_hypotheses_124_);
lean_inc(v_goal_123_);
lean_inc(v_typeAnalysis_122_);
lean_inc(v_acCache_121_);
lean_inc(v_rewriteDSimpCache_120_);
lean_inc(v_rewriteSimpCache_119_);
lean_dec(v___x_118_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_168_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_129_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___closed__1);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v___x_129_);
v___x_131_ = v___x_127_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_129_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_rewriteDSimpCache_120_);
lean_ctor_set(v_reuseFailAlloc_167_, 2, v_acCache_121_);
lean_ctor_set(v_reuseFailAlloc_167_, 3, v_typeAnalysis_122_);
lean_ctor_set(v_reuseFailAlloc_167_, 4, v_goal_123_);
lean_ctor_set(v_reuseFailAlloc_167_, 5, v_hypotheses_124_);
lean_ctor_set_uint8(v_reuseFailAlloc_167_, sizeof(void*)*6, v_didChange_125_);
v___x_131_ = v_reuseFailAlloc_167_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; lean_object* v_type_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_132_ = lean_st_ref_set(v_a_110_, v___x_131_);
v_type_133_ = lean_ctor_get(v_hyp_109_, 1);
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v_rewriteSimpCache_119_);
lean_ctor_set(v___x_135_, 2, v___x_129_);
lean_ctor_set(v___x_135_, 3, v___x_129_);
lean_inc_ref(v_type_133_);
v___x_136_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_136_, 0, v_type_133_);
v___x_137_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v___x_136_, v_methods_107_, v_config_108_, v___x_135_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v_fst_139_; lean_object* v_snd_140_; lean_object* v___x_141_; lean_object* v_persistentCache_142_; lean_object* v_rewriteDSimpCache_143_; lean_object* v_acCache_144_; lean_object* v_typeAnalysis_145_; lean_object* v_goal_146_; lean_object* v_hypotheses_147_; uint8_t v_didChange_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_157_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_a_138_);
lean_dec_ref_known(v___x_137_, 1);
v_fst_139_ = lean_ctor_get(v_a_138_, 0);
lean_inc(v_fst_139_);
v_snd_140_ = lean_ctor_get(v_a_138_, 1);
lean_inc(v_snd_140_);
lean_dec(v_a_138_);
v___x_141_ = lean_st_ref_take(v_a_110_);
v_persistentCache_142_ = lean_ctor_get(v_snd_140_, 1);
lean_inc_ref(v_persistentCache_142_);
lean_dec(v_snd_140_);
v_rewriteDSimpCache_143_ = lean_ctor_get(v___x_141_, 1);
v_acCache_144_ = lean_ctor_get(v___x_141_, 2);
v_typeAnalysis_145_ = lean_ctor_get(v___x_141_, 3);
v_goal_146_ = lean_ctor_get(v___x_141_, 4);
v_hypotheses_147_ = lean_ctor_get(v___x_141_, 5);
v_didChange_148_ = lean_ctor_get_uint8(v___x_141_, sizeof(void*)*6);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; 
v_unused_158_ = lean_ctor_get(v___x_141_, 0);
lean_dec(v_unused_158_);
v___x_150_ = v___x_141_;
v_isShared_151_ = v_isSharedCheck_157_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_hypotheses_147_);
lean_inc(v_goal_146_);
lean_inc(v_typeAnalysis_145_);
lean_inc(v_acCache_144_);
lean_inc(v_rewriteDSimpCache_143_);
lean_dec(v___x_141_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_157_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v_persistentCache_142_);
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_persistentCache_142_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_rewriteDSimpCache_143_);
lean_ctor_set(v_reuseFailAlloc_156_, 2, v_acCache_144_);
lean_ctor_set(v_reuseFailAlloc_156_, 3, v_typeAnalysis_145_);
lean_ctor_set(v_reuseFailAlloc_156_, 4, v_goal_146_);
lean_ctor_set(v_reuseFailAlloc_156_, 5, v_hypotheses_147_);
lean_ctor_set_uint8(v_reuseFailAlloc_156_, sizeof(void*)*6, v_didChange_148_);
v___x_153_ = v_reuseFailAlloc_156_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_st_ref_set(v_a_110_, v___x_153_);
v___x_155_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Hyp_applySimpResult___redArg(v_hyp_109_, v_fst_139_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_);
return v___x_155_;
}
}
}
else
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
lean_dec_ref(v_hyp_109_);
v_a_159_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v___x_137_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_137_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_a_159_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg___boxed(lean_object* v_methods_169_, lean_object* v_config_170_, lean_object* v_hyp_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg(v_methods_169_, v_config_170_, v_hyp_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp(lean_object* v_methods_181_, lean_object* v_config_182_, lean_object* v_hyp_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg(v_methods_181_, v_config_182_, v_hyp_183_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___boxed(lean_object* v_methods_194_, lean_object* v_config_195_, lean_object* v_hyp_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp(v_methods_194_, v_config_195_, v_hyp_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
lean_dec(v_a_204_);
lean_dec_ref(v_a_203_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg___lam__0(lean_object* v_x_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v___x_217_; 
lean_inc(v___y_211_);
lean_inc_ref(v___y_210_);
lean_inc(v___y_209_);
lean_inc_ref(v___y_208_);
v___x_217_ = lean_apply_9(v_x_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, lean_box(0));
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg___lam__0___boxed(lean_object* v_x_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg___lam__0(v_x_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg(lean_object* v_mvarId_229_, lean_object* v_x_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v___f_240_; lean_object* v___x_241_; 
lean_inc(v___y_234_);
lean_inc_ref(v___y_233_);
lean_inc(v___y_232_);
lean_inc_ref(v___y_231_);
v___f_240_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_240_, 0, v_x_230_);
lean_closure_set(v___f_240_, 1, v___y_231_);
lean_closure_set(v___f_240_, 2, v___y_232_);
lean_closure_set(v___f_240_, 3, v___y_233_);
lean_closure_set(v___f_240_, 4, v___y_234_);
v___x_241_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_229_, v___f_240_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
if (lean_obj_tag(v___x_241_) == 0)
{
return v___x_241_;
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_241_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_241_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg___boxed(lean_object* v_mvarId_250_, lean_object* v_x_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg(v_mvarId_250_, v_x_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3(lean_object* v_00_u03b1_262_, lean_object* v_mvarId_263_, lean_object* v_x_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg(v_mvarId_263_, v_x_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___boxed(lean_object* v_00_u03b1_275_, lean_object* v_mvarId_276_, lean_object* v_x_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3(v_00_u03b1_275_, v_mvarId_276_, v_x_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
return v_res_287_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = lean_unsigned_to_nat(32u);
v___x_289_ = lean_mk_empty_array_with_capacity(v___x_288_);
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__1(void){
_start:
{
size_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_291_ = ((size_t)5ULL);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_unsigned_to_nat(32u);
v___x_294_ = lean_mk_empty_array_with_capacity(v___x_293_);
v___x_295_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__0);
v___x_296_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v___x_294_);
lean_ctor_set(v___x_296_, 2, v___x_292_);
lean_ctor_set(v___x_296_, 3, v___x_292_);
lean_ctor_set_usize(v___x_296_, 4, v___x_291_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg(lean_object* v___y_297_){
_start:
{
lean_object* v___x_299_; lean_object* v_traceState_300_; lean_object* v_traces_301_; lean_object* v___x_302_; lean_object* v_traceState_303_; lean_object* v_env_304_; lean_object* v_nextMacroScope_305_; lean_object* v_ngen_306_; lean_object* v_auxDeclNGen_307_; lean_object* v_cache_308_; lean_object* v_messages_309_; lean_object* v_infoState_310_; lean_object* v_snapshotTasks_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_330_; 
v___x_299_ = lean_st_ref_get(v___y_297_);
v_traceState_300_ = lean_ctor_get(v___x_299_, 4);
lean_inc_ref(v_traceState_300_);
lean_dec(v___x_299_);
v_traces_301_ = lean_ctor_get(v_traceState_300_, 0);
lean_inc_ref(v_traces_301_);
lean_dec_ref(v_traceState_300_);
v___x_302_ = lean_st_ref_take(v___y_297_);
v_traceState_303_ = lean_ctor_get(v___x_302_, 4);
v_env_304_ = lean_ctor_get(v___x_302_, 0);
v_nextMacroScope_305_ = lean_ctor_get(v___x_302_, 1);
v_ngen_306_ = lean_ctor_get(v___x_302_, 2);
v_auxDeclNGen_307_ = lean_ctor_get(v___x_302_, 3);
v_cache_308_ = lean_ctor_get(v___x_302_, 5);
v_messages_309_ = lean_ctor_get(v___x_302_, 6);
v_infoState_310_ = lean_ctor_get(v___x_302_, 7);
v_snapshotTasks_311_ = lean_ctor_get(v___x_302_, 8);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_330_ == 0)
{
v___x_313_ = v___x_302_;
v_isShared_314_ = v_isSharedCheck_330_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_snapshotTasks_311_);
lean_inc(v_infoState_310_);
lean_inc(v_messages_309_);
lean_inc(v_cache_308_);
lean_inc(v_traceState_303_);
lean_inc(v_auxDeclNGen_307_);
lean_inc(v_ngen_306_);
lean_inc(v_nextMacroScope_305_);
lean_inc(v_env_304_);
lean_dec(v___x_302_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_330_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
uint64_t v_tid_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_328_; 
v_tid_315_ = lean_ctor_get_uint64(v_traceState_303_, sizeof(void*)*1);
v_isSharedCheck_328_ = !lean_is_exclusive(v_traceState_303_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; 
v_unused_329_ = lean_ctor_get(v_traceState_303_, 0);
lean_dec(v_unused_329_);
v___x_317_ = v_traceState_303_;
v_isShared_318_ = v_isSharedCheck_328_;
goto v_resetjp_316_;
}
else
{
lean_dec(v_traceState_303_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_328_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_319_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___closed__1);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_319_);
v___x_321_ = v___x_317_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_319_);
lean_ctor_set_uint64(v_reuseFailAlloc_327_, sizeof(void*)*1, v_tid_315_);
v___x_321_ = v_reuseFailAlloc_327_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_323_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 4, v___x_321_);
v___x_323_ = v___x_313_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_env_304_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_nextMacroScope_305_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_ngen_306_);
lean_ctor_set(v_reuseFailAlloc_326_, 3, v_auxDeclNGen_307_);
lean_ctor_set(v_reuseFailAlloc_326_, 4, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_326_, 5, v_cache_308_);
lean_ctor_set(v_reuseFailAlloc_326_, 6, v_messages_309_);
lean_ctor_set(v_reuseFailAlloc_326_, 7, v_infoState_310_);
lean_ctor_set(v_reuseFailAlloc_326_, 8, v_snapshotTasks_311_);
v___x_323_ = v_reuseFailAlloc_326_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_st_ref_set(v___y_297_, v___x_323_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v_traces_301_);
return v___x_325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg___boxed(lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg(v___y_331_);
lean_dec(v___y_331_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5(lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg(v___y_341_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___boxed(lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5(v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
return v_res_353_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(lean_object* v_opts_354_, lean_object* v_opt_355_){
_start:
{
lean_object* v_name_356_; lean_object* v_defValue_357_; lean_object* v_map_358_; lean_object* v___x_359_; 
v_name_356_ = lean_ctor_get(v_opt_355_, 0);
v_defValue_357_ = lean_ctor_get(v_opt_355_, 1);
v_map_358_ = lean_ctor_get(v_opts_354_, 0);
v___x_359_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_358_, v_name_356_);
if (lean_obj_tag(v___x_359_) == 0)
{
uint8_t v___x_360_; 
v___x_360_ = lean_unbox(v_defValue_357_);
return v___x_360_;
}
else
{
lean_object* v_val_361_; 
v_val_361_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_val_361_);
lean_dec_ref_known(v___x_359_, 1);
if (lean_obj_tag(v_val_361_) == 1)
{
uint8_t v_v_362_; 
v_v_362_ = lean_ctor_get_uint8(v_val_361_, 0);
lean_dec_ref_known(v_val_361_, 0);
return v_v_362_;
}
else
{
uint8_t v___x_363_; 
lean_dec(v_val_361_);
v___x_363_ = lean_unbox(v_defValue_357_);
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6___boxed(lean_object* v_opts_364_, lean_object* v_opt_365_){
_start:
{
uint8_t v_res_366_; lean_object* v_r_367_; 
v_res_366_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(v_opts_364_, v_opt_365_);
lean_dec_ref(v_opt_365_);
lean_dec_ref(v_opts_364_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__2(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__1));
v___x_372_ = l_Lean_MessageData_ofFormat(v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(lean_object* v_x_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___closed__2);
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___boxed(lean_object* v_x_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(v_x_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec_ref(v_x_385_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1(lean_object* v_e_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_Meta_Sym_Simp_simpControl(v_e_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_438_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_438_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_438_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_438_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
if (lean_obj_tag(v_a_408_) == 0)
{
uint8_t v_contextDependent_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_423_; 
v_contextDependent_412_ = lean_ctor_get_uint8(v_a_408_, 1);
v_isSharedCheck_423_ = !lean_is_exclusive(v_a_408_);
if (v_isSharedCheck_423_ == 0)
{
v___x_414_ = v_a_408_;
v_isShared_415_ = v_isSharedCheck_423_;
goto v_resetjp_413_;
}
else
{
lean_dec(v_a_408_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_423_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
uint8_t v___x_416_; lean_object* v___x_418_; 
v___x_416_ = 0;
if (v_isShared_415_ == 0)
{
v___x_418_ = v___x_414_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_422_, 1, v_contextDependent_412_);
v___x_418_ = v_reuseFailAlloc_422_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_420_; 
lean_ctor_set_uint8(v___x_418_, 0, v___x_416_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_418_);
v___x_420_ = v___x_410_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
else
{
lean_object* v_e_x27_424_; lean_object* v_proof_425_; uint8_t v_contextDependent_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_437_; 
v_e_x27_424_ = lean_ctor_get(v_a_408_, 0);
v_proof_425_ = lean_ctor_get(v_a_408_, 1);
v_contextDependent_426_ = lean_ctor_get_uint8(v_a_408_, sizeof(void*)*2 + 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v_a_408_);
if (v_isSharedCheck_437_ == 0)
{
v___x_428_ = v_a_408_;
v_isShared_429_ = v_isSharedCheck_437_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_proof_425_);
lean_inc(v_e_x27_424_);
lean_dec(v_a_408_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_437_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
uint8_t v___x_430_; lean_object* v___x_432_; 
v___x_430_ = 0;
if (v_isShared_429_ == 0)
{
v___x_432_ = v___x_428_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_e_x27_424_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_proof_425_);
lean_ctor_set_uint8(v_reuseFailAlloc_436_, sizeof(void*)*2 + 1, v_contextDependent_426_);
v___x_432_ = v_reuseFailAlloc_436_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_434_; 
lean_ctor_set_uint8(v___x_432_, sizeof(void*)*2, v___x_430_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_432_);
v___x_434_ = v___x_410_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
}
else
{
return v___x_407_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1___boxed(lean_object* v_e_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__1(v_e_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2(lean_object* v_val_451_, lean_object* v_a_452_, lean_object* v___x_453_, lean_object* v_x_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v___x_466_; 
lean_inc_ref(v___y_455_);
v___x_466_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteSimproc(v_val_451_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; 
v_a_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_467_);
if (lean_obj_tag(v_a_467_) == 0)
{
uint8_t v_done_468_; 
v_done_468_ = lean_ctor_get_uint8(v_a_467_, 0);
if (v_done_468_ == 0)
{
uint8_t v_contextDependent_469_; lean_object* v___x_470_; 
lean_dec_ref_known(v___x_466_, 1);
v_contextDependent_469_ = lean_ctor_get_uint8(v_a_467_, 1);
lean_dec_ref_known(v_a_467_, 0);
v___x_470_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_452_, v___x_453_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; uint8_t v___y_473_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
if (v_contextDependent_469_ == 0)
{
lean_dec(v_a_471_);
return v___x_470_;
}
else
{
if (lean_obj_tag(v_a_471_) == 0)
{
uint8_t v_contextDependent_483_; 
v_contextDependent_483_ = lean_ctor_get_uint8(v_a_471_, 1);
v___y_473_ = v_contextDependent_483_;
goto v___jp_472_;
}
else
{
uint8_t v_contextDependent_484_; 
v_contextDependent_484_ = lean_ctor_get_uint8(v_a_471_, sizeof(void*)*2 + 1);
v___y_473_ = v_contextDependent_484_;
goto v___jp_472_;
}
}
v___jp_472_:
{
if (v___y_473_ == 0)
{
lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_481_; 
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_481_ == 0)
{
lean_object* v_unused_482_; 
v_unused_482_ = lean_ctor_get(v___x_470_, 0);
lean_dec(v_unused_482_);
v___x_475_ = v___x_470_;
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
else
{
lean_dec(v___x_470_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_481_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_477_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_471_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_477_);
v___x_479_ = v___x_475_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
else
{
lean_dec(v_a_471_);
return v___x_470_;
}
}
}
else
{
return v___x_470_;
}
}
else
{
lean_dec_ref_known(v_a_467_, 0);
lean_dec_ref(v___y_455_);
lean_dec_ref(v___x_453_);
return v___x_466_;
}
}
else
{
uint8_t v_done_485_; 
v_done_485_ = lean_ctor_get_uint8(v_a_467_, sizeof(void*)*2);
if (v_done_485_ == 0)
{
lean_object* v_e_x27_486_; lean_object* v_proof_487_; uint8_t v_contextDependent_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_538_; 
lean_dec_ref_known(v___x_466_, 1);
v_e_x27_486_ = lean_ctor_get(v_a_467_, 0);
v_proof_487_ = lean_ctor_get(v_a_467_, 1);
v_contextDependent_488_ = lean_ctor_get_uint8(v_a_467_, sizeof(void*)*2 + 1);
v_isSharedCheck_538_ = !lean_is_exclusive(v_a_467_);
if (v_isSharedCheck_538_ == 0)
{
v___x_490_ = v_a_467_;
v_isShared_491_ = v_isSharedCheck_538_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_proof_487_);
lean_inc(v_e_x27_486_);
lean_dec(v_a_467_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_538_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; 
lean_inc_ref(v_e_x27_486_);
v___x_492_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_452_, v___x_453_, v_e_x27_486_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_537_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_537_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_537_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_537_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
if (lean_obj_tag(v_a_493_) == 0)
{
uint8_t v_done_497_; uint8_t v_contextDependent_498_; uint8_t v___y_500_; 
lean_dec_ref(v___y_455_);
v_done_497_ = lean_ctor_get_uint8(v_a_493_, 0);
v_contextDependent_498_ = lean_ctor_get_uint8(v_a_493_, 1);
lean_dec_ref_known(v_a_493_, 0);
if (v_contextDependent_488_ == 0)
{
v___y_500_ = v_contextDependent_498_;
goto v___jp_499_;
}
else
{
v___y_500_ = v_contextDependent_488_;
goto v___jp_499_;
}
v___jp_499_:
{
lean_object* v___x_502_; 
if (v_isShared_491_ == 0)
{
v___x_502_ = v___x_490_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_e_x27_486_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_proof_487_);
v___x_502_ = v_reuseFailAlloc_506_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_504_; 
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*2, v_done_497_);
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*2 + 1, v___y_500_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_502_);
v___x_504_ = v___x_495_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
else
{
lean_object* v_e_x27_507_; lean_object* v_proof_508_; uint8_t v_done_509_; uint8_t v_contextDependent_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_536_; 
lean_del_object(v___x_495_);
lean_del_object(v___x_490_);
v_e_x27_507_ = lean_ctor_get(v_a_493_, 0);
v_proof_508_ = lean_ctor_get(v_a_493_, 1);
v_done_509_ = lean_ctor_get_uint8(v_a_493_, sizeof(void*)*2);
v_contextDependent_510_ = lean_ctor_get_uint8(v_a_493_, sizeof(void*)*2 + 1);
v_isSharedCheck_536_ = !lean_is_exclusive(v_a_493_);
if (v_isSharedCheck_536_ == 0)
{
v___x_512_ = v_a_493_;
v_isShared_513_ = v_isSharedCheck_536_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_proof_508_);
lean_inc(v_e_x27_507_);
lean_dec(v_a_493_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_536_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; 
lean_inc_ref(v_e_x27_507_);
v___x_514_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_455_, v_e_x27_486_, v_proof_487_, v_e_x27_507_, v_proof_508_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_527_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_527_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_527_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_527_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
uint8_t v___y_520_; 
if (v_contextDependent_488_ == 0)
{
v___y_520_ = v_contextDependent_510_;
goto v___jp_519_;
}
else
{
v___y_520_ = v_contextDependent_488_;
goto v___jp_519_;
}
v___jp_519_:
{
lean_object* v___x_522_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 1, v_a_515_);
v___x_522_ = v___x_512_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_e_x27_507_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_a_515_);
lean_ctor_set_uint8(v_reuseFailAlloc_526_, sizeof(void*)*2, v_done_509_);
v___x_522_ = v_reuseFailAlloc_526_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_524_; 
lean_ctor_set_uint8(v___x_522_, sizeof(void*)*2 + 1, v___y_520_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_522_);
v___x_524_ = v___x_517_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
else
{
lean_object* v_a_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_535_; 
lean_del_object(v___x_512_);
lean_dec_ref(v_e_x27_507_);
v_a_528_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_535_ == 0)
{
v___x_530_ = v___x_514_;
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_a_528_);
lean_dec(v___x_514_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_535_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_533_; 
if (v_isShared_531_ == 0)
{
v___x_533_ = v___x_530_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_a_528_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_490_);
lean_dec_ref(v_proof_487_);
lean_dec_ref(v_e_x27_486_);
lean_dec_ref(v___y_455_);
return v___x_492_;
}
}
}
else
{
lean_dec_ref_known(v_a_467_, 2);
lean_dec_ref(v___y_455_);
lean_dec_ref(v___x_453_);
return v___x_466_;
}
}
}
else
{
lean_dec_ref(v___y_455_);
lean_dec_ref(v___x_453_);
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2___boxed(lean_object* v_val_539_, lean_object* v_a_540_, lean_object* v___x_541_, lean_object* v_x_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2(v_val_539_, v_a_540_, v___x_541_, v_x_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v_a_540_);
lean_dec(v_val_539_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3(lean_object* v___x_555_, lean_object* v___f_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v___x_568_; 
lean_inc_ref(v___y_557_);
v___x_568_ = l_Lean_Meta_Sym_Simp_evalGround___redArg(v___x_555_, v___y_557_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_570_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_a_569_);
v___x_570_ = lean_box(0);
if (lean_obj_tag(v_a_569_) == 0)
{
uint8_t v_done_571_; 
v_done_571_ = lean_ctor_get_uint8(v_a_569_, 0);
if (v_done_571_ == 0)
{
uint8_t v_contextDependent_572_; lean_object* v___x_573_; 
lean_dec_ref_known(v___x_568_, 1);
v_contextDependent_572_ = lean_ctor_get_uint8(v_a_569_, 1);
lean_dec_ref_known(v_a_569_, 0);
v___x_573_ = lean_apply_12(v___f_556_, v___x_570_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, lean_box(0));
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; uint8_t v___y_576_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
if (v_contextDependent_572_ == 0)
{
lean_dec(v_a_574_);
return v___x_573_;
}
else
{
if (lean_obj_tag(v_a_574_) == 0)
{
uint8_t v_contextDependent_586_; 
v_contextDependent_586_ = lean_ctor_get_uint8(v_a_574_, 1);
v___y_576_ = v_contextDependent_586_;
goto v___jp_575_;
}
else
{
uint8_t v_contextDependent_587_; 
v_contextDependent_587_ = lean_ctor_get_uint8(v_a_574_, sizeof(void*)*2 + 1);
v___y_576_ = v_contextDependent_587_;
goto v___jp_575_;
}
}
v___jp_575_:
{
if (v___y_576_ == 0)
{
lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_584_; 
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; 
v_unused_585_ = lean_ctor_get(v___x_573_, 0);
lean_dec(v_unused_585_);
v___x_578_ = v___x_573_;
v_isShared_579_ = v_isSharedCheck_584_;
goto v_resetjp_577_;
}
else
{
lean_dec(v___x_573_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_584_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_580_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_574_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v___x_580_);
v___x_582_ = v___x_578_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
else
{
lean_dec(v_a_574_);
return v___x_573_;
}
}
}
else
{
return v___x_573_;
}
}
else
{
lean_dec_ref_known(v_a_569_, 0);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec_ref(v___f_556_);
return v___x_568_;
}
}
else
{
uint8_t v_done_588_; 
v_done_588_ = lean_ctor_get_uint8(v_a_569_, sizeof(void*)*2);
if (v_done_588_ == 0)
{
lean_object* v_e_x27_589_; lean_object* v_proof_590_; uint8_t v_contextDependent_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_641_; 
lean_dec_ref_known(v___x_568_, 1);
v_e_x27_589_ = lean_ctor_get(v_a_569_, 0);
v_proof_590_ = lean_ctor_get(v_a_569_, 1);
v_contextDependent_591_ = lean_ctor_get_uint8(v_a_569_, sizeof(void*)*2 + 1);
v_isSharedCheck_641_ = !lean_is_exclusive(v_a_569_);
if (v_isSharedCheck_641_ == 0)
{
v___x_593_ = v_a_569_;
v_isShared_594_ = v_isSharedCheck_641_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_proof_590_);
lean_inc(v_e_x27_589_);
lean_dec(v_a_569_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_641_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; 
lean_inc(v___y_566_);
lean_inc_ref(v___y_565_);
lean_inc(v___y_564_);
lean_inc_ref(v___y_563_);
lean_inc(v___y_562_);
lean_inc_ref(v___y_561_);
lean_inc_ref(v_e_x27_589_);
v___x_595_ = lean_apply_12(v___f_556_, v___x_570_, v_e_x27_589_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, lean_box(0));
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_640_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_640_ == 0)
{
v___x_598_ = v___x_595_;
v_isShared_599_ = v_isSharedCheck_640_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_640_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
if (lean_obj_tag(v_a_596_) == 0)
{
uint8_t v_done_600_; uint8_t v_contextDependent_601_; uint8_t v___y_603_; 
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec_ref(v___y_557_);
v_done_600_ = lean_ctor_get_uint8(v_a_596_, 0);
v_contextDependent_601_ = lean_ctor_get_uint8(v_a_596_, 1);
lean_dec_ref_known(v_a_596_, 0);
if (v_contextDependent_591_ == 0)
{
v___y_603_ = v_contextDependent_601_;
goto v___jp_602_;
}
else
{
v___y_603_ = v_contextDependent_591_;
goto v___jp_602_;
}
v___jp_602_:
{
lean_object* v___x_605_; 
if (v_isShared_594_ == 0)
{
v___x_605_ = v___x_593_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_e_x27_589_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_proof_590_);
v___x_605_ = v_reuseFailAlloc_609_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_607_; 
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*2, v_done_600_);
lean_ctor_set_uint8(v___x_605_, sizeof(void*)*2 + 1, v___y_603_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v___x_605_);
v___x_607_ = v___x_598_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
else
{
lean_object* v_e_x27_610_; lean_object* v_proof_611_; uint8_t v_done_612_; uint8_t v_contextDependent_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_639_; 
lean_del_object(v___x_598_);
lean_del_object(v___x_593_);
v_e_x27_610_ = lean_ctor_get(v_a_596_, 0);
v_proof_611_ = lean_ctor_get(v_a_596_, 1);
v_done_612_ = lean_ctor_get_uint8(v_a_596_, sizeof(void*)*2);
v_contextDependent_613_ = lean_ctor_get_uint8(v_a_596_, sizeof(void*)*2 + 1);
v_isSharedCheck_639_ = !lean_is_exclusive(v_a_596_);
if (v_isSharedCheck_639_ == 0)
{
v___x_615_ = v_a_596_;
v_isShared_616_ = v_isSharedCheck_639_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_proof_611_);
lean_inc(v_e_x27_610_);
lean_dec(v_a_596_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_639_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; 
lean_inc_ref(v_e_x27_610_);
v___x_617_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_557_, v_e_x27_589_, v_proof_590_, v_e_x27_610_, v_proof_611_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_630_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_630_ == 0)
{
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_630_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_630_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
uint8_t v___y_623_; 
if (v_contextDependent_591_ == 0)
{
v___y_623_ = v_contextDependent_613_;
goto v___jp_622_;
}
else
{
v___y_623_ = v_contextDependent_591_;
goto v___jp_622_;
}
v___jp_622_:
{
lean_object* v___x_625_; 
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 1, v_a_618_);
v___x_625_ = v___x_615_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_e_x27_610_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_a_618_);
lean_ctor_set_uint8(v_reuseFailAlloc_629_, sizeof(void*)*2, v_done_612_);
v___x_625_ = v_reuseFailAlloc_629_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_627_; 
lean_ctor_set_uint8(v___x_625_, sizeof(void*)*2 + 1, v___y_623_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_625_);
v___x_627_ = v___x_620_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_del_object(v___x_615_);
lean_dec_ref(v_e_x27_610_);
v_a_631_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_617_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_617_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_593_);
lean_dec_ref(v_proof_590_);
lean_dec_ref(v_e_x27_589_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec_ref(v___y_557_);
return v___x_595_;
}
}
}
else
{
lean_dec_ref_known(v_a_569_, 2);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec_ref(v___f_556_);
return v___x_568_;
}
}
}
else
{
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec_ref(v___f_556_);
return v___x_568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3___boxed(lean_object* v___x_642_, lean_object* v___f_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3(v___x_642_, v___f_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
lean_dec(v___x_642_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__5(lean_object* v_snd_656_, lean_object* v_a_657_, lean_object* v___x_658_, lean_object* v_____r_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_669_ = lean_array_push(v_snd_656_, v_a_657_);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_658_);
lean_ctor_set(v___x_670_, 1, v___x_669_);
v___x_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__5___boxed(lean_object* v_snd_673_, lean_object* v_a_674_, lean_object* v___x_675_, lean_object* v_____r_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__5(v_snd_673_, v_a_674_, v___x_675_, v_____r_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(lean_object* v_msgData_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v___x_693_; lean_object* v_env_694_; lean_object* v___x_695_; lean_object* v_mctx_696_; lean_object* v_lctx_697_; lean_object* v_options_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_693_ = lean_st_ref_get(v___y_691_);
v_env_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc_ref(v_env_694_);
lean_dec(v___x_693_);
v___x_695_ = lean_st_ref_get(v___y_689_);
v_mctx_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc_ref(v_mctx_696_);
lean_dec(v___x_695_);
v_lctx_697_ = lean_ctor_get(v___y_688_, 2);
v_options_698_ = lean_ctor_get(v___y_690_, 2);
lean_inc_ref(v_options_698_);
lean_inc_ref(v_lctx_697_);
v___x_699_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_699_, 0, v_env_694_);
lean_ctor_set(v___x_699_, 1, v_mctx_696_);
lean_ctor_set(v___x_699_, 2, v_lctx_697_);
lean_ctor_set(v___x_699_, 3, v_options_698_);
v___x_700_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v_msgData_687_);
v___x_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0___boxed(lean_object* v_msgData_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(v_msgData_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
return v_res_708_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_709_; double v___x_710_; 
v___x_709_ = lean_unsigned_to_nat(0u);
v___x_710_ = lean_float_of_nat(v___x_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(lean_object* v_cls_714_, lean_object* v_msg_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_ref_721_; lean_object* v___x_722_; lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_767_; 
v_ref_721_ = lean_ctor_get(v___y_718_, 5);
v___x_722_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(v_msg_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_767_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_767_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_767_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; lean_object* v_traceState_728_; lean_object* v_env_729_; lean_object* v_nextMacroScope_730_; lean_object* v_ngen_731_; lean_object* v_auxDeclNGen_732_; lean_object* v_cache_733_; lean_object* v_messages_734_; lean_object* v_infoState_735_; lean_object* v_snapshotTasks_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_766_; 
v___x_727_ = lean_st_ref_take(v___y_719_);
v_traceState_728_ = lean_ctor_get(v___x_727_, 4);
v_env_729_ = lean_ctor_get(v___x_727_, 0);
v_nextMacroScope_730_ = lean_ctor_get(v___x_727_, 1);
v_ngen_731_ = lean_ctor_get(v___x_727_, 2);
v_auxDeclNGen_732_ = lean_ctor_get(v___x_727_, 3);
v_cache_733_ = lean_ctor_get(v___x_727_, 5);
v_messages_734_ = lean_ctor_get(v___x_727_, 6);
v_infoState_735_ = lean_ctor_get(v___x_727_, 7);
v_snapshotTasks_736_ = lean_ctor_get(v___x_727_, 8);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_766_ == 0)
{
v___x_738_ = v___x_727_;
v_isShared_739_ = v_isSharedCheck_766_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_snapshotTasks_736_);
lean_inc(v_infoState_735_);
lean_inc(v_messages_734_);
lean_inc(v_cache_733_);
lean_inc(v_traceState_728_);
lean_inc(v_auxDeclNGen_732_);
lean_inc(v_ngen_731_);
lean_inc(v_nextMacroScope_730_);
lean_inc(v_env_729_);
lean_dec(v___x_727_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_766_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
uint64_t v_tid_740_; lean_object* v_traces_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_765_; 
v_tid_740_ = lean_ctor_get_uint64(v_traceState_728_, sizeof(void*)*1);
v_traces_741_ = lean_ctor_get(v_traceState_728_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v_traceState_728_);
if (v_isSharedCheck_765_ == 0)
{
v___x_743_ = v_traceState_728_;
v_isShared_744_ = v_isSharedCheck_765_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_traces_741_);
lean_dec(v_traceState_728_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_765_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; double v___x_746_; uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_745_ = lean_box(0);
v___x_746_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0);
v___x_747_ = 0;
v___x_748_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1));
v___x_749_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_749_, 0, v_cls_714_);
lean_ctor_set(v___x_749_, 1, v___x_745_);
lean_ctor_set(v___x_749_, 2, v___x_748_);
lean_ctor_set_float(v___x_749_, sizeof(void*)*3, v___x_746_);
lean_ctor_set_float(v___x_749_, sizeof(void*)*3 + 8, v___x_746_);
lean_ctor_set_uint8(v___x_749_, sizeof(void*)*3 + 16, v___x_747_);
v___x_750_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__2));
v___x_751_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set(v___x_751_, 1, v_a_723_);
lean_ctor_set(v___x_751_, 2, v___x_750_);
lean_inc(v_ref_721_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_ref_721_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = l_Lean_PersistentArray_push___redArg(v_traces_741_, v___x_752_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_753_);
v___x_755_ = v___x_743_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_753_);
lean_ctor_set_uint64(v_reuseFailAlloc_764_, sizeof(void*)*1, v_tid_740_);
v___x_755_ = v_reuseFailAlloc_764_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_757_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 4, v___x_755_);
v___x_757_ = v___x_738_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_env_729_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_nextMacroScope_730_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v_ngen_731_);
lean_ctor_set(v_reuseFailAlloc_763_, 3, v_auxDeclNGen_732_);
lean_ctor_set(v_reuseFailAlloc_763_, 4, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_763_, 5, v_cache_733_);
lean_ctor_set(v_reuseFailAlloc_763_, 6, v_messages_734_);
lean_ctor_set(v_reuseFailAlloc_763_, 7, v_infoState_735_);
lean_ctor_set(v_reuseFailAlloc_763_, 8, v_snapshotTasks_736_);
v___x_757_ = v_reuseFailAlloc_763_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_761_; 
v___x_758_ = lean_st_ref_set(v___y_719_, v___x_757_);
v___x_759_ = lean_box(0);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_759_);
v___x_761_ = v___x_725_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_759_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___boxed(lean_object* v_cls_768_, lean_object* v_msg_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v_cls_768_, v_msg_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__3(lean_object* v_x_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__3___closed__0));
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__3___boxed(lean_object* v_x_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__3(v_x_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v_x_791_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__1(lean_object* v___f_803_, lean_object* v_x_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v___x_816_; 
lean_inc_ref(v___y_805_);
v___x_816_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_805_, v___y_811_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_818_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
v___x_818_ = lean_box(0);
if (lean_obj_tag(v_a_817_) == 0)
{
uint8_t v_done_819_; 
v_done_819_ = lean_ctor_get_uint8(v_a_817_, 0);
lean_dec_ref_known(v_a_817_, 0);
if (v_done_819_ == 0)
{
lean_object* v___x_820_; 
lean_dec_ref_known(v___x_816_, 1);
lean_inc(v___y_814_);
lean_inc_ref(v___y_813_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
lean_inc(v___y_808_);
lean_inc_ref(v___y_807_);
lean_inc(v___y_806_);
v___x_820_ = lean_apply_12(v___f_803_, v___x_818_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, lean_box(0));
return v___x_820_;
}
else
{
lean_dec_ref(v___y_805_);
lean_dec_ref(v___f_803_);
return v___x_816_;
}
}
else
{
uint8_t v_done_821_; 
lean_dec_ref(v___y_805_);
v_done_821_ = lean_ctor_get_uint8(v_a_817_, sizeof(void*)*1);
if (v_done_821_ == 0)
{
lean_object* v_e_x27_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_840_; 
lean_dec_ref_known(v___x_816_, 1);
v_e_x27_822_ = lean_ctor_get(v_a_817_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v_a_817_);
if (v_isSharedCheck_840_ == 0)
{
v___x_824_ = v_a_817_;
v_isShared_825_ = v_isSharedCheck_840_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_e_x27_822_);
lean_dec(v_a_817_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_840_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; 
lean_inc(v___y_814_);
lean_inc_ref(v___y_813_);
lean_inc(v___y_812_);
lean_inc_ref(v___y_811_);
lean_inc(v___y_810_);
lean_inc_ref(v___y_809_);
lean_inc(v___y_808_);
lean_inc_ref(v___y_807_);
lean_inc(v___y_806_);
lean_inc_ref(v_e_x27_822_);
v___x_826_ = lean_apply_12(v___f_803_, v___x_818_, v_e_x27_822_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, lean_box(0));
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
if (lean_obj_tag(v_a_827_) == 0)
{
lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_838_; 
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; 
v_unused_839_ = lean_ctor_get(v___x_826_, 0);
lean_dec(v_unused_839_);
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_838_;
goto v_resetjp_828_;
}
else
{
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_838_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
uint8_t v_done_831_; lean_object* v___x_833_; 
v_done_831_ = lean_ctor_get_uint8(v_a_827_, 0);
lean_dec_ref_known(v_a_827_, 0);
if (v_isShared_825_ == 0)
{
v___x_833_ = v___x_824_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_e_x27_822_);
v___x_833_ = v_reuseFailAlloc_837_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v___x_835_; 
lean_ctor_set_uint8(v___x_833_, sizeof(void*)*1, v_done_831_);
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 0, v___x_833_);
v___x_835_ = v___x_829_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_827_, 1);
lean_del_object(v___x_824_);
lean_dec_ref(v_e_x27_822_);
return v___x_826_;
}
}
else
{
lean_del_object(v___x_824_);
lean_dec_ref(v_e_x27_822_);
return v___x_826_;
}
}
}
else
{
lean_dec_ref_known(v_a_817_, 1);
lean_dec_ref(v___f_803_);
return v___x_816_;
}
}
}
else
{
lean_dec_ref(v___y_805_);
lean_dec_ref(v___f_803_);
return v___x_816_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__1___boxed(lean_object* v___f_841_, lean_object* v_x_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__1(v___f_841_, v_x_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__2(lean_object* v___f_855_, lean_object* v_x_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
lean_object* v___x_868_; 
lean_inc_ref(v___y_857_);
v___x_868_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v___y_857_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_870_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
v___x_870_ = lean_box(0);
if (lean_obj_tag(v_a_869_) == 0)
{
uint8_t v_done_871_; 
v_done_871_ = lean_ctor_get_uint8(v_a_869_, 0);
lean_dec_ref_known(v_a_869_, 0);
if (v_done_871_ == 0)
{
lean_object* v___x_872_; 
lean_dec_ref_known(v___x_868_, 1);
lean_inc(v___y_866_);
lean_inc_ref(v___y_865_);
lean_inc(v___y_864_);
lean_inc_ref(v___y_863_);
lean_inc(v___y_862_);
lean_inc_ref(v___y_861_);
lean_inc(v___y_860_);
lean_inc_ref(v___y_859_);
lean_inc(v___y_858_);
v___x_872_ = lean_apply_12(v___f_855_, v___x_870_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, lean_box(0));
return v___x_872_;
}
else
{
lean_dec_ref(v___y_857_);
lean_dec_ref(v___f_855_);
return v___x_868_;
}
}
else
{
uint8_t v_done_873_; 
lean_dec_ref(v___y_857_);
v_done_873_ = lean_ctor_get_uint8(v_a_869_, sizeof(void*)*1);
if (v_done_873_ == 0)
{
lean_object* v_e_x27_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_892_; 
lean_dec_ref_known(v___x_868_, 1);
v_e_x27_874_ = lean_ctor_get(v_a_869_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v_a_869_);
if (v_isSharedCheck_892_ == 0)
{
v___x_876_ = v_a_869_;
v_isShared_877_ = v_isSharedCheck_892_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_e_x27_874_);
lean_dec(v_a_869_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_892_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; 
lean_inc(v___y_866_);
lean_inc_ref(v___y_865_);
lean_inc(v___y_864_);
lean_inc_ref(v___y_863_);
lean_inc(v___y_862_);
lean_inc_ref(v___y_861_);
lean_inc(v___y_860_);
lean_inc_ref(v___y_859_);
lean_inc(v___y_858_);
lean_inc_ref(v_e_x27_874_);
v___x_878_ = lean_apply_12(v___f_855_, v___x_870_, v_e_x27_874_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, lean_box(0));
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
if (lean_obj_tag(v_a_879_) == 0)
{
lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_890_; 
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; 
v_unused_891_ = lean_ctor_get(v___x_878_, 0);
lean_dec(v_unused_891_);
v___x_881_ = v___x_878_;
v_isShared_882_ = v_isSharedCheck_890_;
goto v_resetjp_880_;
}
else
{
lean_dec(v___x_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_890_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
uint8_t v_done_883_; lean_object* v___x_885_; 
v_done_883_ = lean_ctor_get_uint8(v_a_879_, 0);
lean_dec_ref_known(v_a_879_, 0);
if (v_isShared_877_ == 0)
{
v___x_885_ = v___x_876_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_e_x27_874_);
v___x_885_ = v_reuseFailAlloc_889_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_887_; 
lean_ctor_set_uint8(v___x_885_, sizeof(void*)*1, v_done_883_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_885_);
v___x_887_ = v___x_881_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_879_, 1);
lean_del_object(v___x_876_);
lean_dec_ref(v_e_x27_874_);
return v___x_878_;
}
}
else
{
lean_del_object(v___x_876_);
lean_dec_ref(v_e_x27_874_);
return v___x_878_;
}
}
}
else
{
lean_dec_ref_known(v_a_869_, 1);
lean_dec_ref(v___f_855_);
return v___x_868_;
}
}
}
else
{
lean_dec_ref(v___y_857_);
lean_dec_ref(v___f_855_);
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__2___boxed(lean_object* v___f_893_, lean_object* v_x_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__2(v___f_893_, v_x_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__4(lean_object* v___x_907_, lean_object* v___f_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; 
lean_inc_ref(v___y_909_);
v___x_920_ = l_Lean_Meta_Sym_DSimp_evalGround___redArg(v___x_907_, v___y_909_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_922_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
v___x_922_ = lean_box(0);
if (lean_obj_tag(v_a_921_) == 0)
{
uint8_t v_done_923_; 
v_done_923_ = lean_ctor_get_uint8(v_a_921_, 0);
lean_dec_ref_known(v_a_921_, 0);
if (v_done_923_ == 0)
{
lean_object* v___x_924_; 
lean_dec_ref_known(v___x_920_, 1);
v___x_924_ = lean_apply_12(v___f_908_, v___x_922_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, lean_box(0));
return v___x_924_;
}
else
{
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec_ref(v___f_908_);
return v___x_920_;
}
}
else
{
uint8_t v_done_925_; 
lean_dec_ref(v___y_909_);
v_done_925_ = lean_ctor_get_uint8(v_a_921_, sizeof(void*)*1);
if (v_done_925_ == 0)
{
lean_object* v_e_x27_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref_known(v___x_920_, 1);
v_e_x27_926_ = lean_ctor_get(v_a_921_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v_a_921_);
if (v_isSharedCheck_944_ == 0)
{
v___x_928_ = v_a_921_;
v_isShared_929_ = v_isSharedCheck_944_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_e_x27_926_);
lean_dec(v_a_921_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_944_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_930_; 
lean_inc_ref(v_e_x27_926_);
v___x_930_ = lean_apply_12(v___f_908_, v___x_922_, v_e_x27_926_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, lean_box(0));
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_931_);
if (lean_obj_tag(v_a_931_) == 0)
{
lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_942_; 
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; 
v_unused_943_ = lean_ctor_get(v___x_930_, 0);
lean_dec(v_unused_943_);
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_942_;
goto v_resetjp_932_;
}
else
{
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_942_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
uint8_t v_done_935_; lean_object* v___x_937_; 
v_done_935_ = lean_ctor_get_uint8(v_a_931_, 0);
lean_dec_ref_known(v_a_931_, 0);
if (v_isShared_929_ == 0)
{
v___x_937_ = v___x_928_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_e_x27_926_);
v___x_937_ = v_reuseFailAlloc_941_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_939_; 
lean_ctor_set_uint8(v___x_937_, sizeof(void*)*1, v_done_935_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_937_);
v___x_939_ = v___x_933_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_931_, 1);
lean_del_object(v___x_928_);
lean_dec_ref(v_e_x27_926_);
return v___x_930_;
}
}
else
{
lean_del_object(v___x_928_);
lean_dec_ref(v_e_x27_926_);
return v___x_930_;
}
}
}
else
{
lean_dec_ref_known(v_a_921_, 1);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___f_908_);
return v___x_920_;
}
}
}
else
{
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec_ref(v___f_908_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__4___boxed(lean_object* v___x_945_, lean_object* v___f_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__4(v___x_945_, v___f_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___x_945_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__6(uint8_t v___x_959_, lean_object* v___f_960_, lean_object* v_____r_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v___x_971_; lean_object* v_rewriteSimpCache_972_; lean_object* v_rewriteDSimpCache_973_; lean_object* v_acCache_974_; lean_object* v_typeAnalysis_975_; lean_object* v_goal_976_; lean_object* v_hypotheses_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_987_; 
v___x_971_ = lean_st_ref_take(v___y_963_);
v_rewriteSimpCache_972_ = lean_ctor_get(v___x_971_, 0);
v_rewriteDSimpCache_973_ = lean_ctor_get(v___x_971_, 1);
v_acCache_974_ = lean_ctor_get(v___x_971_, 2);
v_typeAnalysis_975_ = lean_ctor_get(v___x_971_, 3);
v_goal_976_ = lean_ctor_get(v___x_971_, 4);
v_hypotheses_977_ = lean_ctor_get(v___x_971_, 5);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_987_ == 0)
{
v___x_979_ = v___x_971_;
v_isShared_980_ = v_isSharedCheck_987_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_hypotheses_977_);
lean_inc(v_goal_976_);
lean_inc(v_typeAnalysis_975_);
lean_inc(v_acCache_974_);
lean_inc(v_rewriteDSimpCache_973_);
lean_inc(v_rewriteSimpCache_972_);
lean_dec(v___x_971_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_987_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_rewriteSimpCache_972_);
lean_ctor_set(v_reuseFailAlloc_986_, 1, v_rewriteDSimpCache_973_);
lean_ctor_set(v_reuseFailAlloc_986_, 2, v_acCache_974_);
lean_ctor_set(v_reuseFailAlloc_986_, 3, v_typeAnalysis_975_);
lean_ctor_set(v_reuseFailAlloc_986_, 4, v_goal_976_);
lean_ctor_set(v_reuseFailAlloc_986_, 5, v_hypotheses_977_);
v___x_982_ = v_reuseFailAlloc_986_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*6, v___x_959_);
v___x_983_ = lean_st_ref_set(v___y_963_, v___x_982_);
v___x_984_ = lean_box(0);
lean_inc(v___y_969_);
lean_inc_ref(v___y_968_);
lean_inc(v___y_967_);
lean_inc_ref(v___y_966_);
lean_inc(v___y_965_);
lean_inc_ref(v___y_964_);
lean_inc(v___y_963_);
lean_inc_ref(v___y_962_);
v___x_985_ = lean_apply_10(v___f_960_, v___x_984_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, lean_box(0));
return v___x_985_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__6___boxed(lean_object* v___x_988_, lean_object* v___f_989_, lean_object* v_____r_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
uint8_t v___x_121652__boxed_1000_; lean_object* v_res_1001_; 
v___x_121652__boxed_1000_ = lean_unbox(v___x_988_);
v_res_1001_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__6(v___x_121652__boxed_1000_, v___f_989_, v_____r_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__16_spec__19___redArg(lean_object* v_x_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_){
_start:
{
lean_object* v_ks_1006_; lean_object* v_vs_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1031_; 
v_ks_1006_ = lean_ctor_get(v_x_1002_, 0);
v_vs_1007_ = lean_ctor_get(v_x_1002_, 1);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_x_1002_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1009_ = v_x_1002_;
v_isShared_1010_ = v_isSharedCheck_1031_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_vs_1007_);
lean_inc(v_ks_1006_);
lean_dec(v_x_1002_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1031_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1011_ = lean_array_get_size(v_ks_1006_);
v___x_1012_ = lean_nat_dec_lt(v_x_1003_, v___x_1011_);
if (v___x_1012_ == 0)
{
lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1016_; 
lean_dec(v_x_1003_);
v___x_1013_ = lean_array_push(v_ks_1006_, v_x_1004_);
v___x_1014_ = lean_array_push(v_vs_1007_, v_x_1005_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v___x_1014_);
lean_ctor_set(v___x_1009_, 0, v___x_1013_);
v___x_1016_ = v___x_1009_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
else
{
lean_object* v_k_x27_1018_; uint8_t v___x_1019_; 
v_k_x27_1018_ = lean_array_fget_borrowed(v_ks_1006_, v_x_1003_);
v___x_1019_ = l_Lean_instBEqMVarId_beq(v_x_1004_, v_k_x27_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1021_; 
if (v_isShared_1010_ == 0)
{
v___x_1021_ = v___x_1009_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_ks_1006_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_vs_1007_);
v___x_1021_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = lean_unsigned_to_nat(1u);
v___x_1023_ = lean_nat_add(v_x_1003_, v___x_1022_);
lean_dec(v_x_1003_);
v_x_1002_ = v___x_1021_;
v_x_1003_ = v___x_1023_;
goto _start;
}
}
else
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1026_ = lean_array_fset(v_ks_1006_, v_x_1003_, v_x_1004_);
v___x_1027_ = lean_array_fset(v_vs_1007_, v_x_1003_, v_x_1005_);
lean_dec(v_x_1003_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 1, v___x_1027_);
lean_ctor_set(v___x_1009_, 0, v___x_1026_);
v___x_1029_ = v___x_1009_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v___x_1027_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__16___redArg(lean_object* v_n_1032_, lean_object* v_k_1033_, lean_object* v_v_1034_){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = lean_unsigned_to_nat(0u);
v___x_1036_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__16_spec__19___redArg(v_n_1032_, v___x_1035_, v_k_1033_, v_v_1034_);
return v___x_1036_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg(lean_object* v_x_1038_, size_t v_x_1039_, size_t v_x_1040_, lean_object* v_x_1041_, lean_object* v_x_1042_){
_start:
{
if (lean_obj_tag(v_x_1038_) == 0)
{
lean_object* v_es_1043_; size_t v___x_1044_; size_t v___x_1045_; lean_object* v_j_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_es_1043_ = lean_ctor_get(v_x_1038_, 0);
v___x_1044_ = ((size_t)31ULL);
v___x_1045_ = lean_usize_land(v_x_1039_, v___x_1044_);
v_j_1046_ = lean_usize_to_nat(v___x_1045_);
v___x_1047_ = lean_array_get_size(v_es_1043_);
v___x_1048_ = lean_nat_dec_lt(v_j_1046_, v___x_1047_);
if (v___x_1048_ == 0)
{
lean_dec(v_j_1046_);
lean_dec(v_x_1042_);
lean_dec(v_x_1041_);
return v_x_1038_;
}
else
{
lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1087_; 
lean_inc_ref(v_es_1043_);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_x_1038_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; 
v_unused_1088_ = lean_ctor_get(v_x_1038_, 0);
lean_dec(v_unused_1088_);
v___x_1050_ = v_x_1038_;
v_isShared_1051_ = v_isSharedCheck_1087_;
goto v_resetjp_1049_;
}
else
{
lean_dec(v_x_1038_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1087_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v_v_1052_; lean_object* v___x_1053_; lean_object* v_xs_x27_1054_; lean_object* v___y_1056_; 
v_v_1052_ = lean_array_fget(v_es_1043_, v_j_1046_);
v___x_1053_ = lean_box(0);
v_xs_x27_1054_ = lean_array_fset(v_es_1043_, v_j_1046_, v___x_1053_);
switch(lean_obj_tag(v_v_1052_))
{
case 0:
{
lean_object* v_key_1061_; lean_object* v_val_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1072_; 
v_key_1061_ = lean_ctor_get(v_v_1052_, 0);
v_val_1062_ = lean_ctor_get(v_v_1052_, 1);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_v_1052_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1064_ = v_v_1052_;
v_isShared_1065_ = v_isSharedCheck_1072_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_val_1062_);
lean_inc(v_key_1061_);
lean_dec(v_v_1052_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1072_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
uint8_t v___x_1066_; 
v___x_1066_ = l_Lean_instBEqMVarId_beq(v_x_1041_, v_key_1061_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
lean_del_object(v___x_1064_);
v___x_1067_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1061_, v_val_1062_, v_x_1041_, v_x_1042_);
v___x_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
v___y_1056_ = v___x_1068_;
goto v___jp_1055_;
}
else
{
lean_object* v___x_1070_; 
lean_dec(v_val_1062_);
lean_dec(v_key_1061_);
if (v_isShared_1065_ == 0)
{
lean_ctor_set(v___x_1064_, 1, v_x_1042_);
lean_ctor_set(v___x_1064_, 0, v_x_1041_);
v___x_1070_ = v___x_1064_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_x_1041_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_x_1042_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
v___y_1056_ = v___x_1070_;
goto v___jp_1055_;
}
}
}
}
case 1:
{
lean_object* v_node_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1085_; 
v_node_1073_ = lean_ctor_get(v_v_1052_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_v_1052_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1075_ = v_v_1052_;
v_isShared_1076_ = v_isSharedCheck_1085_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_node_1073_);
lean_dec(v_v_1052_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1085_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
size_t v___x_1077_; size_t v___x_1078_; size_t v___x_1079_; size_t v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1077_ = ((size_t)5ULL);
v___x_1078_ = lean_usize_shift_right(v_x_1039_, v___x_1077_);
v___x_1079_ = ((size_t)1ULL);
v___x_1080_ = lean_usize_add(v_x_1040_, v___x_1079_);
v___x_1081_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg(v_node_1073_, v___x_1078_, v___x_1080_, v_x_1041_, v_x_1042_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1081_);
v___x_1083_ = v___x_1075_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
v___y_1056_ = v___x_1083_;
goto v___jp_1055_;
}
}
}
default: 
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_x_1041_);
lean_ctor_set(v___x_1086_, 1, v_x_1042_);
v___y_1056_ = v___x_1086_;
goto v___jp_1055_;
}
}
v___jp_1055_:
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1057_ = lean_array_fset(v_xs_x27_1054_, v_j_1046_, v___y_1056_);
lean_dec(v_j_1046_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 0, v___x_1057_);
v___x_1059_ = v___x_1050_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
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
else
{
lean_object* v_ks_1089_; lean_object* v_vs_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1110_; 
v_ks_1089_ = lean_ctor_get(v_x_1038_, 0);
v_vs_1090_ = lean_ctor_get(v_x_1038_, 1);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_x_1038_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1092_ = v_x_1038_;
v_isShared_1093_ = v_isSharedCheck_1110_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_vs_1090_);
lean_inc(v_ks_1089_);
lean_dec(v_x_1038_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1110_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_ks_1089_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_vs_1090_);
v___x_1095_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v_newNode_1096_; uint8_t v___y_1098_; size_t v___x_1104_; uint8_t v___x_1105_; 
v_newNode_1096_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__16___redArg(v___x_1095_, v_x_1041_, v_x_1042_);
v___x_1104_ = ((size_t)7ULL);
v___x_1105_ = lean_usize_dec_le(v___x_1104_, v_x_1040_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v___x_1106_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1096_);
v___x_1107_ = lean_unsigned_to_nat(4u);
v___x_1108_ = lean_nat_dec_lt(v___x_1106_, v___x_1107_);
lean_dec(v___x_1106_);
v___y_1098_ = v___x_1108_;
goto v___jp_1097_;
}
else
{
v___y_1098_ = v___x_1105_;
goto v___jp_1097_;
}
v___jp_1097_:
{
if (v___y_1098_ == 0)
{
lean_object* v_ks_1099_; lean_object* v_vs_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_ks_1099_ = lean_ctor_get(v_newNode_1096_, 0);
lean_inc_ref(v_ks_1099_);
v_vs_1100_ = lean_ctor_get(v_newNode_1096_, 1);
lean_inc_ref(v_vs_1100_);
lean_dec_ref(v_newNode_1096_);
v___x_1101_ = lean_unsigned_to_nat(0u);
v___x_1102_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg___closed__0);
v___x_1103_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__17___redArg(v_x_1040_, v_ks_1099_, v_vs_1100_, v___x_1101_, v___x_1102_);
lean_dec_ref(v_vs_1100_);
lean_dec_ref(v_ks_1099_);
return v___x_1103_;
}
else
{
return v_newNode_1096_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__17___redArg(size_t v_depth_1111_, lean_object* v_keys_1112_, lean_object* v_vals_1113_, lean_object* v_i_1114_, lean_object* v_entries_1115_){
_start:
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = lean_array_get_size(v_keys_1112_);
v___x_1117_ = lean_nat_dec_lt(v_i_1114_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_dec(v_i_1114_);
return v_entries_1115_;
}
else
{
lean_object* v_k_1118_; lean_object* v_v_1119_; uint64_t v___x_1120_; size_t v_h_1121_; size_t v___x_1122_; lean_object* v___x_1123_; size_t v___x_1124_; size_t v___x_1125_; size_t v___x_1126_; size_t v_h_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_k_1118_ = lean_array_fget_borrowed(v_keys_1112_, v_i_1114_);
v_v_1119_ = lean_array_fget_borrowed(v_vals_1113_, v_i_1114_);
v___x_1120_ = l_Lean_instHashableMVarId_hash(v_k_1118_);
v_h_1121_ = lean_uint64_to_usize(v___x_1120_);
v___x_1122_ = ((size_t)5ULL);
v___x_1123_ = lean_unsigned_to_nat(1u);
v___x_1124_ = ((size_t)1ULL);
v___x_1125_ = lean_usize_sub(v_depth_1111_, v___x_1124_);
v___x_1126_ = lean_usize_mul(v___x_1122_, v___x_1125_);
v_h_1127_ = lean_usize_shift_right(v_h_1121_, v___x_1126_);
v___x_1128_ = lean_nat_add(v_i_1114_, v___x_1123_);
lean_dec(v_i_1114_);
lean_inc(v_v_1119_);
lean_inc(v_k_1118_);
v___x_1129_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg(v_entries_1115_, v_h_1127_, v_depth_1111_, v_k_1118_, v_v_1119_);
v_i_1114_ = v___x_1128_;
v_entries_1115_ = v___x_1129_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__17___redArg___boxed(lean_object* v_depth_1131_, lean_object* v_keys_1132_, lean_object* v_vals_1133_, lean_object* v_i_1134_, lean_object* v_entries_1135_){
_start:
{
size_t v_depth_boxed_1136_; lean_object* v_res_1137_; 
v_depth_boxed_1136_ = lean_unbox_usize(v_depth_1131_);
lean_dec(v_depth_1131_);
v_res_1137_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__17___redArg(v_depth_boxed_1136_, v_keys_1132_, v_vals_1133_, v_i_1134_, v_entries_1135_);
lean_dec_ref(v_vals_1133_);
lean_dec_ref(v_keys_1132_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_x_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_){
_start:
{
size_t v_x_121787__boxed_1143_; size_t v_x_121788__boxed_1144_; lean_object* v_res_1145_; 
v_x_121787__boxed_1143_ = lean_unbox_usize(v_x_1139_);
lean_dec(v_x_1139_);
v_x_121788__boxed_1144_ = lean_unbox_usize(v_x_1140_);
lean_dec(v_x_1140_);
v_res_1145_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg(v_x_1138_, v_x_121787__boxed_1143_, v_x_121788__boxed_1144_, v_x_1141_, v_x_1142_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2___redArg(lean_object* v_x_1146_, lean_object* v_x_1147_, lean_object* v_x_1148_){
_start:
{
uint64_t v___x_1149_; size_t v___x_1150_; size_t v___x_1151_; lean_object* v___x_1152_; 
v___x_1149_ = l_Lean_instHashableMVarId_hash(v_x_1147_);
v___x_1150_ = lean_uint64_to_usize(v___x_1149_);
v___x_1151_ = ((size_t)1ULL);
v___x_1152_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg(v_x_1146_, v___x_1150_, v___x_1151_, v_x_1147_, v_x_1148_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(lean_object* v_mvarId_1153_, lean_object* v_val_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v___x_1157_; lean_object* v_mctx_1158_; lean_object* v_cache_1159_; lean_object* v_zetaDeltaFVarIds_1160_; lean_object* v_postponed_1161_; lean_object* v_diag_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1190_; 
v___x_1157_ = lean_st_ref_take(v___y_1155_);
v_mctx_1158_ = lean_ctor_get(v___x_1157_, 0);
v_cache_1159_ = lean_ctor_get(v___x_1157_, 1);
v_zetaDeltaFVarIds_1160_ = lean_ctor_get(v___x_1157_, 2);
v_postponed_1161_ = lean_ctor_get(v___x_1157_, 3);
v_diag_1162_ = lean_ctor_get(v___x_1157_, 4);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1164_ = v___x_1157_;
v_isShared_1165_ = v_isSharedCheck_1190_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_diag_1162_);
lean_inc(v_postponed_1161_);
lean_inc(v_zetaDeltaFVarIds_1160_);
lean_inc(v_cache_1159_);
lean_inc(v_mctx_1158_);
lean_dec(v___x_1157_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1190_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v_depth_1166_; lean_object* v_levelAssignDepth_1167_; lean_object* v_lmvarCounter_1168_; lean_object* v_mvarCounter_1169_; lean_object* v_lDecls_1170_; lean_object* v_decls_1171_; lean_object* v_userNames_1172_; lean_object* v_lAssignment_1173_; lean_object* v_eAssignment_1174_; lean_object* v_dAssignment_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1189_; 
v_depth_1166_ = lean_ctor_get(v_mctx_1158_, 0);
v_levelAssignDepth_1167_ = lean_ctor_get(v_mctx_1158_, 1);
v_lmvarCounter_1168_ = lean_ctor_get(v_mctx_1158_, 2);
v_mvarCounter_1169_ = lean_ctor_get(v_mctx_1158_, 3);
v_lDecls_1170_ = lean_ctor_get(v_mctx_1158_, 4);
v_decls_1171_ = lean_ctor_get(v_mctx_1158_, 5);
v_userNames_1172_ = lean_ctor_get(v_mctx_1158_, 6);
v_lAssignment_1173_ = lean_ctor_get(v_mctx_1158_, 7);
v_eAssignment_1174_ = lean_ctor_get(v_mctx_1158_, 8);
v_dAssignment_1175_ = lean_ctor_get(v_mctx_1158_, 9);
v_isSharedCheck_1189_ = !lean_is_exclusive(v_mctx_1158_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1177_ = v_mctx_1158_;
v_isShared_1178_ = v_isSharedCheck_1189_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_dAssignment_1175_);
lean_inc(v_eAssignment_1174_);
lean_inc(v_lAssignment_1173_);
lean_inc(v_userNames_1172_);
lean_inc(v_decls_1171_);
lean_inc(v_lDecls_1170_);
lean_inc(v_mvarCounter_1169_);
lean_inc(v_lmvarCounter_1168_);
lean_inc(v_levelAssignDepth_1167_);
lean_inc(v_depth_1166_);
lean_dec(v_mctx_1158_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1189_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2___redArg(v_eAssignment_1174_, v_mvarId_1153_, v_val_1154_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 8, v___x_1179_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_depth_1166_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_levelAssignDepth_1167_);
lean_ctor_set(v_reuseFailAlloc_1188_, 2, v_lmvarCounter_1168_);
lean_ctor_set(v_reuseFailAlloc_1188_, 3, v_mvarCounter_1169_);
lean_ctor_set(v_reuseFailAlloc_1188_, 4, v_lDecls_1170_);
lean_ctor_set(v_reuseFailAlloc_1188_, 5, v_decls_1171_);
lean_ctor_set(v_reuseFailAlloc_1188_, 6, v_userNames_1172_);
lean_ctor_set(v_reuseFailAlloc_1188_, 7, v_lAssignment_1173_);
lean_ctor_set(v_reuseFailAlloc_1188_, 8, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1188_, 9, v_dAssignment_1175_);
v___x_1181_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1183_; 
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1181_);
v___x_1183_ = v___x_1164_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1181_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_cache_1159_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v_zetaDeltaFVarIds_1160_);
lean_ctor_set(v_reuseFailAlloc_1187_, 3, v_postponed_1161_);
lean_ctor_set(v_reuseFailAlloc_1187_, 4, v_diag_1162_);
v___x_1183_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1184_ = lean_st_ref_set(v___y_1155_, v___x_1183_);
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
return v___x_1186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg___boxed(lean_object* v_mvarId_1191_, lean_object* v_val_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v_mvarId_1191_, v_val_1192_, v___y_1193_);
lean_dec(v___y_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0(lean_object* v_x_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v___x_1208_; 
lean_inc_ref(v___y_1197_);
v___x_1208_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_1197_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1209_);
if (lean_obj_tag(v_a_1209_) == 0)
{
uint8_t v_done_1210_; 
v_done_1210_ = lean_ctor_get_uint8(v_a_1209_, 0);
lean_dec_ref_known(v_a_1209_, 0);
if (v_done_1210_ == 0)
{
lean_object* v___x_1211_; 
lean_dec_ref_known(v___x_1208_, 1);
v___x_1211_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteDsimproc___redArg(v___y_1197_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
return v___x_1211_;
}
else
{
lean_dec_ref(v___y_1197_);
return v___x_1208_;
}
}
else
{
uint8_t v_done_1212_; 
lean_dec_ref(v___y_1197_);
v_done_1212_ = lean_ctor_get_uint8(v_a_1209_, sizeof(void*)*1);
if (v_done_1212_ == 0)
{
lean_object* v_e_x27_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1231_; 
lean_dec_ref_known(v___x_1208_, 1);
v_e_x27_1213_ = lean_ctor_get(v_a_1209_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_a_1209_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1215_ = v_a_1209_;
v_isShared_1216_ = v_isSharedCheck_1231_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_e_x27_1213_);
lean_dec(v_a_1209_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1231_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; 
lean_inc_ref(v_e_x27_1213_);
v___x_1217_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteDsimproc___redArg(v_e_x27_1213_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
if (lean_obj_tag(v_a_1218_) == 0)
{
lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1229_; 
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; 
v_unused_1230_ = lean_ctor_get(v___x_1217_, 0);
lean_dec(v_unused_1230_);
v___x_1220_ = v___x_1217_;
v_isShared_1221_ = v_isSharedCheck_1229_;
goto v_resetjp_1219_;
}
else
{
lean_dec(v___x_1217_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1229_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
uint8_t v_done_1222_; lean_object* v___x_1224_; 
v_done_1222_ = lean_ctor_get_uint8(v_a_1218_, 0);
lean_dec_ref_known(v_a_1218_, 0);
if (v_isShared_1216_ == 0)
{
v___x_1224_ = v___x_1215_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_e_x27_1213_);
v___x_1224_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1226_; 
lean_ctor_set_uint8(v___x_1224_, sizeof(void*)*1, v_done_1222_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1224_);
v___x_1226_ = v___x_1220_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v___x_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_1218_, 1);
lean_del_object(v___x_1215_);
lean_dec_ref(v_e_x27_1213_);
return v___x_1217_;
}
}
else
{
lean_del_object(v___x_1215_);
lean_dec_ref(v_e_x27_1213_);
return v___x_1217_;
}
}
}
else
{
lean_dec_ref_known(v_a_1209_, 1);
return v___x_1208_;
}
}
}
else
{
lean_dec_ref(v___y_1197_);
return v___x_1208_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0___boxed(lean_object* v_x_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__0(v_x_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
return v_res_1244_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__9));
v___x_1268_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__11));
v___x_1269_ = l_Lean_Name_append(v___x_1268_, v___x_1267_);
return v___x_1269_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__14(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__13));
v___x_1272_ = l_Lean_stringToMessageData(v___x_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg(lean_object* v_upperBound_1273_, lean_object* v___x_1274_, lean_object* v___x_1275_, lean_object* v___x_1276_, lean_object* v___x_1277_, lean_object* v_a_1278_, lean_object* v_b_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___y_1290_; lean_object* v___y_1313_; uint8_t v___x_1316_; 
v___x_1316_ = lean_nat_dec_lt(v_a_1278_, v_upperBound_1273_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; 
lean_dec(v_a_1278_);
lean_dec_ref(v___x_1277_);
lean_dec_ref(v___x_1276_);
lean_dec_ref(v___x_1275_);
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v_b_1279_);
return v___x_1317_;
}
else
{
lean_object* v_snd_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1399_; 
v_snd_1318_ = lean_ctor_get(v_b_1279_, 1);
v_isSharedCheck_1399_ = !lean_is_exclusive(v_b_1279_);
if (v_isSharedCheck_1399_ == 0)
{
lean_object* v_unused_1400_; 
v_unused_1400_ = lean_ctor_get(v_b_1279_, 0);
lean_dec(v_unused_1400_);
v___x_1320_ = v_b_1279_;
v_isShared_1321_ = v_isSharedCheck_1399_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_snd_1318_);
lean_dec(v_b_1279_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1399_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1352_; lean_object* v___x_1396_; 
v___x_1322_ = lean_box(0);
v___x_1323_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__5));
v___x_1324_ = lean_array_fget_borrowed(v___x_1274_, v_a_1278_);
lean_inc(v___x_1324_);
lean_inc_ref(v___x_1275_);
v___x_1396_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_dsimp___redArg(v___x_1323_, v___x_1275_, v___x_1324_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1398_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
lean_dec_ref_known(v___x_1396_, 1);
lean_inc_ref(v___x_1277_);
lean_inc_ref(v___x_1276_);
v___x_1398_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_Rewrite_0__Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_simp___redArg(v___x_1276_, v___x_1277_, v_a_1397_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
v___y_1352_ = v___x_1398_;
goto v___jp_1351_;
}
else
{
v___y_1352_ = v___x_1396_;
goto v___jp_1351_;
}
v___jp_1325_:
{
lean_object* v_options_1328_; uint8_t v_hasTrace_1329_; 
v_options_1328_ = lean_ctor_get(v___y_1286_, 2);
v_hasTrace_1329_ = lean_ctor_get_uint8(v_options_1328_, sizeof(void*)*1);
if (v_hasTrace_1329_ == 0)
{
lean_dec_ref(v___y_1326_);
v___y_1313_ = v___y_1327_;
goto v___jp_1312_;
}
else
{
lean_object* v_inheritedTraceOptions_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v_inheritedTraceOptions_1330_ = lean_ctor_get(v___y_1286_, 13);
v___x_1331_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__9));
v___x_1332_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12);
v___x_1333_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1330_, v_options_1328_, v___x_1332_);
if (v___x_1333_ == 0)
{
lean_dec_ref(v___y_1326_);
v___y_1313_ = v___y_1327_;
goto v___jp_1312_;
}
else
{
lean_object* v_type_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v_type_1334_ = lean_ctor_get(v___x_1324_, 1);
lean_inc_ref(v_type_1334_);
v___x_1335_ = l_Lean_MessageData_ofExpr(v_type_1334_);
v___x_1336_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__14, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__14_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__14);
v___x_1337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1335_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = l_Lean_MessageData_ofExpr(v___y_1326_);
v___x_1339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1337_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
v___x_1340_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v___x_1331_, v___x_1339_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v_a_1341_; lean_object* v___x_1342_; 
v_a_1341_ = lean_ctor_get(v___x_1340_, 0);
lean_inc(v_a_1341_);
lean_dec_ref_known(v___x_1340_, 1);
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
lean_inc(v___y_1285_);
lean_inc_ref(v___y_1284_);
lean_inc(v___y_1283_);
lean_inc_ref(v___y_1282_);
lean_inc(v___y_1281_);
lean_inc_ref(v___y_1280_);
v___x_1342_ = lean_apply_10(v___y_1327_, v_a_1341_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, lean_box(0));
v___y_1290_ = v___x_1342_;
goto v___jp_1289_;
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec_ref(v___y_1327_);
lean_dec(v_a_1278_);
lean_dec_ref(v___x_1277_);
lean_dec_ref(v___x_1276_);
lean_dec_ref(v___x_1275_);
v_a_1343_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1340_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1340_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
}
v___jp_1351_:
{
if (lean_obj_tag(v___y_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v_type_1354_; lean_object* v_value_1355_; uint8_t v___x_1356_; 
v_a_1353_ = lean_ctor_get(v___y_1352_, 0);
lean_inc(v_a_1353_);
lean_dec_ref_known(v___y_1352_, 1);
v_type_1354_ = lean_ctor_get(v_a_1353_, 1);
v_value_1355_ = lean_ctor_get(v_a_1353_, 2);
lean_inc_ref(v_type_1354_);
v___x_1356_ = l_Lean_Expr_isFalse(v_type_1354_);
if (v___x_1356_ == 0)
{
lean_object* v_type_1357_; lean_object* v___f_1358_; lean_object* v___x_1359_; lean_object* v___f_1360_; uint8_t v___x_1361_; 
lean_del_object(v___x_1320_);
v_type_1357_ = lean_ctor_get(v___x_1324_, 1);
lean_inc(v_a_1353_);
lean_inc(v_snd_1318_);
v___f_1358_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__5___boxed), 13, 3);
lean_closure_set(v___f_1358_, 0, v_snd_1318_);
lean_closure_set(v___f_1358_, 1, v_a_1353_);
lean_closure_set(v___f_1358_, 2, v___x_1322_);
v___x_1359_ = lean_box(v___x_1316_);
v___f_1360_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__6___boxed), 12, 2);
lean_closure_set(v___f_1360_, 0, v___x_1359_);
lean_closure_set(v___f_1360_, 1, v___f_1358_);
v___x_1361_ = lean_expr_eqv(v_type_1357_, v_type_1354_);
if (v___x_1361_ == 0)
{
lean_inc_ref(v_type_1354_);
lean_dec(v_a_1353_);
lean_dec(v_snd_1318_);
v___y_1326_ = v_type_1354_;
v___y_1327_ = v___f_1360_;
goto v___jp_1325_;
}
else
{
if (v___x_1356_ == 0)
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
lean_dec_ref(v___f_1360_);
v___x_1362_ = lean_box(0);
v___x_1363_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___lam__5(v_snd_1318_, v_a_1353_, v___x_1322_, v___x_1362_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
v___y_1290_ = v___x_1363_;
goto v___jp_1289_;
}
else
{
lean_inc_ref(v_type_1354_);
lean_dec(v_a_1353_);
lean_dec(v_snd_1318_);
v___y_1326_ = v_type_1354_;
v___y_1327_ = v___f_1360_;
goto v___jp_1325_;
}
}
}
else
{
lean_object* v___x_1364_; lean_object* v_goal_1365_; lean_object* v___x_1366_; 
lean_inc_ref(v_value_1355_);
lean_dec(v_a_1353_);
lean_dec(v_a_1278_);
lean_dec_ref(v___x_1277_);
lean_dec_ref(v___x_1276_);
lean_dec_ref(v___x_1275_);
v___x_1364_ = lean_st_ref_get(v___y_1281_);
v_goal_1365_ = lean_ctor_get(v___x_1364_, 4);
lean_inc(v_goal_1365_);
lean_dec(v___x_1364_);
v___x_1366_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v_goal_1365_, v_value_1355_, v___y_1285_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1378_; 
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v___x_1366_, 0);
lean_dec(v_unused_1379_);
v___x_1368_ = v___x_1366_;
v_isShared_1369_ = v_isSharedCheck_1378_;
goto v_resetjp_1367_;
}
else
{
lean_dec(v___x_1366_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1378_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1370_ = lean_box(v___x_1356_);
v___x_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 0, v___x_1371_);
v___x_1373_ = v___x_1320_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_snd_1318_);
v___x_1373_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1375_; 
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v___x_1373_);
v___x_1375_ = v___x_1368_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_del_object(v___x_1320_);
lean_dec(v_snd_1318_);
v_a_1380_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1366_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1366_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_del_object(v___x_1320_);
lean_dec(v_snd_1318_);
lean_dec(v_a_1278_);
lean_dec_ref(v___x_1277_);
lean_dec_ref(v___x_1276_);
lean_dec_ref(v___x_1275_);
v_a_1388_ = lean_ctor_get(v___y_1352_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___y_1352_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___y_1352_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___y_1352_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
}
}
v___jp_1289_:
{
if (lean_obj_tag(v___y_1290_) == 0)
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1303_; 
v_a_1291_ = lean_ctor_get(v___y_1290_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___y_1290_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1293_ = v___y_1290_;
v_isShared_1294_ = v_isSharedCheck_1303_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___y_1290_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1303_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
if (lean_obj_tag(v_a_1291_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1297_; 
lean_dec(v_a_1278_);
lean_dec_ref(v___x_1277_);
lean_dec_ref(v___x_1276_);
lean_dec_ref(v___x_1275_);
v_a_1295_ = lean_ctor_get(v_a_1291_, 0);
lean_inc(v_a_1295_);
lean_dec_ref_known(v_a_1291_, 1);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v_a_1295_);
v___x_1297_ = v___x_1293_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_del_object(v___x_1293_);
v_a_1299_ = lean_ctor_get(v_a_1291_, 0);
lean_inc(v_a_1299_);
lean_dec_ref_known(v_a_1291_, 1);
v___x_1300_ = lean_unsigned_to_nat(1u);
v___x_1301_ = lean_nat_add(v_a_1278_, v___x_1300_);
lean_dec(v_a_1278_);
v_a_1278_ = v___x_1301_;
v_b_1279_ = v_a_1299_;
goto _start;
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v_a_1278_);
lean_dec_ref(v___x_1277_);
lean_dec_ref(v___x_1276_);
lean_dec_ref(v___x_1275_);
v_a_1304_ = lean_ctor_get(v___y_1290_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___y_1290_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___y_1290_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___y_1290_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
v___jp_1312_:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_box(0);
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
lean_inc(v___y_1285_);
lean_inc_ref(v___y_1284_);
lean_inc(v___y_1283_);
lean_inc_ref(v___y_1282_);
lean_inc(v___y_1281_);
lean_inc_ref(v___y_1280_);
v___x_1315_ = lean_apply_10(v___y_1313_, v___x_1314_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, lean_box(0));
v___y_1290_ = v___x_1315_;
goto v___jp_1289_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___boxed(lean_object* v_upperBound_1401_, lean_object* v___x_1402_, lean_object* v___x_1403_, lean_object* v___x_1404_, lean_object* v___x_1405_, lean_object* v_a_1406_, lean_object* v_b_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg(v_upperBound_1401_, v___x_1402_, v___x_1403_, v___x_1404_, v___x_1405_, v_a_1406_, v_b_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec_ref(v___x_1402_);
lean_dec(v_upperBound_1401_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4(lean_object* v___x_1418_, lean_object* v___x_1419_, lean_object* v___x_1420_, lean_object* v___x_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1431_; lean_object* v_hypotheses_1432_; lean_object* v___x_1433_; lean_object* v_newHyps_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1431_ = lean_st_ref_get(v___y_1423_);
v_hypotheses_1432_ = lean_ctor_get(v___x_1431_, 5);
lean_inc_ref(v_hypotheses_1432_);
lean_dec(v___x_1431_);
v___x_1433_ = lean_array_get_size(v_hypotheses_1432_);
v_newHyps_1434_ = lean_mk_empty_array_with_capacity(v___x_1433_);
v___x_1435_ = lean_box(0);
v___x_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
lean_ctor_set(v___x_1436_, 1, v_newHyps_1434_);
v___x_1437_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg(v___x_1433_, v_hypotheses_1432_, v___x_1418_, v___x_1419_, v___x_1420_, v___x_1421_, v___x_1436_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec_ref(v_hypotheses_1432_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1469_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1440_ = v___x_1437_;
v_isShared_1441_ = v_isSharedCheck_1469_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1437_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1469_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v_fst_1442_; 
v_fst_1442_ = lean_ctor_get(v_a_1438_, 0);
if (lean_obj_tag(v_fst_1442_) == 0)
{
lean_object* v_snd_1443_; lean_object* v___x_1444_; lean_object* v_rewriteSimpCache_1445_; lean_object* v_rewriteDSimpCache_1446_; lean_object* v_acCache_1447_; lean_object* v_typeAnalysis_1448_; lean_object* v_goal_1449_; uint8_t v_didChange_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1463_; 
v_snd_1443_ = lean_ctor_get(v_a_1438_, 1);
lean_inc(v_snd_1443_);
lean_dec(v_a_1438_);
v___x_1444_ = lean_st_ref_take(v___y_1423_);
v_rewriteSimpCache_1445_ = lean_ctor_get(v___x_1444_, 0);
v_rewriteDSimpCache_1446_ = lean_ctor_get(v___x_1444_, 1);
v_acCache_1447_ = lean_ctor_get(v___x_1444_, 2);
v_typeAnalysis_1448_ = lean_ctor_get(v___x_1444_, 3);
v_goal_1449_ = lean_ctor_get(v___x_1444_, 4);
v_didChange_1450_ = lean_ctor_get_uint8(v___x_1444_, sizeof(void*)*6);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v___x_1444_, 5);
lean_dec(v_unused_1464_);
v___x_1452_ = v___x_1444_;
v_isShared_1453_ = v_isSharedCheck_1463_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_goal_1449_);
lean_inc(v_typeAnalysis_1448_);
lean_inc(v_acCache_1447_);
lean_inc(v_rewriteDSimpCache_1446_);
lean_inc(v_rewriteSimpCache_1445_);
lean_dec(v___x_1444_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1463_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 5, v_snd_1443_);
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_rewriteSimpCache_1445_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_rewriteDSimpCache_1446_);
lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_acCache_1447_);
lean_ctor_set(v_reuseFailAlloc_1462_, 3, v_typeAnalysis_1448_);
lean_ctor_set(v_reuseFailAlloc_1462_, 4, v_goal_1449_);
lean_ctor_set(v_reuseFailAlloc_1462_, 5, v_snd_1443_);
lean_ctor_set_uint8(v_reuseFailAlloc_1462_, sizeof(void*)*6, v_didChange_1450_);
v___x_1455_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1456_; uint8_t v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1456_ = lean_st_ref_set(v___y_1423_, v___x_1455_);
v___x_1457_ = 0;
v___x_1458_ = lean_box(v___x_1457_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1458_);
v___x_1460_ = v___x_1440_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
else
{
lean_object* v_val_1465_; lean_object* v___x_1467_; 
lean_inc_ref(v_fst_1442_);
lean_dec(v_a_1438_);
v_val_1465_ = lean_ctor_get(v_fst_1442_, 0);
lean_inc(v_val_1465_);
lean_dec_ref_known(v_fst_1442_, 1);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v_val_1465_);
v___x_1467_ = v___x_1440_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_val_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
}
else
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
v_a_1470_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1437_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1437_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4___boxed(lean_object* v___x_1478_, lean_object* v___x_1479_, lean_object* v___x_1480_, lean_object* v___x_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4(v___x_1478_, v___x_1479_, v___x_1480_, v___x_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9_spec__11(size_t v_sz_1492_, size_t v_i_1493_, lean_object* v_bs_1494_){
_start:
{
uint8_t v___x_1495_; 
v___x_1495_ = lean_usize_dec_lt(v_i_1493_, v_sz_1492_);
if (v___x_1495_ == 0)
{
return v_bs_1494_;
}
else
{
lean_object* v_v_1496_; lean_object* v_msg_1497_; lean_object* v___x_1498_; lean_object* v_bs_x27_1499_; size_t v___x_1500_; size_t v___x_1501_; lean_object* v___x_1502_; 
v_v_1496_ = lean_array_uget_borrowed(v_bs_1494_, v_i_1493_);
v_msg_1497_ = lean_ctor_get(v_v_1496_, 1);
lean_inc_ref(v_msg_1497_);
v___x_1498_ = lean_unsigned_to_nat(0u);
v_bs_x27_1499_ = lean_array_uset(v_bs_1494_, v_i_1493_, v___x_1498_);
v___x_1500_ = ((size_t)1ULL);
v___x_1501_ = lean_usize_add(v_i_1493_, v___x_1500_);
v___x_1502_ = lean_array_uset(v_bs_x27_1499_, v_i_1493_, v_msg_1497_);
v_i_1493_ = v___x_1501_;
v_bs_1494_ = v___x_1502_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9_spec__11___boxed(lean_object* v_sz_1504_, lean_object* v_i_1505_, lean_object* v_bs_1506_){
_start:
{
size_t v_sz_boxed_1507_; size_t v_i_boxed_1508_; lean_object* v_res_1509_; 
v_sz_boxed_1507_ = lean_unbox_usize(v_sz_1504_);
lean_dec(v_sz_1504_);
v_i_boxed_1508_ = lean_unbox_usize(v_i_1505_);
lean_dec(v_i_1505_);
v_res_1509_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9_spec__11(v_sz_boxed_1507_, v_i_boxed_1508_, v_bs_1506_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9___redArg(lean_object* v_oldTraces_1510_, lean_object* v_data_1511_, lean_object* v_ref_1512_, lean_object* v_msg_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_fileName_1519_; lean_object* v_fileMap_1520_; lean_object* v_options_1521_; lean_object* v_currRecDepth_1522_; lean_object* v_maxRecDepth_1523_; lean_object* v_ref_1524_; lean_object* v_currNamespace_1525_; lean_object* v_openDecls_1526_; lean_object* v_initHeartbeats_1527_; lean_object* v_maxHeartbeats_1528_; lean_object* v_quotContext_1529_; lean_object* v_currMacroScope_1530_; uint8_t v_diag_1531_; lean_object* v_cancelTk_x3f_1532_; uint8_t v_suppressElabErrors_1533_; lean_object* v_inheritedTraceOptions_1534_; lean_object* v___x_1535_; lean_object* v_traceState_1536_; lean_object* v_traces_1537_; lean_object* v_ref_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; size_t v_sz_1541_; size_t v___x_1542_; lean_object* v___x_1543_; lean_object* v_msg_1544_; lean_object* v___x_1545_; lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1583_; 
v_fileName_1519_ = lean_ctor_get(v___y_1516_, 0);
v_fileMap_1520_ = lean_ctor_get(v___y_1516_, 1);
v_options_1521_ = lean_ctor_get(v___y_1516_, 2);
v_currRecDepth_1522_ = lean_ctor_get(v___y_1516_, 3);
v_maxRecDepth_1523_ = lean_ctor_get(v___y_1516_, 4);
v_ref_1524_ = lean_ctor_get(v___y_1516_, 5);
v_currNamespace_1525_ = lean_ctor_get(v___y_1516_, 6);
v_openDecls_1526_ = lean_ctor_get(v___y_1516_, 7);
v_initHeartbeats_1527_ = lean_ctor_get(v___y_1516_, 8);
v_maxHeartbeats_1528_ = lean_ctor_get(v___y_1516_, 9);
v_quotContext_1529_ = lean_ctor_get(v___y_1516_, 10);
v_currMacroScope_1530_ = lean_ctor_get(v___y_1516_, 11);
v_diag_1531_ = lean_ctor_get_uint8(v___y_1516_, sizeof(void*)*14);
v_cancelTk_x3f_1532_ = lean_ctor_get(v___y_1516_, 12);
v_suppressElabErrors_1533_ = lean_ctor_get_uint8(v___y_1516_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1534_ = lean_ctor_get(v___y_1516_, 13);
v___x_1535_ = lean_st_ref_get(v___y_1517_);
v_traceState_1536_ = lean_ctor_get(v___x_1535_, 4);
lean_inc_ref(v_traceState_1536_);
lean_dec(v___x_1535_);
v_traces_1537_ = lean_ctor_get(v_traceState_1536_, 0);
lean_inc_ref(v_traces_1537_);
lean_dec_ref(v_traceState_1536_);
v_ref_1538_ = l_Lean_replaceRef(v_ref_1512_, v_ref_1524_);
lean_inc_ref(v_inheritedTraceOptions_1534_);
lean_inc(v_cancelTk_x3f_1532_);
lean_inc(v_currMacroScope_1530_);
lean_inc(v_quotContext_1529_);
lean_inc(v_maxHeartbeats_1528_);
lean_inc(v_initHeartbeats_1527_);
lean_inc(v_openDecls_1526_);
lean_inc(v_currNamespace_1525_);
lean_inc(v_maxRecDepth_1523_);
lean_inc(v_currRecDepth_1522_);
lean_inc_ref(v_options_1521_);
lean_inc_ref(v_fileMap_1520_);
lean_inc_ref(v_fileName_1519_);
v___x_1539_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1539_, 0, v_fileName_1519_);
lean_ctor_set(v___x_1539_, 1, v_fileMap_1520_);
lean_ctor_set(v___x_1539_, 2, v_options_1521_);
lean_ctor_set(v___x_1539_, 3, v_currRecDepth_1522_);
lean_ctor_set(v___x_1539_, 4, v_maxRecDepth_1523_);
lean_ctor_set(v___x_1539_, 5, v_ref_1538_);
lean_ctor_set(v___x_1539_, 6, v_currNamespace_1525_);
lean_ctor_set(v___x_1539_, 7, v_openDecls_1526_);
lean_ctor_set(v___x_1539_, 8, v_initHeartbeats_1527_);
lean_ctor_set(v___x_1539_, 9, v_maxHeartbeats_1528_);
lean_ctor_set(v___x_1539_, 10, v_quotContext_1529_);
lean_ctor_set(v___x_1539_, 11, v_currMacroScope_1530_);
lean_ctor_set(v___x_1539_, 12, v_cancelTk_x3f_1532_);
lean_ctor_set(v___x_1539_, 13, v_inheritedTraceOptions_1534_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*14, v_diag_1531_);
lean_ctor_set_uint8(v___x_1539_, sizeof(void*)*14 + 1, v_suppressElabErrors_1533_);
v___x_1540_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1537_);
lean_dec_ref(v_traces_1537_);
v_sz_1541_ = lean_array_size(v___x_1540_);
v___x_1542_ = ((size_t)0ULL);
v___x_1543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9_spec__11(v_sz_1541_, v___x_1542_, v___x_1540_);
v_msg_1544_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1544_, 0, v_data_1511_);
lean_ctor_set(v_msg_1544_, 1, v_msg_1513_);
lean_ctor_set(v_msg_1544_, 2, v___x_1543_);
v___x_1545_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0_spec__0(v_msg_1544_, v___y_1514_, v___y_1515_, v___x_1539_, v___y_1517_);
lean_dec_ref_known(v___x_1539_, 14);
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1548_ = v___x_1545_;
v_isShared_1549_ = v_isSharedCheck_1583_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1545_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1583_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1550_; lean_object* v_traceState_1551_; lean_object* v_env_1552_; lean_object* v_nextMacroScope_1553_; lean_object* v_ngen_1554_; lean_object* v_auxDeclNGen_1555_; lean_object* v_cache_1556_; lean_object* v_messages_1557_; lean_object* v_infoState_1558_; lean_object* v_snapshotTasks_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1582_; 
v___x_1550_ = lean_st_ref_take(v___y_1517_);
v_traceState_1551_ = lean_ctor_get(v___x_1550_, 4);
v_env_1552_ = lean_ctor_get(v___x_1550_, 0);
v_nextMacroScope_1553_ = lean_ctor_get(v___x_1550_, 1);
v_ngen_1554_ = lean_ctor_get(v___x_1550_, 2);
v_auxDeclNGen_1555_ = lean_ctor_get(v___x_1550_, 3);
v_cache_1556_ = lean_ctor_get(v___x_1550_, 5);
v_messages_1557_ = lean_ctor_get(v___x_1550_, 6);
v_infoState_1558_ = lean_ctor_get(v___x_1550_, 7);
v_snapshotTasks_1559_ = lean_ctor_get(v___x_1550_, 8);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1561_ = v___x_1550_;
v_isShared_1562_ = v_isSharedCheck_1582_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_snapshotTasks_1559_);
lean_inc(v_infoState_1558_);
lean_inc(v_messages_1557_);
lean_inc(v_cache_1556_);
lean_inc(v_traceState_1551_);
lean_inc(v_auxDeclNGen_1555_);
lean_inc(v_ngen_1554_);
lean_inc(v_nextMacroScope_1553_);
lean_inc(v_env_1552_);
lean_dec(v___x_1550_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1582_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
uint64_t v_tid_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1580_; 
v_tid_1563_ = lean_ctor_get_uint64(v_traceState_1551_, sizeof(void*)*1);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_traceState_1551_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; 
v_unused_1581_ = lean_ctor_get(v_traceState_1551_, 0);
lean_dec(v_unused_1581_);
v___x_1565_ = v_traceState_1551_;
v_isShared_1566_ = v_isSharedCheck_1580_;
goto v_resetjp_1564_;
}
else
{
lean_dec(v_traceState_1551_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1580_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1567_, 0, v_ref_1512_);
lean_ctor_set(v___x_1567_, 1, v_a_1546_);
v___x_1568_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1510_, v___x_1567_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 0, v___x_1568_);
v___x_1570_ = v___x_1565_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1568_);
lean_ctor_set_uint64(v_reuseFailAlloc_1579_, sizeof(void*)*1, v_tid_1563_);
v___x_1570_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
lean_object* v___x_1572_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 4, v___x_1570_);
v___x_1572_ = v___x_1561_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_env_1552_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_nextMacroScope_1553_);
lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_ngen_1554_);
lean_ctor_set(v_reuseFailAlloc_1578_, 3, v_auxDeclNGen_1555_);
lean_ctor_set(v_reuseFailAlloc_1578_, 4, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1578_, 5, v_cache_1556_);
lean_ctor_set(v_reuseFailAlloc_1578_, 6, v_messages_1557_);
lean_ctor_set(v_reuseFailAlloc_1578_, 7, v_infoState_1558_);
lean_ctor_set(v_reuseFailAlloc_1578_, 8, v_snapshotTasks_1559_);
v___x_1572_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1573_ = lean_st_ref_set(v___y_1517_, v___x_1572_);
v___x_1574_ = lean_box(0);
if (v_isShared_1549_ == 0)
{
lean_ctor_set(v___x_1548_, 0, v___x_1574_);
v___x_1576_ = v___x_1548_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9___redArg___boxed(lean_object* v_oldTraces_1584_, lean_object* v_data_1585_, lean_object* v_ref_1586_, lean_object* v_msg_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9___redArg(v_oldTraces_1584_, v_data_1585_, v_ref_1586_, v_msg_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
return v_res_1593_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__11(lean_object* v_e_1594_){
_start:
{
if (lean_obj_tag(v_e_1594_) == 0)
{
uint8_t v___x_1595_; 
v___x_1595_ = 2;
return v___x_1595_;
}
else
{
uint8_t v___x_1596_; 
v___x_1596_ = 0;
return v___x_1596_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__11___boxed(lean_object* v_e_1597_){
_start:
{
uint8_t v_res_1598_; lean_object* v_r_1599_; 
v_res_1598_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__11(v_e_1597_);
lean_dec_ref(v_e_1597_);
v_r_1599_ = lean_box(v_res_1598_);
return v_r_1599_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10___redArg(lean_object* v_x_1600_){
_start:
{
if (lean_obj_tag(v_x_1600_) == 0)
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
v_a_1602_ = lean_ctor_get(v_x_1600_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_x_1600_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v_x_1600_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v_x_1600_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
lean_ctor_set_tag(v___x_1604_, 1);
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
v_a_1610_ = lean_ctor_get(v_x_1600_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v_x_1600_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v_x_1600_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v_x_1600_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
lean_ctor_set_tag(v___x_1612_, 0);
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10___redArg___boxed(lean_object* v_x_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10___redArg(v_x_1618_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12(lean_object* v_opts_1621_, lean_object* v_opt_1622_){
_start:
{
lean_object* v_name_1623_; lean_object* v_defValue_1624_; lean_object* v_map_1625_; lean_object* v___x_1626_; 
v_name_1623_ = lean_ctor_get(v_opt_1622_, 0);
v_defValue_1624_ = lean_ctor_get(v_opt_1622_, 1);
v_map_1625_ = lean_ctor_get(v_opts_1621_, 0);
v___x_1626_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1625_, v_name_1623_);
if (lean_obj_tag(v___x_1626_) == 0)
{
lean_inc(v_defValue_1624_);
return v_defValue_1624_;
}
else
{
lean_object* v_val_1627_; 
v_val_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc(v_val_1627_);
lean_dec_ref_known(v___x_1626_, 1);
if (lean_obj_tag(v_val_1627_) == 3)
{
lean_object* v_v_1628_; 
v_v_1628_ = lean_ctor_get(v_val_1627_, 0);
lean_inc(v_v_1628_);
lean_dec_ref_known(v_val_1627_, 1);
return v_v_1628_;
}
else
{
lean_dec(v_val_1627_);
lean_inc(v_defValue_1624_);
return v_defValue_1624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12___boxed(lean_object* v_opts_1629_, lean_object* v_opt_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12(v_opts_1629_, v_opt_1630_);
lean_dec_ref(v_opt_1630_);
lean_dec_ref(v_opts_1629_);
return v_res_1631_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__1(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__0));
v___x_1634_ = l_Lean_stringToMessageData(v___x_1633_);
return v___x_1634_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__2(void){
_start:
{
lean_object* v___x_1635_; double v___x_1636_; 
v___x_1635_ = lean_unsigned_to_nat(1000u);
v___x_1636_ = lean_float_of_nat(v___x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7(lean_object* v_cls_1637_, uint8_t v_collapsed_1638_, lean_object* v_tag_1639_, lean_object* v_opts_1640_, uint8_t v_clsEnabled_1641_, lean_object* v_oldTraces_1642_, lean_object* v_msg_1643_, lean_object* v_resStartStop_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v_fst_1654_; lean_object* v_snd_1655_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v_data_1659_; lean_object* v_fst_1662_; lean_object* v_snd_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; lean_object* v___y_1667_; lean_object* v_a_1668_; uint8_t v___y_1683_; double v___y_1714_; 
v_fst_1654_ = lean_ctor_get(v_resStartStop_1644_, 0);
lean_inc(v_fst_1654_);
v_snd_1655_ = lean_ctor_get(v_resStartStop_1644_, 1);
lean_inc(v_snd_1655_);
lean_dec_ref(v_resStartStop_1644_);
v_fst_1662_ = lean_ctor_get(v_snd_1655_, 0);
lean_inc(v_fst_1662_);
v_snd_1663_ = lean_ctor_get(v_snd_1655_, 1);
lean_inc(v_snd_1663_);
lean_dec(v_snd_1655_);
v___x_1664_ = l_Lean_trace_profiler;
v___x_1665_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(v_opts_1640_, v___x_1664_);
if (v___x_1665_ == 0)
{
v___y_1683_ = v___x_1665_;
goto v___jp_1682_;
}
else
{
lean_object* v___x_1719_; uint8_t v___x_1720_; 
v___x_1719_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1720_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(v_opts_1640_, v___x_1719_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1722_; double v___x_1723_; double v___x_1724_; double v___x_1725_; 
v___x_1721_ = l_Lean_trace_profiler_threshold;
v___x_1722_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12(v_opts_1640_, v___x_1721_);
v___x_1723_ = lean_float_of_nat(v___x_1722_);
v___x_1724_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__2);
v___x_1725_ = lean_float_div(v___x_1723_, v___x_1724_);
v___y_1714_ = v___x_1725_;
goto v___jp_1713_;
}
else
{
lean_object* v___x_1726_; lean_object* v___x_1727_; double v___x_1728_; 
v___x_1726_ = l_Lean_trace_profiler_threshold;
v___x_1727_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__12(v_opts_1640_, v___x_1726_);
v___x_1728_ = lean_float_of_nat(v___x_1727_);
v___y_1714_ = v___x_1728_;
goto v___jp_1713_;
}
}
v___jp_1656_:
{
lean_object* v___x_1660_; 
lean_inc(v___y_1657_);
v___x_1660_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9___redArg(v_oldTraces_1642_, v_data_1659_, v___y_1657_, v___y_1658_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v___x_1661_; 
lean_dec_ref_known(v___x_1660_, 1);
v___x_1661_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10___redArg(v_fst_1654_);
return v___x_1661_;
}
else
{
lean_dec(v_fst_1654_);
return v___x_1660_;
}
}
v___jp_1666_:
{
uint8_t v_result_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; double v___x_1672_; lean_object* v_data_1673_; 
v_result_1669_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__11(v_fst_1654_);
v___x_1670_ = lean_box(v_result_1669_);
v___x_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
v___x_1672_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_1639_);
lean_inc_ref(v___x_1671_);
lean_inc(v_cls_1637_);
v_data_1673_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1673_, 0, v_cls_1637_);
lean_ctor_set(v_data_1673_, 1, v___x_1671_);
lean_ctor_set(v_data_1673_, 2, v_tag_1639_);
lean_ctor_set_float(v_data_1673_, sizeof(void*)*3, v___x_1672_);
lean_ctor_set_float(v_data_1673_, sizeof(void*)*3 + 8, v___x_1672_);
lean_ctor_set_uint8(v_data_1673_, sizeof(void*)*3 + 16, v_collapsed_1638_);
if (v___x_1665_ == 0)
{
lean_dec_ref_known(v___x_1671_, 1);
lean_dec(v_snd_1663_);
lean_dec(v_fst_1662_);
lean_dec_ref(v_tag_1639_);
lean_dec(v_cls_1637_);
v___y_1657_ = v___y_1667_;
v___y_1658_ = v_a_1668_;
v_data_1659_ = v_data_1673_;
goto v___jp_1656_;
}
else
{
lean_object* v_data_1674_; double v___x_1675_; double v___x_1676_; 
lean_dec_ref_known(v_data_1673_, 3);
v_data_1674_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1674_, 0, v_cls_1637_);
lean_ctor_set(v_data_1674_, 1, v___x_1671_);
lean_ctor_set(v_data_1674_, 2, v_tag_1639_);
v___x_1675_ = lean_unbox_float(v_fst_1662_);
lean_dec(v_fst_1662_);
lean_ctor_set_float(v_data_1674_, sizeof(void*)*3, v___x_1675_);
v___x_1676_ = lean_unbox_float(v_snd_1663_);
lean_dec(v_snd_1663_);
lean_ctor_set_float(v_data_1674_, sizeof(void*)*3 + 8, v___x_1676_);
lean_ctor_set_uint8(v_data_1674_, sizeof(void*)*3 + 16, v_collapsed_1638_);
v___y_1657_ = v___y_1667_;
v___y_1658_ = v_a_1668_;
v_data_1659_ = v_data_1674_;
goto v___jp_1656_;
}
}
v___jp_1677_:
{
lean_object* v_ref_1678_; lean_object* v___x_1679_; 
v_ref_1678_ = lean_ctor_get(v___y_1651_, 5);
lean_inc(v___y_1652_);
lean_inc_ref(v___y_1651_);
lean_inc(v___y_1650_);
lean_inc_ref(v___y_1649_);
lean_inc(v___y_1648_);
lean_inc_ref(v___y_1647_);
lean_inc(v___y_1646_);
lean_inc_ref(v___y_1645_);
lean_inc(v_fst_1654_);
v___x_1679_ = lean_apply_10(v_msg_1643_, v_fst_1654_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, lean_box(0));
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_object* v_a_1680_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1680_);
lean_dec_ref_known(v___x_1679_, 1);
v___y_1667_ = v_ref_1678_;
v_a_1668_ = v_a_1680_;
goto v___jp_1666_;
}
else
{
lean_object* v___x_1681_; 
lean_dec_ref_known(v___x_1679_, 1);
v___x_1681_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___closed__1);
v___y_1667_ = v_ref_1678_;
v_a_1668_ = v___x_1681_;
goto v___jp_1666_;
}
}
v___jp_1682_:
{
if (v_clsEnabled_1641_ == 0)
{
if (v___y_1683_ == 0)
{
lean_object* v___x_1684_; lean_object* v_traceState_1685_; lean_object* v_env_1686_; lean_object* v_nextMacroScope_1687_; lean_object* v_ngen_1688_; lean_object* v_auxDeclNGen_1689_; lean_object* v_cache_1690_; lean_object* v_messages_1691_; lean_object* v_infoState_1692_; lean_object* v_snapshotTasks_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1712_; 
lean_dec(v_snd_1663_);
lean_dec(v_fst_1662_);
lean_dec_ref(v_msg_1643_);
lean_dec_ref(v_tag_1639_);
lean_dec(v_cls_1637_);
v___x_1684_ = lean_st_ref_take(v___y_1652_);
v_traceState_1685_ = lean_ctor_get(v___x_1684_, 4);
v_env_1686_ = lean_ctor_get(v___x_1684_, 0);
v_nextMacroScope_1687_ = lean_ctor_get(v___x_1684_, 1);
v_ngen_1688_ = lean_ctor_get(v___x_1684_, 2);
v_auxDeclNGen_1689_ = lean_ctor_get(v___x_1684_, 3);
v_cache_1690_ = lean_ctor_get(v___x_1684_, 5);
v_messages_1691_ = lean_ctor_get(v___x_1684_, 6);
v_infoState_1692_ = lean_ctor_get(v___x_1684_, 7);
v_snapshotTasks_1693_ = lean_ctor_get(v___x_1684_, 8);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1695_ = v___x_1684_;
v_isShared_1696_ = v_isSharedCheck_1712_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_snapshotTasks_1693_);
lean_inc(v_infoState_1692_);
lean_inc(v_messages_1691_);
lean_inc(v_cache_1690_);
lean_inc(v_traceState_1685_);
lean_inc(v_auxDeclNGen_1689_);
lean_inc(v_ngen_1688_);
lean_inc(v_nextMacroScope_1687_);
lean_inc(v_env_1686_);
lean_dec(v___x_1684_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1712_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
uint64_t v_tid_1697_; lean_object* v_traces_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1711_; 
v_tid_1697_ = lean_ctor_get_uint64(v_traceState_1685_, sizeof(void*)*1);
v_traces_1698_ = lean_ctor_get(v_traceState_1685_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_traceState_1685_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1700_ = v_traceState_1685_;
v_isShared_1701_ = v_isSharedCheck_1711_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_traces_1698_);
lean_dec(v_traceState_1685_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1711_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1702_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1642_, v_traces_1698_);
lean_dec_ref(v_traces_1698_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1702_);
v___x_1704_ = v___x_1700_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1702_);
lean_ctor_set_uint64(v_reuseFailAlloc_1710_, sizeof(void*)*1, v_tid_1697_);
v___x_1704_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1706_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 4, v___x_1704_);
v___x_1706_ = v___x_1695_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_env_1686_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v_nextMacroScope_1687_);
lean_ctor_set(v_reuseFailAlloc_1709_, 2, v_ngen_1688_);
lean_ctor_set(v_reuseFailAlloc_1709_, 3, v_auxDeclNGen_1689_);
lean_ctor_set(v_reuseFailAlloc_1709_, 4, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1709_, 5, v_cache_1690_);
lean_ctor_set(v_reuseFailAlloc_1709_, 6, v_messages_1691_);
lean_ctor_set(v_reuseFailAlloc_1709_, 7, v_infoState_1692_);
lean_ctor_set(v_reuseFailAlloc_1709_, 8, v_snapshotTasks_1693_);
v___x_1706_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = lean_st_ref_set(v___y_1652_, v___x_1706_);
v___x_1708_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10___redArg(v_fst_1654_);
return v___x_1708_;
}
}
}
}
}
else
{
goto v___jp_1677_;
}
}
else
{
goto v___jp_1677_;
}
}
v___jp_1713_:
{
double v___x_1715_; double v___x_1716_; double v___x_1717_; uint8_t v___x_1718_; 
v___x_1715_ = lean_unbox_float(v_snd_1663_);
v___x_1716_ = lean_unbox_float(v_fst_1662_);
v___x_1717_ = lean_float_sub(v___x_1715_, v___x_1716_);
v___x_1718_ = lean_float_decLt(v___y_1714_, v___x_1717_);
v___y_1683_ = v___x_1718_;
goto v___jp_1682_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7___boxed(lean_object** _args){
lean_object* v_cls_1729_ = _args[0];
lean_object* v_collapsed_1730_ = _args[1];
lean_object* v_tag_1731_ = _args[2];
lean_object* v_opts_1732_ = _args[3];
lean_object* v_clsEnabled_1733_ = _args[4];
lean_object* v_oldTraces_1734_ = _args[5];
lean_object* v_msg_1735_ = _args[6];
lean_object* v_resStartStop_1736_ = _args[7];
lean_object* v___y_1737_ = _args[8];
lean_object* v___y_1738_ = _args[9];
lean_object* v___y_1739_ = _args[10];
lean_object* v___y_1740_ = _args[11];
lean_object* v___y_1741_ = _args[12];
lean_object* v___y_1742_ = _args[13];
lean_object* v___y_1743_ = _args[14];
lean_object* v___y_1744_ = _args[15];
lean_object* v___y_1745_ = _args[16];
_start:
{
uint8_t v_collapsed_boxed_1746_; uint8_t v_clsEnabled_boxed_1747_; lean_object* v_res_1748_; 
v_collapsed_boxed_1746_ = lean_unbox(v_collapsed_1730_);
v_clsEnabled_boxed_1747_ = lean_unbox(v_clsEnabled_1733_);
v_res_1748_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7(v_cls_1729_, v_collapsed_boxed_1746_, v_tag_1731_, v_opts_1732_, v_clsEnabled_boxed_1747_, v_oldTraces_1734_, v_msg_1735_, v_resStartStop_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec_ref(v_opts_1732_);
return v_res_1748_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___closed__0));
v___x_1751_ = l_Lean_stringToMessageData(v___x_1750_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4(lean_object* v_as_1752_, size_t v_sz_1753_, size_t v_i_1754_, lean_object* v_b_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_a_1766_; uint8_t v___x_1770_; 
v___x_1770_ = lean_usize_dec_lt(v_i_1754_, v_sz_1753_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; 
v___x_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1771_, 0, v_b_1755_);
return v___x_1771_;
}
else
{
lean_object* v_a_1772_; lean_object* v_options_1773_; lean_object* v_fst_1774_; lean_object* v_snd_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1795_; 
v_a_1772_ = lean_array_uget(v_as_1752_, v_i_1754_);
v_options_1773_ = lean_ctor_get(v___y_1762_, 2);
v_fst_1774_ = lean_ctor_get(v_a_1772_, 0);
v_snd_1775_ = lean_ctor_get(v_a_1772_, 1);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_a_1772_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1777_ = v_a_1772_;
v_isShared_1778_ = v_isSharedCheck_1795_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_snd_1775_);
lean_inc(v_fst_1774_);
lean_dec(v_a_1772_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1795_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v_inheritedTraceOptions_1779_; uint8_t v_hasTrace_1780_; lean_object* v___x_1781_; 
v_inheritedTraceOptions_1779_ = lean_ctor_get(v___y_1762_, 13);
v_hasTrace_1780_ = lean_ctor_get_uint8(v_options_1773_, sizeof(void*)*1);
v___x_1781_ = lean_box(0);
if (v_hasTrace_1780_ == 0)
{
lean_del_object(v___x_1777_);
lean_dec(v_snd_1775_);
lean_dec(v_fst_1774_);
v_a_1766_ = v___x_1781_;
goto v___jp_1765_;
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1782_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__9));
v___x_1783_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12);
v___x_1784_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1779_, v_options_1773_, v___x_1783_);
if (v___x_1784_ == 0)
{
lean_del_object(v___x_1777_);
lean_dec(v_snd_1775_);
lean_dec(v_fst_1774_);
v_a_1766_ = v___x_1781_;
goto v___jp_1765_;
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1788_; 
v___x_1785_ = l_Lean_MessageData_ofName(v_fst_1774_);
v___x_1786_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___closed__1);
if (v_isShared_1778_ == 0)
{
lean_ctor_set_tag(v___x_1777_, 7);
lean_ctor_set(v___x_1777_, 1, v___x_1786_);
lean_ctor_set(v___x_1777_, 0, v___x_1785_);
v___x_1788_ = v___x_1777_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1785_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v___x_1786_);
v___x_1788_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; 
v___x_1789_ = l_Nat_reprFast(v_snd_1775_);
v___x_1790_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
v___x_1791_ = l_Lean_MessageData_ofFormat(v___x_1790_);
v___x_1792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1788_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v___x_1782_, v___x_1792_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_dec_ref_known(v___x_1793_, 1);
v_a_1766_ = v___x_1781_;
goto v___jp_1765_;
}
else
{
return v___x_1793_;
}
}
}
}
}
}
v___jp_1765_:
{
size_t v___x_1767_; size_t v___x_1768_; 
v___x_1767_ = ((size_t)1ULL);
v___x_1768_ = lean_usize_add(v_i_1754_, v___x_1767_);
v_i_1754_ = v___x_1768_;
v_b_1755_ = v_a_1766_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4___boxed(lean_object* v_as_1796_, lean_object* v_sz_1797_, lean_object* v_i_1798_, lean_object* v_b_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
size_t v_sz_boxed_1809_; size_t v_i_boxed_1810_; lean_object* v_res_1811_; 
v_sz_boxed_1809_ = lean_unbox_usize(v_sz_1797_);
lean_dec(v_sz_1797_);
v_i_boxed_1810_ = lean_unbox_usize(v_i_1798_);
lean_dec(v_i_1798_);
v_res_1811_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4(v_as_1796_, v_sz_boxed_1809_, v_i_boxed_1810_, v_b_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec_ref(v_as_1796_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9(lean_object* v_x_1812_, lean_object* v_x_1813_){
_start:
{
if (lean_obj_tag(v_x_1813_) == 0)
{
return v_x_1812_;
}
else
{
lean_object* v_key_1814_; lean_object* v_value_1815_; lean_object* v_tail_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v_key_1814_ = lean_ctor_get(v_x_1813_, 0);
v_value_1815_ = lean_ctor_get(v_x_1813_, 1);
v_tail_1816_ = lean_ctor_get(v_x_1813_, 2);
lean_inc(v_value_1815_);
lean_inc(v_key_1814_);
v___x_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1817_, 0, v_key_1814_);
lean_ctor_set(v___x_1817_, 1, v_value_1815_);
v___x_1818_ = lean_array_push(v_x_1812_, v___x_1817_);
v_x_1812_ = v___x_1818_;
v_x_1813_ = v_tail_1816_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9___boxed(lean_object* v_x_1820_, lean_object* v_x_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9(v_x_1820_, v_x_1821_);
lean_dec(v_x_1821_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__10(lean_object* v_as_1823_, size_t v_i_1824_, size_t v_stop_1825_, lean_object* v_b_1826_){
_start:
{
uint8_t v___x_1827_; 
v___x_1827_ = lean_usize_dec_eq(v_i_1824_, v_stop_1825_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; lean_object* v___x_1829_; size_t v___x_1830_; size_t v___x_1831_; 
v___x_1828_ = lean_array_uget_borrowed(v_as_1823_, v_i_1824_);
v___x_1829_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__9(v_b_1826_, v___x_1828_);
v___x_1830_ = ((size_t)1ULL);
v___x_1831_ = lean_usize_add(v_i_1824_, v___x_1830_);
v_i_1824_ = v___x_1831_;
v_b_1826_ = v___x_1829_;
goto _start;
}
else
{
return v_b_1826_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__10___boxed(lean_object* v_as_1833_, lean_object* v_i_1834_, lean_object* v_stop_1835_, lean_object* v_b_1836_){
_start:
{
size_t v_i_boxed_1837_; size_t v_stop_boxed_1838_; lean_object* v_res_1839_; 
v_i_boxed_1837_ = lean_unbox_usize(v_i_1834_);
lean_dec(v_i_1834_);
v_stop_boxed_1838_ = lean_unbox_usize(v_stop_1835_);
lean_dec(v_stop_1835_);
v_res_1839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__10(v_as_1833_, v_i_boxed_1837_, v_stop_boxed_1838_, v_b_1836_);
lean_dec_ref(v_as_1833_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8_spec__14___redArg(lean_object* v_hi_1840_, lean_object* v_pivot_1841_, lean_object* v_as_1842_, lean_object* v_i_1843_, lean_object* v_k_1844_){
_start:
{
uint8_t v___x_1845_; 
v___x_1845_ = lean_nat_dec_lt(v_k_1844_, v_hi_1840_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
lean_dec(v_k_1844_);
v___x_1846_ = lean_array_fswap(v_as_1842_, v_i_1843_, v_hi_1840_);
v___x_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1847_, 0, v_i_1843_);
lean_ctor_set(v___x_1847_, 1, v___x_1846_);
return v___x_1847_;
}
else
{
lean_object* v_snd_1848_; lean_object* v___x_1849_; lean_object* v_snd_1850_; uint8_t v___x_1851_; 
v_snd_1848_ = lean_ctor_get(v_pivot_1841_, 1);
v___x_1849_ = lean_array_fget_borrowed(v_as_1842_, v_k_1844_);
v_snd_1850_ = lean_ctor_get(v___x_1849_, 1);
v___x_1851_ = lean_nat_dec_lt(v_snd_1848_, v_snd_1850_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = lean_unsigned_to_nat(1u);
v___x_1853_ = lean_nat_add(v_k_1844_, v___x_1852_);
lean_dec(v_k_1844_);
v_k_1844_ = v___x_1853_;
goto _start;
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1855_ = lean_array_fswap(v_as_1842_, v_i_1843_, v_k_1844_);
v___x_1856_ = lean_unsigned_to_nat(1u);
v___x_1857_ = lean_nat_add(v_i_1843_, v___x_1856_);
lean_dec(v_i_1843_);
v___x_1858_ = lean_nat_add(v_k_1844_, v___x_1856_);
lean_dec(v_k_1844_);
v_as_1842_ = v___x_1855_;
v_i_1843_ = v___x_1857_;
v_k_1844_ = v___x_1858_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8_spec__14___redArg___boxed(lean_object* v_hi_1860_, lean_object* v_pivot_1861_, lean_object* v_as_1862_, lean_object* v_i_1863_, lean_object* v_k_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8_spec__14___redArg(v_hi_1860_, v_pivot_1861_, v_as_1862_, v_i_1863_, v_k_1864_);
lean_dec_ref(v_pivot_1861_);
lean_dec(v_hi_1860_);
return v_res_1865_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg___lam__0(lean_object* v_a_1866_, lean_object* v_b_1867_){
_start:
{
lean_object* v_snd_1868_; lean_object* v_snd_1869_; uint8_t v___x_1870_; 
v_snd_1868_ = lean_ctor_get(v_b_1867_, 1);
v_snd_1869_ = lean_ctor_get(v_a_1866_, 1);
v___x_1870_ = lean_nat_dec_lt(v_snd_1868_, v_snd_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg___lam__0___boxed(lean_object* v_a_1871_, lean_object* v_b_1872_){
_start:
{
uint8_t v_res_1873_; lean_object* v_r_1874_; 
v_res_1873_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg___lam__0(v_a_1871_, v_b_1872_);
lean_dec_ref(v_b_1872_);
lean_dec_ref(v_a_1871_);
v_r_1874_ = lean_box(v_res_1873_);
return v_r_1874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg(lean_object* v_n_1875_, lean_object* v_as_1876_, lean_object* v_lo_1877_, lean_object* v_hi_1878_){
_start:
{
lean_object* v___y_1880_; uint8_t v___x_1890_; 
v___x_1890_ = lean_nat_dec_lt(v_lo_1877_, v_hi_1878_);
if (v___x_1890_ == 0)
{
lean_dec(v_lo_1877_);
return v_as_1876_;
}
else
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v_mid_1893_; lean_object* v___y_1895_; lean_object* v___y_1901_; lean_object* v___x_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; 
v___x_1891_ = lean_nat_add(v_lo_1877_, v_hi_1878_);
v___x_1892_ = lean_unsigned_to_nat(1u);
v_mid_1893_ = lean_nat_shiftr(v___x_1891_, v___x_1892_);
lean_dec(v___x_1891_);
v___x_1906_ = lean_array_fget_borrowed(v_as_1876_, v_mid_1893_);
v___x_1907_ = lean_array_fget_borrowed(v_as_1876_, v_lo_1877_);
v___x_1908_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg___lam__0(v___x_1906_, v___x_1907_);
if (v___x_1908_ == 0)
{
v___y_1901_ = v_as_1876_;
goto v___jp_1900_;
}
else
{
lean_object* v___x_1909_; 
v___x_1909_ = lean_array_fswap(v_as_1876_, v_lo_1877_, v_mid_1893_);
v___y_1901_ = v___x_1909_;
goto v___jp_1900_;
}
v___jp_1894_:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1896_ = lean_array_fget_borrowed(v___y_1895_, v_mid_1893_);
v___x_1897_ = lean_array_fget_borrowed(v___y_1895_, v_hi_1878_);
v___x_1898_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg___lam__0(v___x_1896_, v___x_1897_);
if (v___x_1898_ == 0)
{
lean_dec(v_mid_1893_);
v___y_1880_ = v___y_1895_;
goto v___jp_1879_;
}
else
{
lean_object* v___x_1899_; 
v___x_1899_ = lean_array_fswap(v___y_1895_, v_mid_1893_, v_hi_1878_);
lean_dec(v_mid_1893_);
v___y_1880_ = v___x_1899_;
goto v___jp_1879_;
}
}
v___jp_1900_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1902_ = lean_array_fget_borrowed(v___y_1901_, v_hi_1878_);
v___x_1903_ = lean_array_fget_borrowed(v___y_1901_, v_lo_1877_);
v___x_1904_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg___lam__0(v___x_1902_, v___x_1903_);
if (v___x_1904_ == 0)
{
v___y_1895_ = v___y_1901_;
goto v___jp_1894_;
}
else
{
lean_object* v___x_1905_; 
v___x_1905_ = lean_array_fswap(v___y_1901_, v_lo_1877_, v_hi_1878_);
v___y_1895_ = v___x_1905_;
goto v___jp_1894_;
}
}
}
v___jp_1879_:
{
lean_object* v_pivot_1881_; lean_object* v___x_1882_; lean_object* v_fst_1883_; lean_object* v_snd_1884_; uint8_t v___x_1885_; 
v_pivot_1881_ = lean_array_fget(v___y_1880_, v_hi_1878_);
lean_inc_n(v_lo_1877_, 2);
v___x_1882_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8_spec__14___redArg(v_hi_1878_, v_pivot_1881_, v___y_1880_, v_lo_1877_, v_lo_1877_);
lean_dec(v_pivot_1881_);
v_fst_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_fst_1883_);
v_snd_1884_ = lean_ctor_get(v___x_1882_, 1);
lean_inc(v_snd_1884_);
lean_dec_ref(v___x_1882_);
v___x_1885_ = lean_nat_dec_le(v_hi_1878_, v_fst_1883_);
if (v___x_1885_ == 0)
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1886_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg(v_n_1875_, v_snd_1884_, v_lo_1877_, v_fst_1883_);
v___x_1887_ = lean_unsigned_to_nat(1u);
v___x_1888_ = lean_nat_add(v_fst_1883_, v___x_1887_);
lean_dec(v_fst_1883_);
v_as_1876_ = v___x_1886_;
v_lo_1877_ = v___x_1888_;
goto _start;
}
else
{
lean_dec(v_fst_1883_);
lean_dec(v_lo_1877_);
return v_snd_1884_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg___boxed(lean_object* v_n_1910_, lean_object* v_as_1911_, lean_object* v_lo_1912_, lean_object* v_hi_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg(v_n_1910_, v_as_1911_, v_lo_1912_, v_hi_1913_);
lean_dec(v_hi_1913_);
lean_dec(v_n_1910_);
return v_res_1914_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__0(void){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1915_ = lean_box(0);
v___x_1916_ = lean_unsigned_to_nat(16u);
v___x_1917_ = lean_mk_array(v___x_1916_, v___x_1915_);
return v___x_1917_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__1(void){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1918_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__0, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__0);
v___x_1919_ = lean_unsigned_to_nat(0u);
v___x_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
lean_ctor_set(v___x_1920_, 1, v___x_1918_);
return v___x_1920_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__2(void){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1921_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__1, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__1);
v___x_1922_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
lean_ctor_set(v___x_1922_, 2, v___x_1921_);
lean_ctor_set(v___x_1922_, 3, v___x_1921_);
return v___x_1922_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__5(void){
_start:
{
lean_object* v___x_1927_; double v___x_1928_; 
v___x_1927_ = lean_unsigned_to_nat(1000000000u);
v___x_1928_ = lean_float_of_nat(v___x_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5(lean_object* v___x_1929_, lean_object* v___f_1930_, lean_object* v___f_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(v___x_1929_, v___y_1939_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v_maxSteps_1946_; lean_object* v___x_1947_; lean_object* v_goal_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___f_1953_; lean_object* v___f_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; lean_object* v___x_1957_; lean_object* v___f_1958_; lean_object* v___x_1959_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1941_, 1);
v___x_1943_ = lean_unsigned_to_nat(0u);
v___x_1944_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__2);
v___x_1945_ = lean_st_mk_ref(v___x_1944_);
v_maxSteps_1946_ = lean_ctor_get(v___y_1932_, 1);
v___x_1947_ = lean_st_ref_get(v___y_1933_);
v_goal_1948_ = lean_ctor_get(v___x_1947_, 4);
lean_inc(v_goal_1948_);
lean_dec(v___x_1947_);
v___x_1949_ = lean_unsigned_to_nat(2u);
lean_inc_n(v_maxSteps_1946_, 2);
v___x_1950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1950_, 0, v_maxSteps_1946_);
lean_ctor_set(v___x_1950_, 1, v___x_1949_);
v___x_1951_ = lean_unsigned_to_nat(255u);
v___x_1952_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__4));
lean_inc(v___x_1945_);
v___f_1953_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__2___boxed), 15, 3);
lean_closure_set(v___f_1953_, 0, v___x_1945_);
lean_closure_set(v___f_1953_, 1, v_a_1942_);
lean_closure_set(v___f_1953_, 2, v___x_1952_);
v___f_1954_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__3___boxed), 13, 2);
lean_closure_set(v___f_1954_, 0, v___x_1951_);
lean_closure_set(v___f_1954_, 1, v___f_1953_);
v___x_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___f_1930_);
lean_ctor_set(v___x_1955_, 1, v___f_1954_);
v___x_1956_ = 1;
v___x_1957_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1957_, 0, v_maxSteps_1946_);
lean_ctor_set_uint8(v___x_1957_, sizeof(void*)*1, v___x_1956_);
v___f_1958_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__4___boxed), 13, 4);
lean_closure_set(v___f_1958_, 0, v___x_1957_);
lean_closure_set(v___f_1958_, 1, v___x_1955_);
lean_closure_set(v___f_1958_, 2, v___x_1950_);
lean_closure_set(v___f_1958_, 3, v___x_1943_);
v___x_1959_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__3___redArg(v_goal_1948_, v___f_1958_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___y_1962_; lean_object* v_options_1979_; uint8_t v_hasTrace_1980_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
v_options_1979_ = lean_ctor_get(v___y_1938_, 2);
v_hasTrace_1980_ = lean_ctor_get_uint8(v_options_1979_, sizeof(void*)*1);
if (v_hasTrace_1980_ == 0)
{
lean_dec(v_a_1960_);
lean_dec(v___x_1945_);
lean_dec_ref(v___f_1931_);
return v___x_1959_;
}
else
{
lean_object* v_inheritedTraceOptions_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; uint8_t v___x_1984_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v_a_1989_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v_a_2005_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v_a_2011_; lean_object* v___y_2021_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v_a_2024_; 
v_inheritedTraceOptions_1981_ = lean_ctor_get(v___y_1938_, 13);
v___x_1982_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__9));
v___x_1983_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg___closed__12);
v___x_1984_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1981_, v_options_1979_, v___x_1983_);
if (v___x_1984_ == 0)
{
lean_dec(v_a_1960_);
lean_dec(v___x_1945_);
lean_dec_ref(v___f_1931_);
return v___x_1959_;
}
else
{
lean_object* v___x_2026_; lean_object* v___y_2028_; size_t v___y_2029_; size_t v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2060_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; lean_object* v___y_2080_; lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2089_; lean_object* v_statistics_2095_; lean_object* v_size_2096_; lean_object* v_buckets_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; uint8_t v___x_2100_; 
lean_dec_ref_known(v___x_1959_, 1);
v___x_2026_ = lean_st_ref_get(v___x_1945_);
lean_dec(v___x_1945_);
v_statistics_2095_ = lean_ctor_get(v___x_2026_, 3);
lean_inc_ref(v_statistics_2095_);
lean_dec(v___x_2026_);
v_size_2096_ = lean_ctor_get(v_statistics_2095_, 0);
lean_inc(v_size_2096_);
v_buckets_2097_ = lean_ctor_get(v_statistics_2095_, 1);
lean_inc_ref(v_buckets_2097_);
lean_dec_ref(v_statistics_2095_);
v___x_2098_ = lean_mk_empty_array_with_capacity(v_size_2096_);
lean_dec(v_size_2096_);
v___x_2099_ = lean_array_get_size(v_buckets_2097_);
v___x_2100_ = lean_nat_dec_lt(v___x_1943_, v___x_2099_);
if (v___x_2100_ == 0)
{
lean_dec_ref(v_buckets_2097_);
v___y_2089_ = v___x_2098_;
goto v___jp_2088_;
}
else
{
uint8_t v___x_2101_; 
v___x_2101_ = lean_nat_dec_le(v___x_2099_, v___x_2099_);
if (v___x_2101_ == 0)
{
if (v___x_2100_ == 0)
{
lean_dec_ref(v_buckets_2097_);
v___y_2089_ = v___x_2098_;
goto v___jp_2088_;
}
else
{
size_t v___x_2102_; size_t v___x_2103_; lean_object* v___x_2104_; 
v___x_2102_ = ((size_t)0ULL);
v___x_2103_ = lean_usize_of_nat(v___x_2099_);
v___x_2104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__10(v_buckets_2097_, v___x_2102_, v___x_2103_, v___x_2098_);
lean_dec_ref(v_buckets_2097_);
v___y_2089_ = v___x_2104_;
goto v___jp_2088_;
}
}
else
{
size_t v___x_2105_; size_t v___x_2106_; lean_object* v___x_2107_; 
v___x_2105_ = ((size_t)0ULL);
v___x_2106_ = lean_usize_of_nat(v___x_2099_);
v___x_2107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__10(v_buckets_2097_, v___x_2105_, v___x_2106_, v___x_2098_);
lean_dec_ref(v_buckets_2097_);
v___y_2089_ = v___x_2107_;
goto v___jp_2088_;
}
}
v___jp_2027_:
{
lean_object* v___x_2033_; lean_object* v_a_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; 
v___x_2033_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__5___redArg(v___y_1939_);
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref(v___x_2033_);
v___x_2035_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2036_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(v_options_1979_, v___x_2035_);
if (v___x_2036_ == 0)
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = lean_io_mono_nanos_now();
v___x_2038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4(v___y_2028_, v___y_2029_, v___y_2030_, v___y_2032_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec_ref(v___y_2028_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_dec_ref_known(v___x_2038_, 1);
v___y_2002_ = v___y_2031_;
v___y_2003_ = v___x_2037_;
v___y_2004_ = v_a_2034_;
v_a_2005_ = v___y_2032_;
goto v___jp_2001_;
}
else
{
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
v___y_2002_ = v___y_2031_;
v___y_2003_ = v___x_2037_;
v___y_2004_ = v_a_2034_;
v_a_2005_ = v_a_2039_;
goto v___jp_2001_;
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
v_a_2040_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2038_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2038_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
lean_ctor_set_tag(v___x_2042_, 0);
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
v___y_1986_ = v___y_2031_;
v___y_1987_ = v___x_2037_;
v___y_1988_ = v_a_2034_;
v_a_1989_ = v___x_2045_;
goto v___jp_1985_;
}
}
}
}
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = lean_io_get_num_heartbeats();
v___x_2049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4(v___y_2028_, v___y_2029_, v___y_2030_, v___y_2032_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec_ref(v___y_2028_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_dec_ref_known(v___x_2049_, 1);
v___y_2021_ = v___y_2031_;
v___y_2022_ = v___x_2048_;
v___y_2023_ = v_a_2034_;
v_a_2024_ = v___y_2032_;
goto v___jp_2020_;
}
else
{
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref_known(v___x_2049_, 1);
v___y_2021_ = v___y_2031_;
v___y_2022_ = v___x_2048_;
v___y_2023_ = v_a_2034_;
v_a_2024_ = v_a_2050_;
goto v___jp_2020_;
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
v_a_2051_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2049_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2049_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
lean_ctor_set_tag(v___x_2053_, 0);
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
v___y_2008_ = v___y_2031_;
v___y_2009_ = v___x_2048_;
v___y_2010_ = v_a_2034_;
v_a_2011_ = v___x_2056_;
goto v___jp_2007_;
}
}
}
}
}
}
v___jp_2059_:
{
lean_object* v___x_2061_; size_t v_sz_2062_; size_t v___x_2063_; lean_object* v___x_2064_; 
v___x_2061_ = lean_box(0);
v_sz_2062_ = lean_array_size(v___y_2060_);
v___x_2063_ = ((size_t)0ULL);
v___x_2064_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1));
if (v___x_1984_ == 0)
{
lean_object* v___x_2065_; uint8_t v___x_2066_; 
v___x_2065_ = l_Lean_trace_profiler;
v___x_2066_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__6(v_options_1979_, v___x_2065_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; 
lean_dec_ref(v___f_1931_);
v___x_2067_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__4(v___y_2060_, v_sz_2062_, v___x_2063_, v___x_2061_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec_ref(v___y_2060_);
if (lean_obj_tag(v___x_2067_) == 0)
{
lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; 
v_unused_2075_ = lean_ctor_get(v___x_2067_, 0);
lean_dec(v_unused_2075_);
v___x_2069_ = v___x_2067_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_dec(v___x_2067_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v_a_1960_);
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_1960_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
else
{
v___y_1962_ = v___x_2067_;
goto v___jp_1961_;
}
}
else
{
v___y_2028_ = v___y_2060_;
v___y_2029_ = v_sz_2062_;
v___y_2030_ = v___x_2063_;
v___y_2031_ = v___x_2064_;
v___y_2032_ = v___x_2061_;
goto v___jp_2027_;
}
}
else
{
v___y_2028_ = v___y_2060_;
v___y_2029_ = v_sz_2062_;
v___y_2030_ = v___x_2063_;
v___y_2031_ = v___x_2064_;
v___y_2032_ = v___x_2061_;
goto v___jp_2027_;
}
}
v___jp_2076_:
{
lean_object* v___x_2081_; 
v___x_2081_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg(v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec(v___y_2077_);
v___y_2060_ = v___x_2081_;
goto v___jp_2059_;
}
v___jp_2082_:
{
uint8_t v___x_2087_; 
v___x_2087_ = lean_nat_dec_le(v___y_2086_, v___y_2083_);
if (v___x_2087_ == 0)
{
lean_dec(v___y_2083_);
lean_inc(v___y_2086_);
v___y_2077_ = v___y_2084_;
v___y_2078_ = v___y_2085_;
v___y_2079_ = v___y_2086_;
v___y_2080_ = v___y_2086_;
goto v___jp_2076_;
}
else
{
v___y_2077_ = v___y_2084_;
v___y_2078_ = v___y_2085_;
v___y_2079_ = v___y_2086_;
v___y_2080_ = v___y_2083_;
goto v___jp_2076_;
}
}
v___jp_2088_:
{
lean_object* v___x_2090_; uint8_t v___x_2091_; 
v___x_2090_ = lean_array_get_size(v___y_2089_);
v___x_2091_ = lean_nat_dec_eq(v___x_2090_, v___x_1943_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; 
v___x_2092_ = lean_unsigned_to_nat(1u);
v___x_2093_ = lean_nat_sub(v___x_2090_, v___x_2092_);
v___x_2094_ = lean_nat_dec_le(v___x_1943_, v___x_2093_);
if (v___x_2094_ == 0)
{
lean_inc(v___x_2093_);
v___y_2083_ = v___x_2093_;
v___y_2084_ = v___x_2090_;
v___y_2085_ = v___y_2089_;
v___y_2086_ = v___x_2093_;
goto v___jp_2082_;
}
else
{
v___y_2083_ = v___x_2093_;
v___y_2084_ = v___x_2090_;
v___y_2085_ = v___y_2089_;
v___y_2086_ = v___x_1943_;
goto v___jp_2082_;
}
}
else
{
v___y_2060_ = v___y_2089_;
goto v___jp_2059_;
}
}
}
v___jp_1985_:
{
lean_object* v___x_1990_; double v___x_1991_; double v___x_1992_; double v___x_1993_; double v___x_1994_; double v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1990_ = lean_io_mono_nanos_now();
v___x_1991_ = lean_float_of_nat(v___y_1987_);
v___x_1992_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___closed__5);
v___x_1993_ = lean_float_div(v___x_1991_, v___x_1992_);
v___x_1994_ = lean_float_of_nat(v___x_1990_);
v___x_1995_ = lean_float_div(v___x_1994_, v___x_1992_);
v___x_1996_ = lean_box_float(v___x_1993_);
v___x_1997_ = lean_box_float(v___x_1995_);
v___x_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1996_);
lean_ctor_set(v___x_1998_, 1, v___x_1997_);
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v_a_1989_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
lean_inc_ref(v___y_1986_);
v___x_2000_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7(v___x_1982_, v___x_1956_, v___y_1986_, v_options_1979_, v___x_1984_, v___y_1988_, v___f_1931_, v___x_1999_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
v___y_1962_ = v___x_2000_;
goto v___jp_1961_;
}
v___jp_2001_:
{
lean_object* v___x_2006_; 
v___x_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2006_, 0, v_a_2005_);
v___y_1986_ = v___y_2002_;
v___y_1987_ = v___y_2003_;
v___y_1988_ = v___y_2004_;
v_a_1989_ = v___x_2006_;
goto v___jp_1985_;
}
v___jp_2007_:
{
lean_object* v___x_2012_; double v___x_2013_; double v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2012_ = lean_io_get_num_heartbeats();
v___x_2013_ = lean_float_of_nat(v___y_2009_);
v___x_2014_ = lean_float_of_nat(v___x_2012_);
v___x_2015_ = lean_box_float(v___x_2013_);
v___x_2016_ = lean_box_float(v___x_2014_);
v___x_2017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2015_);
lean_ctor_set(v___x_2017_, 1, v___x_2016_);
v___x_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2018_, 0, v_a_2011_);
lean_ctor_set(v___x_2018_, 1, v___x_2017_);
lean_inc_ref(v___y_2008_);
v___x_2019_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7(v___x_1982_, v___x_1956_, v___y_2008_, v_options_1979_, v___x_1984_, v___y_2010_, v___f_1931_, v___x_2018_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
v___y_1962_ = v___x_2019_;
goto v___jp_1961_;
}
v___jp_2020_:
{
lean_object* v___x_2025_; 
v___x_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2025_, 0, v_a_2024_);
v___y_2008_ = v___y_2021_;
v___y_2009_ = v___y_2022_;
v___y_2010_ = v___y_2023_;
v_a_2011_ = v___x_2025_;
goto v___jp_2007_;
}
}
v___jp_1961_:
{
if (lean_obj_tag(v___y_1962_) == 0)
{
lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
v_isSharedCheck_1969_ = !lean_is_exclusive(v___y_1962_);
if (v_isSharedCheck_1969_ == 0)
{
lean_object* v_unused_1970_; 
v_unused_1970_ = lean_ctor_get(v___y_1962_, 0);
lean_dec(v_unused_1970_);
v___x_1964_ = v___y_1962_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_dec(v___y_1962_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 0, v_a_1960_);
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1960_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec(v_a_1960_);
v_a_1971_ = lean_ctor_get(v___y_1962_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___y_1962_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___y_1962_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___y_1962_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
}
else
{
lean_dec(v___x_1945_);
lean_dec_ref(v___f_1931_);
return v___x_1959_;
}
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec_ref(v___f_1931_);
lean_dec_ref(v___f_1930_);
v_a_2108_ = lean_ctor_get(v___x_1941_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_1941_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_1941_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_1941_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___boxed(lean_object* v___x_2116_, lean_object* v___f_2117_, lean_object* v___f_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5(v___x_2116_, v___f_2117_, v___f_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec_ref(v___x_2116_);
return v_res_2128_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4(void){
_start:
{
lean_object* v___f_2134_; lean_object* v___f_2135_; lean_object* v___x_2136_; lean_object* v___f_2137_; 
v___f_2134_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__0));
v___f_2135_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__1));
v___x_2136_ = l_Lean_Meta_Tactic_BVDecide_bvNormalizeExt;
v___f_2137_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__5___boxed), 12, 3);
lean_closure_set(v___f_2137_, 0, v___x_2136_);
lean_closure_set(v___f_2137_, 1, v___f_2135_);
lean_closure_set(v___f_2137_, 2, v___f_2134_);
return v___f_2137_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__5(void){
_start:
{
lean_object* v___f_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___f_2138_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4);
v___x_2139_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__3));
v___x_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
lean_ctor_set(v___x_2140_, 1, v___f_2138_);
return v___x_2140_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass(void){
_start:
{
lean_object* v___x_2141_; 
v___x_2141_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__5, &l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__5);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0(lean_object* v_cls_2142_, lean_object* v_msg_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v_cls_2142_, v_msg_2143_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___boxed(lean_object* v_cls_2154_, lean_object* v_msg_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0(v_cls_2154_, v_msg_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1(lean_object* v_mvarId_2166_, lean_object* v_val_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___redArg(v_mvarId_2166_, v_val_2167_, v___y_2173_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1___boxed(lean_object* v_mvarId_2178_, lean_object* v_val_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1(v_mvarId_2178_, v_val_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2(lean_object* v_upperBound_2190_, lean_object* v___x_2191_, lean_object* v___x_2192_, lean_object* v___x_2193_, lean_object* v___x_2194_, lean_object* v_inst_2195_, lean_object* v_R_2196_, lean_object* v_a_2197_, lean_object* v_b_2198_, lean_object* v_c_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___redArg(v_upperBound_2190_, v___x_2191_, v___x_2192_, v___x_2193_, v___x_2194_, v_a_2197_, v_b_2198_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_2210_ = _args[0];
lean_object* v___x_2211_ = _args[1];
lean_object* v___x_2212_ = _args[2];
lean_object* v___x_2213_ = _args[3];
lean_object* v___x_2214_ = _args[4];
lean_object* v_inst_2215_ = _args[5];
lean_object* v_R_2216_ = _args[6];
lean_object* v_a_2217_ = _args[7];
lean_object* v_b_2218_ = _args[8];
lean_object* v_c_2219_ = _args[9];
lean_object* v___y_2220_ = _args[10];
lean_object* v___y_2221_ = _args[11];
lean_object* v___y_2222_ = _args[12];
lean_object* v___y_2223_ = _args[13];
lean_object* v___y_2224_ = _args[14];
lean_object* v___y_2225_ = _args[15];
lean_object* v___y_2226_ = _args[16];
lean_object* v___y_2227_ = _args[17];
lean_object* v___y_2228_ = _args[18];
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__2(v_upperBound_2210_, v___x_2211_, v___x_2212_, v___x_2213_, v___x_2214_, v_inst_2215_, v_R_2216_, v_a_2217_, v_b_2218_, v_c_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec_ref(v___x_2211_);
lean_dec(v_upperBound_2210_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10(lean_object* v_00_u03b1_2230_, lean_object* v_x_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10___redArg(v_x_2231_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2242_, lean_object* v_x_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__10(v_00_u03b1_2242_, v_x_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8(lean_object* v_n_2254_, lean_object* v_as_2255_, lean_object* v_lo_2256_, lean_object* v_hi_2257_, lean_object* v_w_2258_, lean_object* v_hlo_2259_, lean_object* v_hhi_2260_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___redArg(v_n_2254_, v_as_2255_, v_lo_2256_, v_hi_2257_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8___boxed(lean_object* v_n_2262_, lean_object* v_as_2263_, lean_object* v_lo_2264_, lean_object* v_hi_2265_, lean_object* v_w_2266_, lean_object* v_hlo_2267_, lean_object* v_hhi_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8(v_n_2262_, v_as_2263_, v_lo_2264_, v_hi_2265_, v_w_2266_, v_hlo_2267_, v_hhi_2268_);
lean_dec(v_hi_2265_);
lean_dec(v_n_2262_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2(lean_object* v_00_u03b2_2270_, lean_object* v_x_2271_, lean_object* v_x_2272_, lean_object* v_x_2273_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2___redArg(v_x_2271_, v_x_2272_, v_x_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9(lean_object* v_oldTraces_2275_, lean_object* v_data_2276_, lean_object* v_ref_2277_, lean_object* v_msg_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9___redArg(v_oldTraces_2275_, v_data_2276_, v_ref_2277_, v_msg_2278_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9___boxed(lean_object* v_oldTraces_2289_, lean_object* v_data_2290_, lean_object* v_ref_2291_, lean_object* v_msg_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__7_spec__9(v_oldTraces_2289_, v_data_2290_, v_ref_2291_, v_msg_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8_spec__14(lean_object* v_n_2303_, lean_object* v_lo_2304_, lean_object* v_hi_2305_, lean_object* v_hhi_2306_, lean_object* v_pivot_2307_, lean_object* v_as_2308_, lean_object* v_i_2309_, lean_object* v_k_2310_, lean_object* v_ilo_2311_, lean_object* v_ik_2312_, lean_object* v_w_2313_){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8_spec__14___redArg(v_hi_2305_, v_pivot_2307_, v_as_2308_, v_i_2309_, v_k_2310_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8_spec__14___boxed(lean_object* v_n_2315_, lean_object* v_lo_2316_, lean_object* v_hi_2317_, lean_object* v_hhi_2318_, lean_object* v_pivot_2319_, lean_object* v_as_2320_, lean_object* v_i_2321_, lean_object* v_k_2322_, lean_object* v_ilo_2323_, lean_object* v_ik_2324_, lean_object* v_w_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__8_spec__14(v_n_2315_, v_lo_2316_, v_hi_2317_, v_hhi_2318_, v_pivot_2319_, v_as_2320_, v_i_2321_, v_k_2322_, v_ilo_2323_, v_ik_2324_, v_w_2325_);
lean_dec_ref(v_pivot_2319_);
lean_dec(v_hi_2317_);
lean_dec(v_lo_2316_);
lean_dec(v_n_2315_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6(lean_object* v_00_u03b2_2327_, lean_object* v_x_2328_, size_t v_x_2329_, size_t v_x_2330_, lean_object* v_x_2331_, lean_object* v_x_2332_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___redArg(v_x_2328_, v_x_2329_, v_x_2330_, v_x_2331_, v_x_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_2334_, lean_object* v_x_2335_, lean_object* v_x_2336_, lean_object* v_x_2337_, lean_object* v_x_2338_, lean_object* v_x_2339_){
_start:
{
size_t v_x_123721__boxed_2340_; size_t v_x_123722__boxed_2341_; lean_object* v_res_2342_; 
v_x_123721__boxed_2340_ = lean_unbox_usize(v_x_2336_);
lean_dec(v_x_2336_);
v_x_123722__boxed_2341_ = lean_unbox_usize(v_x_2337_);
lean_dec(v_x_2337_);
v_res_2342_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6(v_00_u03b2_2334_, v_x_2335_, v_x_123721__boxed_2340_, v_x_123722__boxed_2341_, v_x_2338_, v_x_2339_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__16(lean_object* v_00_u03b2_2343_, lean_object* v_n_2344_, lean_object* v_k_2345_, lean_object* v_v_2346_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__16___redArg(v_n_2344_, v_k_2345_, v_v_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__17(lean_object* v_00_u03b2_2348_, size_t v_depth_2349_, lean_object* v_keys_2350_, lean_object* v_vals_2351_, lean_object* v_heq_2352_, lean_object* v_i_2353_, lean_object* v_entries_2354_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__17___redArg(v_depth_2349_, v_keys_2350_, v_vals_2351_, v_i_2353_, v_entries_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__17___boxed(lean_object* v_00_u03b2_2356_, lean_object* v_depth_2357_, lean_object* v_keys_2358_, lean_object* v_vals_2359_, lean_object* v_heq_2360_, lean_object* v_i_2361_, lean_object* v_entries_2362_){
_start:
{
size_t v_depth_boxed_2363_; lean_object* v_res_2364_; 
v_depth_boxed_2363_ = lean_unbox_usize(v_depth_2357_);
lean_dec(v_depth_2357_);
v_res_2364_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__17(v_00_u03b2_2356_, v_depth_boxed_2363_, v_keys_2358_, v_vals_2359_, v_heq_2360_, v_i_2361_, v_entries_2362_);
lean_dec_ref(v_vals_2359_);
lean_dec_ref(v_keys_2358_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__16_spec__19(lean_object* v_00_u03b2_2365_, lean_object* v_x_2366_, lean_object* v_x_2367_, lean_object* v_x_2368_, lean_object* v_x_2369_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__1_spec__2_spec__6_spec__16_spec__19___redArg(v_x_2366_, v_x_2367_, v_x_2368_, v_x_2369_);
return v___x_2370_;
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

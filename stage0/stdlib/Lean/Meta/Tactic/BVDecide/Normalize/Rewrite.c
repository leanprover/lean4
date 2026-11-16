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
lean_object* l_Lean_Meta_Sym_DSimp_evalGround___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteDsimproc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpControl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_bvNormalizeExt;
lean_object* l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_evalGround___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__4___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "rewriteRules simproc statistics:"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofProp"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__3_value),LEAN_SCALAR_PTR_LITERAL(51, 215, 172, 1, 76, 176, 171, 156)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__4_value),LEAN_SCALAR_PTR_LITERAL(151, 241, 154, 221, 113, 114, 185, 190)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__8___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__9___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___boxed(lean_object**);
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___redArg___closed__0_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__1_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__2___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__2_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__3___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__2_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__3_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__4___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__3_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__4_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___boxed, .m_arity = 13, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__4_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__5_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__7_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_evalGround___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__7_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__8_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__8_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__10;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__11;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__12;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__5_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__14;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "  ==>  "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___boxed, .m_arity = 16, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "rewriteRules"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__1_value),LEAN_SCALAR_PTR_LITERAL(39, 217, 1, 104, 84, 94, 139, 227)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__2_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___boxed, .m_arity = 14, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__0_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__3_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___closed__4_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__0___redArg___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__0___redArg___lam__0___boxed(lean_object* v_x_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__0___redArg___lam__0(v_x_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__0___redArg(lean_object* v_mvarId_29_, lean_object* v_x_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_){
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
v___f_43_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__0___redArg___lam__0___boxed), 13, 8);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__0___redArg___boxed(lean_object* v_mvarId_53_, lean_object* v_x_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__0___redArg(v_mvarId_53_, v_x_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__0(lean_object* v_00_u03b1_68_, lean_object* v_mvarId_69_, lean_object* v_x_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__0___redArg(v_mvarId_69_, v_x_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__0___boxed(lean_object* v_00_u03b1_84_, lean_object* v_mvarId_85_, lean_object* v_x_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__0(v_00_u03b1_84_, v_mvarId_85_, v_x_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___redArg___closed__0(void){
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_103_ = ((size_t)5ULL);
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = lean_unsigned_to_nat(32u);
v___x_106_ = lean_mk_empty_array_with_capacity(v___x_105_);
v___x_107_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___redArg___closed__0);
v___x_108_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___x_106_);
lean_ctor_set(v___x_108_, 2, v___x_104_);
lean_ctor_set(v___x_108_, 3, v___x_104_);
lean_ctor_set_usize(v___x_108_, 4, v___x_103_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___redArg(lean_object* v___y_109_){
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
v___x_132_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___redArg___closed__1);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___redArg___boxed(lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___redArg(v___y_144_);
lean_dec(v___y_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3(lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___redArg(v___y_157_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___boxed(lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3(v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__4(lean_object* v_opts_173_, lean_object* v_opt_174_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__4___boxed(lean_object* v_opts_183_, lean_object* v_opt_184_){
_start:
{
uint8_t v_res_185_; lean_object* v_r_186_; 
v_res_185_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__4(v_opts_183_, v_opt_184_);
lean_dec_ref(v_opt_184_);
lean_dec_ref(v_opts_183_);
v_r_186_ = lean_box(v_res_185_);
return v_r_186_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__0___closed__1));
v___x_191_ = l_Lean_MessageData_ofFormat(v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__0(lean_object* v_x_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__0___closed__2);
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__0___boxed(lean_object* v_x_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__0(v_x_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__1(lean_object* v_x_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__1___closed__0));
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__1___boxed(lean_object* v_x_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__1(v_x_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v_x_236_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__2(lean_object* v_x_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_260_; 
lean_inc_ref(v___y_249_);
v___x_260_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_249_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
if (lean_obj_tag(v_a_261_) == 0)
{
uint8_t v_done_262_; 
v_done_262_ = lean_ctor_get_uint8(v_a_261_, 0);
lean_dec_ref_known(v_a_261_, 0);
if (v_done_262_ == 0)
{
lean_object* v___x_263_; 
lean_dec_ref_known(v___x_260_, 1);
v___x_263_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteDsimproc___redArg(v___y_249_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
return v___x_263_;
}
else
{
lean_dec_ref(v___y_249_);
return v___x_260_;
}
}
else
{
uint8_t v_done_264_; 
lean_dec_ref(v___y_249_);
v_done_264_ = lean_ctor_get_uint8(v_a_261_, sizeof(void*)*1);
if (v_done_264_ == 0)
{
lean_object* v_e_x27_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_283_; 
lean_dec_ref_known(v___x_260_, 1);
v_e_x27_265_ = lean_ctor_get(v_a_261_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v_a_261_);
if (v_isSharedCheck_283_ == 0)
{
v___x_267_ = v_a_261_;
v_isShared_268_ = v_isSharedCheck_283_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_e_x27_265_);
lean_dec(v_a_261_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_283_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; 
lean_inc_ref(v_e_x27_265_);
v___x_269_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteDsimproc___redArg(v_e_x27_265_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v_a_270_; 
v_a_270_ = lean_ctor_get(v___x_269_, 0);
if (lean_obj_tag(v_a_270_) == 0)
{
lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_281_; 
lean_inc_ref(v_a_270_);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_281_ == 0)
{
lean_object* v_unused_282_; 
v_unused_282_ = lean_ctor_get(v___x_269_, 0);
lean_dec(v_unused_282_);
v___x_272_ = v___x_269_;
v_isShared_273_ = v_isSharedCheck_281_;
goto v_resetjp_271_;
}
else
{
lean_dec(v___x_269_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_281_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
uint8_t v_done_274_; lean_object* v___x_276_; 
v_done_274_ = lean_ctor_get_uint8(v_a_270_, 0);
lean_dec_ref_known(v_a_270_, 0);
if (v_isShared_268_ == 0)
{
v___x_276_ = v___x_267_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_e_x27_265_);
v___x_276_ = v_reuseFailAlloc_280_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_278_; 
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*1, v_done_274_);
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 0, v___x_276_);
v___x_278_ = v___x_272_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_276_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
else
{
lean_del_object(v___x_267_);
lean_dec_ref(v_e_x27_265_);
return v___x_269_;
}
}
else
{
lean_del_object(v___x_267_);
lean_dec_ref(v_e_x27_265_);
return v___x_269_;
}
}
}
else
{
lean_dec_ref_known(v_a_261_, 1);
return v___x_260_;
}
}
}
else
{
lean_dec_ref(v___y_249_);
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__2___boxed(lean_object* v_x_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__2(v_x_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__3(lean_object* v___f_297_, lean_object* v_x_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_box(0);
lean_inc_ref(v___y_299_);
v___x_311_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_299_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
if (lean_obj_tag(v_a_312_) == 0)
{
uint8_t v_done_313_; 
v_done_313_ = lean_ctor_get_uint8(v_a_312_, 0);
lean_dec_ref_known(v_a_312_, 0);
if (v_done_313_ == 0)
{
lean_object* v___x_314_; 
lean_dec_ref_known(v___x_311_, 1);
lean_inc(v___y_308_);
lean_inc_ref(v___y_307_);
lean_inc(v___y_306_);
lean_inc_ref(v___y_305_);
lean_inc(v___y_304_);
lean_inc_ref(v___y_303_);
lean_inc(v___y_302_);
lean_inc_ref(v___y_301_);
lean_inc(v___y_300_);
v___x_314_ = lean_apply_12(v___f_297_, v___x_310_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, lean_box(0));
return v___x_314_;
}
else
{
lean_dec_ref(v___y_299_);
lean_dec_ref(v___f_297_);
return v___x_311_;
}
}
else
{
uint8_t v_done_315_; 
lean_dec_ref(v___y_299_);
v_done_315_ = lean_ctor_get_uint8(v_a_312_, sizeof(void*)*1);
if (v_done_315_ == 0)
{
lean_object* v_e_x27_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_334_; 
lean_dec_ref_known(v___x_311_, 1);
v_e_x27_316_ = lean_ctor_get(v_a_312_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v_a_312_);
if (v_isSharedCheck_334_ == 0)
{
v___x_318_ = v_a_312_;
v_isShared_319_ = v_isSharedCheck_334_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_e_x27_316_);
lean_dec(v_a_312_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_334_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; 
lean_inc(v___y_308_);
lean_inc_ref(v___y_307_);
lean_inc(v___y_306_);
lean_inc_ref(v___y_305_);
lean_inc(v___y_304_);
lean_inc_ref(v___y_303_);
lean_inc(v___y_302_);
lean_inc_ref(v___y_301_);
lean_inc(v___y_300_);
lean_inc_ref(v_e_x27_316_);
v___x_320_ = lean_apply_12(v___f_297_, v___x_310_, v_e_x27_316_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, lean_box(0));
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
if (lean_obj_tag(v_a_321_) == 0)
{
lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_332_; 
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; 
v_unused_333_ = lean_ctor_get(v___x_320_, 0);
lean_dec(v_unused_333_);
v___x_323_ = v___x_320_;
v_isShared_324_ = v_isSharedCheck_332_;
goto v_resetjp_322_;
}
else
{
lean_dec(v___x_320_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_332_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
uint8_t v_done_325_; lean_object* v___x_327_; 
v_done_325_ = lean_ctor_get_uint8(v_a_321_, 0);
lean_dec_ref_known(v_a_321_, 0);
if (v_isShared_319_ == 0)
{
v___x_327_ = v___x_318_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_e_x27_316_);
v___x_327_ = v_reuseFailAlloc_331_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_329_; 
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*1, v_done_325_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_327_);
v___x_329_ = v___x_323_;
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
lean_dec_ref_known(v_a_321_, 1);
lean_del_object(v___x_318_);
lean_dec_ref(v_e_x27_316_);
return v___x_320_;
}
}
else
{
lean_del_object(v___x_318_);
lean_dec_ref(v_e_x27_316_);
return v___x_320_;
}
}
}
else
{
lean_dec_ref_known(v_a_312_, 1);
lean_dec_ref(v___f_297_);
return v___x_311_;
}
}
}
else
{
lean_dec_ref(v___y_299_);
lean_dec_ref(v___f_297_);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__3___boxed(lean_object* v___f_335_, lean_object* v_x_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__3(v___f_335_, v_x_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__4(lean_object* v___f_349_, lean_object* v_x_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_box(0);
lean_inc_ref(v___y_351_);
v___x_363_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v___y_351_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
if (lean_obj_tag(v_a_364_) == 0)
{
uint8_t v_done_365_; 
v_done_365_ = lean_ctor_get_uint8(v_a_364_, 0);
lean_dec_ref_known(v_a_364_, 0);
if (v_done_365_ == 0)
{
lean_object* v___x_366_; 
lean_dec_ref_known(v___x_363_, 1);
lean_inc(v___y_360_);
lean_inc_ref(v___y_359_);
lean_inc(v___y_358_);
lean_inc_ref(v___y_357_);
lean_inc(v___y_356_);
lean_inc_ref(v___y_355_);
lean_inc(v___y_354_);
lean_inc_ref(v___y_353_);
lean_inc(v___y_352_);
v___x_366_ = lean_apply_12(v___f_349_, v___x_362_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, lean_box(0));
return v___x_366_;
}
else
{
lean_dec_ref(v___y_351_);
lean_dec_ref(v___f_349_);
return v___x_363_;
}
}
else
{
uint8_t v_done_367_; 
lean_dec_ref(v___y_351_);
v_done_367_ = lean_ctor_get_uint8(v_a_364_, sizeof(void*)*1);
if (v_done_367_ == 0)
{
lean_object* v_e_x27_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_386_; 
lean_dec_ref_known(v___x_363_, 1);
v_e_x27_368_ = lean_ctor_get(v_a_364_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v_a_364_);
if (v_isSharedCheck_386_ == 0)
{
v___x_370_ = v_a_364_;
v_isShared_371_ = v_isSharedCheck_386_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_e_x27_368_);
lean_dec(v_a_364_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_386_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; 
lean_inc(v___y_360_);
lean_inc_ref(v___y_359_);
lean_inc(v___y_358_);
lean_inc_ref(v___y_357_);
lean_inc(v___y_356_);
lean_inc_ref(v___y_355_);
lean_inc(v___y_354_);
lean_inc_ref(v___y_353_);
lean_inc(v___y_352_);
lean_inc_ref(v_e_x27_368_);
v___x_372_ = lean_apply_12(v___f_349_, v___x_362_, v_e_x27_368_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, lean_box(0));
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_a_373_);
if (lean_obj_tag(v_a_373_) == 0)
{
lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_384_; 
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_384_ == 0)
{
lean_object* v_unused_385_; 
v_unused_385_ = lean_ctor_get(v___x_372_, 0);
lean_dec(v_unused_385_);
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_384_;
goto v_resetjp_374_;
}
else
{
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_384_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
uint8_t v_done_377_; lean_object* v___x_379_; 
v_done_377_ = lean_ctor_get_uint8(v_a_373_, 0);
lean_dec_ref_known(v_a_373_, 0);
if (v_isShared_371_ == 0)
{
v___x_379_ = v___x_370_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_e_x27_368_);
v___x_379_ = v_reuseFailAlloc_383_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_381_; 
lean_ctor_set_uint8(v___x_379_, sizeof(void*)*1, v_done_377_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_379_);
v___x_381_ = v___x_375_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_373_, 1);
lean_del_object(v___x_370_);
lean_dec_ref(v_e_x27_368_);
return v___x_372_;
}
}
else
{
lean_del_object(v___x_370_);
lean_dec_ref(v_e_x27_368_);
return v___x_372_;
}
}
}
else
{
lean_dec_ref_known(v_a_364_, 1);
lean_dec_ref(v___f_349_);
return v___x_363_;
}
}
}
else
{
lean_dec_ref(v___y_351_);
lean_dec_ref(v___f_349_);
return v___x_363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__4___boxed(lean_object* v___f_387_, lean_object* v_x_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__4(v___f_387_, v_x_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5(lean_object* v___x_401_, lean_object* v___f_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_box(0);
v___x_415_ = l_Lean_Meta_Sym_DSimp_evalGround___redArg(v___x_401_, v___y_403_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_a_416_);
if (lean_obj_tag(v_a_416_) == 0)
{
uint8_t v_done_417_; 
v_done_417_ = lean_ctor_get_uint8(v_a_416_, 0);
lean_dec_ref_known(v_a_416_, 0);
if (v_done_417_ == 0)
{
lean_object* v___x_418_; 
lean_dec_ref_known(v___x_415_, 1);
v___x_418_ = lean_apply_12(v___f_402_, v___x_414_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, lean_box(0));
return v___x_418_;
}
else
{
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec_ref(v___f_402_);
return v___x_415_;
}
}
else
{
uint8_t v_done_419_; 
lean_dec_ref(v___y_403_);
v_done_419_ = lean_ctor_get_uint8(v_a_416_, sizeof(void*)*1);
if (v_done_419_ == 0)
{
lean_object* v_e_x27_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_438_; 
lean_dec_ref_known(v___x_415_, 1);
v_e_x27_420_ = lean_ctor_get(v_a_416_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v_a_416_);
if (v_isSharedCheck_438_ == 0)
{
v___x_422_ = v_a_416_;
v_isShared_423_ = v_isSharedCheck_438_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_e_x27_420_);
lean_dec(v_a_416_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_438_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; 
lean_inc_ref(v_e_x27_420_);
v___x_424_ = lean_apply_12(v___f_402_, v___x_414_, v_e_x27_420_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, lean_box(0));
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
if (lean_obj_tag(v_a_425_) == 0)
{
lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_436_; 
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_436_ == 0)
{
lean_object* v_unused_437_; 
v_unused_437_ = lean_ctor_get(v___x_424_, 0);
lean_dec(v_unused_437_);
v___x_427_ = v___x_424_;
v_isShared_428_ = v_isSharedCheck_436_;
goto v_resetjp_426_;
}
else
{
lean_dec(v___x_424_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_436_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
uint8_t v_done_429_; lean_object* v___x_431_; 
v_done_429_ = lean_ctor_get_uint8(v_a_425_, 0);
lean_dec_ref_known(v_a_425_, 0);
if (v_isShared_423_ == 0)
{
v___x_431_ = v___x_422_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_e_x27_420_);
v___x_431_ = v_reuseFailAlloc_435_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_433_; 
lean_ctor_set_uint8(v___x_431_, sizeof(void*)*1, v_done_429_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_431_);
v___x_433_ = v___x_427_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_425_, 1);
lean_del_object(v___x_422_);
lean_dec_ref(v_e_x27_420_);
return v___x_424_;
}
}
else
{
lean_del_object(v___x_422_);
lean_dec_ref(v_e_x27_420_);
return v___x_424_;
}
}
}
else
{
lean_dec_ref_known(v_a_416_, 1);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___f_402_);
return v___x_415_;
}
}
}
else
{
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec_ref(v___f_402_);
return v___x_415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___boxed(lean_object* v___x_439_, lean_object* v___f_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5(v___x_439_, v___f_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
lean_dec(v___x_439_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6(uint8_t v___x_464_, lean_object* v_e_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_476_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___closed__5));
v___x_477_ = lean_unsigned_to_nat(1u);
v___x_478_ = l_Lean_Expr_isAppOfArity(v_e_465_, v___x_476_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_Meta_Sym_Simp_simpControl(v_e_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_508_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_508_ == 0)
{
v___x_482_ = v___x_479_;
v_isShared_483_ = v_isSharedCheck_508_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_508_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
if (lean_obj_tag(v_a_480_) == 0)
{
uint8_t v_contextDependent_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_494_; 
v_contextDependent_484_ = lean_ctor_get_uint8(v_a_480_, 1);
v_isSharedCheck_494_ = !lean_is_exclusive(v_a_480_);
if (v_isSharedCheck_494_ == 0)
{
v___x_486_ = v_a_480_;
v_isShared_487_ = v_isSharedCheck_494_;
goto v_resetjp_485_;
}
else
{
lean_dec(v_a_480_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_494_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_493_, 1, v_contextDependent_484_);
v___x_489_ = v_reuseFailAlloc_493_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_491_; 
lean_ctor_set_uint8(v___x_489_, 0, v___x_478_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_489_);
v___x_491_ = v___x_482_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
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
else
{
lean_object* v_e_x27_495_; lean_object* v_proof_496_; uint8_t v_contextDependent_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_507_; 
v_e_x27_495_ = lean_ctor_get(v_a_480_, 0);
v_proof_496_ = lean_ctor_get(v_a_480_, 1);
v_contextDependent_497_ = lean_ctor_get_uint8(v_a_480_, sizeof(void*)*2 + 1);
v_isSharedCheck_507_ = !lean_is_exclusive(v_a_480_);
if (v_isSharedCheck_507_ == 0)
{
v___x_499_ = v_a_480_;
v_isShared_500_ = v_isSharedCheck_507_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_proof_496_);
lean_inc(v_e_x27_495_);
lean_dec(v_a_480_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_507_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_e_x27_495_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_proof_496_);
lean_ctor_set_uint8(v_reuseFailAlloc_506_, sizeof(void*)*2 + 1, v_contextDependent_497_);
v___x_502_ = v_reuseFailAlloc_506_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_504_; 
lean_ctor_set_uint8(v___x_502_, sizeof(void*)*2, v___x_478_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_502_);
v___x_504_ = v___x_482_;
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
}
}
else
{
return v___x_479_;
}
}
else
{
uint8_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec_ref(v_e_465_);
v___x_509_ = 0;
v___x_510_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_510_, 0, v___x_464_);
lean_ctor_set_uint8(v___x_510_, 1, v___x_509_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___boxed(lean_object* v___x_512_, lean_object* v_e_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
uint8_t v___x_178344__boxed_524_; lean_object* v_res_525_; 
v___x_178344__boxed_524_ = lean_unbox(v___x_512_);
v_res_525_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6(v___x_178344__boxed_524_, v_e_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__7(lean_object* v_val_526_, lean_object* v_a_527_, lean_object* v___x_528_, lean_object* v_x_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v___x_541_; 
lean_inc_ref(v___y_530_);
v___x_541_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteSimproc(v_val_526_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
if (lean_obj_tag(v_a_542_) == 0)
{
uint8_t v_done_543_; 
v_done_543_ = lean_ctor_get_uint8(v_a_542_, 0);
if (v_done_543_ == 0)
{
uint8_t v_contextDependent_544_; lean_object* v___x_545_; 
lean_dec_ref_known(v___x_541_, 1);
v_contextDependent_544_ = lean_ctor_get_uint8(v_a_542_, 1);
lean_dec_ref_known(v_a_542_, 0);
v___x_545_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_527_, v___x_528_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; uint8_t v___y_548_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
if (v_contextDependent_544_ == 0)
{
return v___x_545_;
}
else
{
if (lean_obj_tag(v_a_546_) == 0)
{
uint8_t v_contextDependent_558_; 
v_contextDependent_558_ = lean_ctor_get_uint8(v_a_546_, 1);
v___y_548_ = v_contextDependent_558_;
goto v___jp_547_;
}
else
{
uint8_t v_contextDependent_559_; 
v_contextDependent_559_ = lean_ctor_get_uint8(v_a_546_, sizeof(void*)*2 + 1);
v___y_548_ = v_contextDependent_559_;
goto v___jp_547_;
}
}
v___jp_547_:
{
if (v___y_548_ == 0)
{
lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_556_; 
lean_inc(v_a_546_);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; 
v_unused_557_ = lean_ctor_get(v___x_545_, 0);
lean_dec(v_unused_557_);
v___x_550_ = v___x_545_;
v_isShared_551_ = v_isSharedCheck_556_;
goto v_resetjp_549_;
}
else
{
lean_dec(v___x_545_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_556_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_546_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_552_);
v___x_554_ = v___x_550_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_552_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
else
{
return v___x_545_;
}
}
}
else
{
return v___x_545_;
}
}
else
{
lean_dec_ref_known(v_a_542_, 0);
lean_dec_ref(v___y_530_);
lean_dec_ref(v___x_528_);
return v___x_541_;
}
}
else
{
uint8_t v_done_560_; 
v_done_560_ = lean_ctor_get_uint8(v_a_542_, sizeof(void*)*2);
if (v_done_560_ == 0)
{
lean_object* v_e_x27_561_; lean_object* v_proof_562_; uint8_t v_contextDependent_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref_known(v___x_541_, 1);
v_e_x27_561_ = lean_ctor_get(v_a_542_, 0);
v_proof_562_ = lean_ctor_get(v_a_542_, 1);
v_contextDependent_563_ = lean_ctor_get_uint8(v_a_542_, sizeof(void*)*2 + 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_a_542_);
if (v_isSharedCheck_613_ == 0)
{
v___x_565_ = v_a_542_;
v_isShared_566_ = v_isSharedCheck_613_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_proof_562_);
lean_inc(v_e_x27_561_);
lean_dec(v_a_542_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_613_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; 
lean_inc_ref(v_e_x27_561_);
v___x_567_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_527_, v___x_528_, v_e_x27_561_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_612_; 
v_a_568_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_612_ == 0)
{
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_612_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_612_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
if (lean_obj_tag(v_a_568_) == 0)
{
uint8_t v_done_572_; uint8_t v_contextDependent_573_; uint8_t v___y_575_; 
lean_dec_ref(v___y_530_);
v_done_572_ = lean_ctor_get_uint8(v_a_568_, 0);
v_contextDependent_573_ = lean_ctor_get_uint8(v_a_568_, 1);
lean_dec_ref_known(v_a_568_, 0);
if (v_contextDependent_563_ == 0)
{
v___y_575_ = v_contextDependent_573_;
goto v___jp_574_;
}
else
{
v___y_575_ = v_contextDependent_563_;
goto v___jp_574_;
}
v___jp_574_:
{
lean_object* v___x_577_; 
if (v_isShared_566_ == 0)
{
v___x_577_ = v___x_565_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_e_x27_561_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_proof_562_);
v___x_577_ = v_reuseFailAlloc_581_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_579_; 
lean_ctor_set_uint8(v___x_577_, sizeof(void*)*2, v_done_572_);
lean_ctor_set_uint8(v___x_577_, sizeof(void*)*2 + 1, v___y_575_);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v___x_577_);
v___x_579_ = v___x_570_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___x_577_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
else
{
lean_object* v_e_x27_582_; lean_object* v_proof_583_; uint8_t v_done_584_; uint8_t v_contextDependent_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_611_; 
lean_del_object(v___x_570_);
lean_del_object(v___x_565_);
v_e_x27_582_ = lean_ctor_get(v_a_568_, 0);
v_proof_583_ = lean_ctor_get(v_a_568_, 1);
v_done_584_ = lean_ctor_get_uint8(v_a_568_, sizeof(void*)*2);
v_contextDependent_585_ = lean_ctor_get_uint8(v_a_568_, sizeof(void*)*2 + 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_a_568_);
if (v_isSharedCheck_611_ == 0)
{
v___x_587_ = v_a_568_;
v_isShared_588_ = v_isSharedCheck_611_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_proof_583_);
lean_inc(v_e_x27_582_);
lean_dec(v_a_568_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_611_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; 
lean_inc_ref(v_e_x27_582_);
v___x_589_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_530_, v_e_x27_561_, v_proof_562_, v_e_x27_582_, v_proof_583_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_602_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_602_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_602_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_602_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
uint8_t v___y_595_; 
if (v_contextDependent_563_ == 0)
{
v___y_595_ = v_contextDependent_585_;
goto v___jp_594_;
}
else
{
v___y_595_ = v_contextDependent_563_;
goto v___jp_594_;
}
v___jp_594_:
{
lean_object* v___x_597_; 
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v_a_590_);
v___x_597_ = v___x_587_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_e_x27_582_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_a_590_);
lean_ctor_set_uint8(v_reuseFailAlloc_601_, sizeof(void*)*2, v_done_584_);
v___x_597_ = v_reuseFailAlloc_601_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_599_; 
lean_ctor_set_uint8(v___x_597_, sizeof(void*)*2 + 1, v___y_595_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 0, v___x_597_);
v___x_599_ = v___x_592_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_del_object(v___x_587_);
lean_dec_ref(v_e_x27_582_);
v_a_603_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_589_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_589_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_565_);
lean_dec_ref(v_proof_562_);
lean_dec_ref(v_e_x27_561_);
lean_dec_ref(v___y_530_);
return v___x_567_;
}
}
}
else
{
lean_dec_ref_known(v_a_542_, 2);
lean_dec_ref(v___y_530_);
lean_dec_ref(v___x_528_);
return v___x_541_;
}
}
}
else
{
lean_dec_ref(v___y_530_);
lean_dec_ref(v___x_528_);
return v___x_541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__7___boxed(lean_object* v_val_614_, lean_object* v_a_615_, lean_object* v___x_616_, lean_object* v_x_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__7(v_val_614_, v_a_615_, v___x_616_, v_x_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v_a_615_);
lean_dec(v_val_614_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__8(lean_object* v___x_630_, lean_object* v___f_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = lean_box(0);
v___x_644_ = l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(v___y_632_, v___x_630_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
if (lean_obj_tag(v_a_645_) == 0)
{
uint8_t v_done_646_; 
v_done_646_ = lean_ctor_get_uint8(v_a_645_, 0);
if (v_done_646_ == 0)
{
uint8_t v_contextDependent_647_; lean_object* v___x_648_; 
lean_dec_ref_known(v___x_644_, 1);
v_contextDependent_647_ = lean_ctor_get_uint8(v_a_645_, 1);
lean_dec_ref_known(v_a_645_, 0);
v___x_648_ = lean_apply_12(v___f_631_, v___x_643_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, lean_box(0));
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; uint8_t v___y_651_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_a_649_);
if (v_contextDependent_647_ == 0)
{
lean_dec(v_a_649_);
return v___x_648_;
}
else
{
if (lean_obj_tag(v_a_649_) == 0)
{
uint8_t v_contextDependent_661_; 
v_contextDependent_661_ = lean_ctor_get_uint8(v_a_649_, 1);
v___y_651_ = v_contextDependent_661_;
goto v___jp_650_;
}
else
{
uint8_t v_contextDependent_662_; 
v_contextDependent_662_ = lean_ctor_get_uint8(v_a_649_, sizeof(void*)*2 + 1);
v___y_651_ = v_contextDependent_662_;
goto v___jp_650_;
}
}
v___jp_650_:
{
if (v___y_651_ == 0)
{
lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_659_; 
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_659_ == 0)
{
lean_object* v_unused_660_; 
v_unused_660_ = lean_ctor_get(v___x_648_, 0);
lean_dec(v_unused_660_);
v___x_653_ = v___x_648_;
v_isShared_654_ = v_isSharedCheck_659_;
goto v_resetjp_652_;
}
else
{
lean_dec(v___x_648_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_659_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_655_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_649_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v___x_655_);
v___x_657_ = v___x_653_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
else
{
lean_dec(v_a_649_);
return v___x_648_;
}
}
}
else
{
return v___x_648_;
}
}
else
{
lean_dec_ref_known(v_a_645_, 0);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec_ref(v___f_631_);
return v___x_644_;
}
}
else
{
uint8_t v_done_663_; 
v_done_663_ = lean_ctor_get_uint8(v_a_645_, sizeof(void*)*2);
if (v_done_663_ == 0)
{
lean_object* v_e_x27_664_; lean_object* v_proof_665_; uint8_t v_contextDependent_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_716_; 
lean_dec_ref_known(v___x_644_, 1);
v_e_x27_664_ = lean_ctor_get(v_a_645_, 0);
v_proof_665_ = lean_ctor_get(v_a_645_, 1);
v_contextDependent_666_ = lean_ctor_get_uint8(v_a_645_, sizeof(void*)*2 + 1);
v_isSharedCheck_716_ = !lean_is_exclusive(v_a_645_);
if (v_isSharedCheck_716_ == 0)
{
v___x_668_ = v_a_645_;
v_isShared_669_ = v_isSharedCheck_716_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_proof_665_);
lean_inc(v_e_x27_664_);
lean_dec(v_a_645_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_716_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_670_; 
lean_inc(v___y_641_);
lean_inc_ref(v___y_640_);
lean_inc(v___y_639_);
lean_inc_ref(v___y_638_);
lean_inc(v___y_637_);
lean_inc_ref(v___y_636_);
lean_inc_ref(v_e_x27_664_);
v___x_670_ = lean_apply_12(v___f_631_, v___x_643_, v_e_x27_664_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, lean_box(0));
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_715_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_715_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_715_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_715_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
if (lean_obj_tag(v_a_671_) == 0)
{
uint8_t v_done_675_; uint8_t v_contextDependent_676_; uint8_t v___y_678_; 
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec_ref(v___y_632_);
v_done_675_ = lean_ctor_get_uint8(v_a_671_, 0);
v_contextDependent_676_ = lean_ctor_get_uint8(v_a_671_, 1);
lean_dec_ref_known(v_a_671_, 0);
if (v_contextDependent_666_ == 0)
{
v___y_678_ = v_contextDependent_676_;
goto v___jp_677_;
}
else
{
v___y_678_ = v_contextDependent_666_;
goto v___jp_677_;
}
v___jp_677_:
{
lean_object* v___x_680_; 
if (v_isShared_669_ == 0)
{
v___x_680_ = v___x_668_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_e_x27_664_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_proof_665_);
v___x_680_ = v_reuseFailAlloc_684_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_682_; 
lean_ctor_set_uint8(v___x_680_, sizeof(void*)*2, v_done_675_);
lean_ctor_set_uint8(v___x_680_, sizeof(void*)*2 + 1, v___y_678_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_680_);
v___x_682_ = v___x_673_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
else
{
lean_object* v_e_x27_685_; lean_object* v_proof_686_; uint8_t v_done_687_; uint8_t v_contextDependent_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_714_; 
lean_del_object(v___x_673_);
lean_del_object(v___x_668_);
v_e_x27_685_ = lean_ctor_get(v_a_671_, 0);
v_proof_686_ = lean_ctor_get(v_a_671_, 1);
v_done_687_ = lean_ctor_get_uint8(v_a_671_, sizeof(void*)*2);
v_contextDependent_688_ = lean_ctor_get_uint8(v_a_671_, sizeof(void*)*2 + 1);
v_isSharedCheck_714_ = !lean_is_exclusive(v_a_671_);
if (v_isSharedCheck_714_ == 0)
{
v___x_690_ = v_a_671_;
v_isShared_691_ = v_isSharedCheck_714_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_proof_686_);
lean_inc(v_e_x27_685_);
lean_dec(v_a_671_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_714_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; 
lean_inc_ref(v_e_x27_685_);
v___x_692_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_632_, v_e_x27_664_, v_proof_665_, v_e_x27_685_, v_proof_686_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_705_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_705_ == 0)
{
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_705_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_705_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
uint8_t v___y_698_; 
if (v_contextDependent_666_ == 0)
{
v___y_698_ = v_contextDependent_688_;
goto v___jp_697_;
}
else
{
v___y_698_ = v_contextDependent_666_;
goto v___jp_697_;
}
v___jp_697_:
{
lean_object* v___x_700_; 
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 1, v_a_693_);
v___x_700_ = v___x_690_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_e_x27_685_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_a_693_);
lean_ctor_set_uint8(v_reuseFailAlloc_704_, sizeof(void*)*2, v_done_687_);
v___x_700_ = v_reuseFailAlloc_704_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
lean_ctor_set_uint8(v___x_700_, sizeof(void*)*2 + 1, v___y_698_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v___x_700_);
v___x_702_ = v___x_695_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
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
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
lean_del_object(v___x_690_);
lean_dec_ref(v_e_x27_685_);
v_a_706_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_692_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_692_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_668_);
lean_dec_ref(v_proof_665_);
lean_dec_ref(v_e_x27_664_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec_ref(v___y_632_);
return v___x_670_;
}
}
}
else
{
lean_dec_ref_known(v_a_645_, 2);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec_ref(v___f_631_);
return v___x_644_;
}
}
}
else
{
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec_ref(v___f_631_);
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__8___boxed(lean_object* v___x_717_, lean_object* v___f_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__8(v___x_717_, v___f_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
lean_dec_ref(v___x_717_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__7___redArg(lean_object* v_x_731_){
_start:
{
if (lean_obj_tag(v_x_731_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
v_a_733_ = lean_ctor_get(v_x_731_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v_x_731_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v_x_731_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v_x_731_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
lean_ctor_set_tag(v___x_735_, 1);
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
v_a_741_ = lean_ctor_get(v_x_731_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v_x_731_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v_x_731_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v_x_731_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
lean_ctor_set_tag(v___x_743_, 0);
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__7___redArg___boxed(lean_object* v_x_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__7___redArg(v_x_749_);
return v_res_751_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__8(lean_object* v_e_752_){
_start:
{
if (lean_obj_tag(v_e_752_) == 0)
{
uint8_t v___x_753_; 
v___x_753_ = 2;
return v___x_753_;
}
else
{
uint8_t v___x_754_; 
v___x_754_ = 0;
return v___x_754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__8___boxed(lean_object* v_e_755_){
_start:
{
uint8_t v_res_756_; lean_object* v_r_757_; 
v_res_756_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__8(v_e_755_);
lean_dec_ref(v_e_755_);
v_r_757_ = lean_box(v_res_756_);
return v_r_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1_spec__1(lean_object* v_msgData_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_764_; lean_object* v_env_765_; uint8_t v___x_766_; lean_object* v_env_767_; lean_object* v___x_768_; lean_object* v_toCold_769_; lean_object* v_mctx_770_; lean_object* v_lctx_771_; lean_object* v_options_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_764_ = lean_st_ref_get(v___y_762_);
v_env_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc_ref(v_env_765_);
lean_dec(v___x_764_);
v___x_766_ = 0;
v_env_767_ = l_Lean_Environment_setRecordingDeps(v_env_765_, v___x_766_);
v___x_768_ = lean_st_ref_get(v___y_760_);
v_toCold_769_ = lean_ctor_get(v___y_761_, 0);
v_mctx_770_ = lean_ctor_get(v___x_768_, 0);
lean_inc_ref(v_mctx_770_);
lean_dec(v___x_768_);
v_lctx_771_ = lean_ctor_get(v___y_759_, 2);
v_options_772_ = lean_ctor_get(v_toCold_769_, 2);
lean_inc_ref(v_options_772_);
lean_inc_ref(v_lctx_771_);
v___x_773_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_773_, 0, v_env_767_);
lean_ctor_set(v___x_773_, 1, v_mctx_770_);
lean_ctor_set(v___x_773_, 2, v_lctx_771_);
lean_ctor_set(v___x_773_, 3, v_options_772_);
v___x_774_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v_msgData_758_);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1_spec__1___boxed(lean_object* v_msgData_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1_spec__1(v_msgData_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6_spec__7(size_t v_sz_783_, size_t v_i_784_, lean_object* v_bs_785_){
_start:
{
uint8_t v___x_786_; 
v___x_786_ = lean_usize_dec_lt(v_i_784_, v_sz_783_);
if (v___x_786_ == 0)
{
return v_bs_785_;
}
else
{
lean_object* v_v_787_; lean_object* v_msg_788_; lean_object* v___x_789_; lean_object* v_bs_x27_790_; size_t v___x_791_; size_t v___x_792_; lean_object* v___x_793_; 
v_v_787_ = lean_array_uget_borrowed(v_bs_785_, v_i_784_);
v_msg_788_ = lean_ctor_get(v_v_787_, 1);
lean_inc_ref(v_msg_788_);
v___x_789_ = lean_unsigned_to_nat(0u);
v_bs_x27_790_ = lean_array_uset(v_bs_785_, v_i_784_, v___x_789_);
v___x_791_ = ((size_t)1ULL);
v___x_792_ = lean_usize_add(v_i_784_, v___x_791_);
v___x_793_ = lean_array_uset(v_bs_x27_790_, v_i_784_, v_msg_788_);
v_i_784_ = v___x_792_;
v_bs_785_ = v___x_793_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6_spec__7___boxed(lean_object* v_sz_795_, lean_object* v_i_796_, lean_object* v_bs_797_){
_start:
{
size_t v_sz_boxed_798_; size_t v_i_boxed_799_; lean_object* v_res_800_; 
v_sz_boxed_798_ = lean_unbox_usize(v_sz_795_);
lean_dec(v_sz_795_);
v_i_boxed_799_ = lean_unbox_usize(v_i_796_);
lean_dec(v_i_796_);
v_res_800_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6_spec__7(v_sz_boxed_798_, v_i_boxed_799_, v_bs_797_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6___redArg(lean_object* v_oldTraces_801_, lean_object* v_data_802_, lean_object* v_ref_803_, lean_object* v_msg_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_toCold_810_; lean_object* v_currRecDepth_811_; lean_object* v_ref_812_; uint16_t v_optionFlags_813_; uint8_t v_suppressElabErrors_814_; uint8_t v_checkDeprecated_815_; uint8_t v_isRecordingDeps_816_; lean_object* v_ref_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v_traceState_820_; lean_object* v_traces_821_; lean_object* v___x_822_; size_t v_sz_823_; size_t v___x_824_; lean_object* v___x_825_; lean_object* v_msg_826_; lean_object* v___x_827_; lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_866_; 
v_toCold_810_ = lean_ctor_get(v___y_807_, 0);
v_currRecDepth_811_ = lean_ctor_get(v___y_807_, 1);
v_ref_812_ = lean_ctor_get(v___y_807_, 2);
v_optionFlags_813_ = lean_ctor_get_uint16(v___y_807_, sizeof(void*)*3);
v_suppressElabErrors_814_ = lean_ctor_get_uint8(v___y_807_, sizeof(void*)*3 + 2);
v_checkDeprecated_815_ = lean_ctor_get_uint8(v___y_807_, sizeof(void*)*3 + 3);
v_isRecordingDeps_816_ = lean_ctor_get_uint8(v___y_807_, sizeof(void*)*3 + 4);
v_ref_817_ = l_Lean_replaceRef(v_ref_803_, v_ref_812_);
lean_inc(v_currRecDepth_811_);
lean_inc_ref(v_toCold_810_);
v___x_818_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_818_, 0, v_toCold_810_);
lean_ctor_set(v___x_818_, 1, v_currRecDepth_811_);
lean_ctor_set(v___x_818_, 2, v_ref_817_);
lean_ctor_set_uint16(v___x_818_, sizeof(void*)*3, v_optionFlags_813_);
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*3 + 2, v_suppressElabErrors_814_);
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*3 + 3, v_checkDeprecated_815_);
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*3 + 4, v_isRecordingDeps_816_);
v___x_819_ = lean_st_ref_get(v___y_808_);
v_traceState_820_ = lean_ctor_get(v___x_819_, 4);
lean_inc_ref(v_traceState_820_);
lean_dec(v___x_819_);
v_traces_821_ = lean_ctor_get(v_traceState_820_, 0);
lean_inc_ref(v_traces_821_);
lean_dec_ref(v_traceState_820_);
v___x_822_ = l_Lean_PersistentArray_toArray___redArg(v_traces_821_);
lean_dec_ref(v_traces_821_);
v_sz_823_ = lean_array_size(v___x_822_);
v___x_824_ = ((size_t)0ULL);
v___x_825_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6_spec__7(v_sz_823_, v___x_824_, v___x_822_);
v_msg_826_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_826_, 0, v_data_802_);
lean_ctor_set(v_msg_826_, 1, v_msg_804_);
lean_ctor_set(v_msg_826_, 2, v___x_825_);
v___x_827_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1_spec__1(v_msg_826_, v___y_805_, v___y_806_, v___x_818_, v___y_808_);
lean_dec_ref_known(v___x_818_, 3);
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_866_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_866_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_866_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_832_; lean_object* v_traceState_833_; lean_object* v_env_834_; lean_object* v_nextMacroScope_835_; lean_object* v_ngen_836_; lean_object* v_auxDeclNGen_837_; lean_object* v_cache_838_; lean_object* v_recordedDeps_839_; lean_object* v_messages_840_; lean_object* v_infoState_841_; lean_object* v_snapshotTasks_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_865_; 
v___x_832_ = lean_st_ref_take(v___y_808_);
v_traceState_833_ = lean_ctor_get(v___x_832_, 4);
v_env_834_ = lean_ctor_get(v___x_832_, 0);
v_nextMacroScope_835_ = lean_ctor_get(v___x_832_, 1);
v_ngen_836_ = lean_ctor_get(v___x_832_, 2);
v_auxDeclNGen_837_ = lean_ctor_get(v___x_832_, 3);
v_cache_838_ = lean_ctor_get(v___x_832_, 5);
v_recordedDeps_839_ = lean_ctor_get(v___x_832_, 6);
v_messages_840_ = lean_ctor_get(v___x_832_, 7);
v_infoState_841_ = lean_ctor_get(v___x_832_, 8);
v_snapshotTasks_842_ = lean_ctor_get(v___x_832_, 9);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_865_ == 0)
{
v___x_844_ = v___x_832_;
v_isShared_845_ = v_isSharedCheck_865_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_snapshotTasks_842_);
lean_inc(v_infoState_841_);
lean_inc(v_messages_840_);
lean_inc(v_recordedDeps_839_);
lean_inc(v_cache_838_);
lean_inc(v_traceState_833_);
lean_inc(v_auxDeclNGen_837_);
lean_inc(v_ngen_836_);
lean_inc(v_nextMacroScope_835_);
lean_inc(v_env_834_);
lean_dec(v___x_832_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_865_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
uint64_t v_tid_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_863_; 
v_tid_846_ = lean_ctor_get_uint64(v_traceState_833_, sizeof(void*)*1);
v_isSharedCheck_863_ = !lean_is_exclusive(v_traceState_833_);
if (v_isSharedCheck_863_ == 0)
{
lean_object* v_unused_864_; 
v_unused_864_ = lean_ctor_get(v_traceState_833_, 0);
lean_dec(v_unused_864_);
v___x_848_ = v_traceState_833_;
v_isShared_849_ = v_isSharedCheck_863_;
goto v_resetjp_847_;
}
else
{
lean_dec(v_traceState_833_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_863_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_850_ = lean_box(0);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v_ref_803_);
lean_ctor_set(v___x_851_, 1, v_a_828_);
v___x_852_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_801_, v___x_851_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_852_);
v___x_854_ = v___x_848_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_852_);
lean_ctor_set_uint64(v_reuseFailAlloc_862_, sizeof(void*)*1, v_tid_846_);
v___x_854_ = v_reuseFailAlloc_862_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_856_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v___x_854_);
v___x_856_ = v___x_844_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_env_834_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_nextMacroScope_835_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_ngen_836_);
lean_ctor_set(v_reuseFailAlloc_861_, 3, v_auxDeclNGen_837_);
lean_ctor_set(v_reuseFailAlloc_861_, 4, v___x_854_);
lean_ctor_set(v_reuseFailAlloc_861_, 5, v_cache_838_);
lean_ctor_set(v_reuseFailAlloc_861_, 6, v_recordedDeps_839_);
lean_ctor_set(v_reuseFailAlloc_861_, 7, v_messages_840_);
lean_ctor_set(v_reuseFailAlloc_861_, 8, v_infoState_841_);
lean_ctor_set(v_reuseFailAlloc_861_, 9, v_snapshotTasks_842_);
v___x_856_ = v_reuseFailAlloc_861_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_857_ = lean_st_ref_put(v___y_808_, v___x_856_);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v___x_850_);
v___x_859_ = v___x_830_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_850_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6___redArg___boxed(lean_object* v_oldTraces_867_, lean_object* v_data_868_, lean_object* v_ref_869_, lean_object* v_msg_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6___redArg(v_oldTraces_867_, v_data_868_, v_ref_869_, v_msg_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__9(lean_object* v_opts_877_, lean_object* v_opt_878_){
_start:
{
lean_object* v_name_879_; lean_object* v_defValue_880_; lean_object* v_map_881_; lean_object* v___x_882_; 
v_name_879_ = lean_ctor_get(v_opt_878_, 0);
v_defValue_880_ = lean_ctor_get(v_opt_878_, 1);
v_map_881_ = lean_ctor_get(v_opts_877_, 0);
v___x_882_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_881_, v_name_879_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_inc(v_defValue_880_);
return v_defValue_880_;
}
else
{
lean_object* v_val_883_; 
v_val_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_val_883_);
lean_dec_ref_known(v___x_882_, 1);
if (lean_obj_tag(v_val_883_) == 3)
{
lean_object* v_v_884_; 
v_v_884_ = lean_ctor_get(v_val_883_, 0);
lean_inc(v_v_884_);
lean_dec_ref_known(v_val_883_, 1);
return v_v_884_;
}
else
{
lean_dec(v_val_883_);
lean_inc(v_defValue_880_);
return v_defValue_880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__9___boxed(lean_object* v_opts_885_, lean_object* v_opt_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__9(v_opts_885_, v_opt_886_);
lean_dec_ref(v_opt_886_);
lean_dec_ref(v_opts_885_);
return v_res_887_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__0(void){
_start:
{
lean_object* v___x_888_; double v___x_889_; 
v___x_888_ = lean_unsigned_to_nat(0u);
v___x_889_ = lean_float_of_nat(v___x_888_);
return v___x_889_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__2(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__1));
v___x_892_ = l_Lean_stringToMessageData(v___x_891_);
return v___x_892_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__3(void){
_start:
{
lean_object* v___x_893_; double v___x_894_; 
v___x_893_ = lean_unsigned_to_nat(1000u);
v___x_894_ = lean_float_of_nat(v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5(lean_object* v_cls_895_, uint8_t v_collapsed_896_, lean_object* v_tag_897_, lean_object* v_opts_898_, uint8_t v_clsEnabled_899_, lean_object* v_oldTraces_900_, lean_object* v_msg_901_, lean_object* v_resStartStop_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_fst_915_; lean_object* v_snd_916_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v_data_920_; lean_object* v_fst_923_; lean_object* v_snd_924_; lean_object* v___x_925_; uint8_t v___x_926_; lean_object* v___y_928_; lean_object* v_a_929_; uint8_t v___y_944_; double v___y_976_; 
v_fst_915_ = lean_ctor_get(v_resStartStop_902_, 0);
lean_inc(v_fst_915_);
v_snd_916_ = lean_ctor_get(v_resStartStop_902_, 1);
lean_inc(v_snd_916_);
lean_dec_ref(v_resStartStop_902_);
v_fst_923_ = lean_ctor_get(v_snd_916_, 0);
lean_inc(v_fst_923_);
v_snd_924_ = lean_ctor_get(v_snd_916_, 1);
lean_inc(v_snd_924_);
lean_dec(v_snd_916_);
v___x_925_ = l_Lean_trace_profiler;
v___x_926_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__4(v_opts_898_, v___x_925_);
if (v___x_926_ == 0)
{
v___y_944_ = v___x_926_;
goto v___jp_943_;
}
else
{
lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_981_ = l_Lean_trace_profiler_useHeartbeats;
v___x_982_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__4(v_opts_898_, v___x_981_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v___x_984_; double v___x_985_; double v___x_986_; double v___x_987_; 
v___x_983_ = l_Lean_trace_profiler_threshold;
v___x_984_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__9(v_opts_898_, v___x_983_);
v___x_985_ = lean_float_of_nat(v___x_984_);
v___x_986_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__3);
v___x_987_ = lean_float_div(v___x_985_, v___x_986_);
v___y_976_ = v___x_987_;
goto v___jp_975_;
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; double v___x_990_; 
v___x_988_ = l_Lean_trace_profiler_threshold;
v___x_989_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__9(v_opts_898_, v___x_988_);
v___x_990_ = lean_float_of_nat(v___x_989_);
v___y_976_ = v___x_990_;
goto v___jp_975_;
}
}
v___jp_917_:
{
lean_object* v___x_921_; 
lean_inc(v___y_918_);
v___x_921_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6___redArg(v_oldTraces_900_, v_data_920_, v___y_918_, v___y_919_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v___x_922_; 
lean_dec_ref_known(v___x_921_, 1);
v___x_922_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__7___redArg(v_fst_915_);
return v___x_922_;
}
else
{
lean_dec(v_fst_915_);
return v___x_921_;
}
}
v___jp_927_:
{
uint8_t v_result_930_; lean_object* v___x_931_; lean_object* v___x_932_; double v___x_933_; lean_object* v_data_934_; 
v_result_930_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__8(v_fst_915_);
v___x_931_ = lean_box(v_result_930_);
v___x_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
v___x_933_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__0);
lean_inc_ref(v_tag_897_);
lean_inc_ref(v___x_932_);
lean_inc(v_cls_895_);
v_data_934_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_934_, 0, v_cls_895_);
lean_ctor_set(v_data_934_, 1, v___x_932_);
lean_ctor_set(v_data_934_, 2, v_tag_897_);
lean_ctor_set_float(v_data_934_, sizeof(void*)*3, v___x_933_);
lean_ctor_set_float(v_data_934_, sizeof(void*)*3 + 8, v___x_933_);
lean_ctor_set_uint8(v_data_934_, sizeof(void*)*3 + 16, v_collapsed_896_);
if (v___x_926_ == 0)
{
lean_dec_ref_known(v___x_932_, 1);
lean_dec(v_snd_924_);
lean_dec(v_fst_923_);
lean_dec_ref(v_tag_897_);
lean_dec(v_cls_895_);
v___y_918_ = v___y_928_;
v___y_919_ = v_a_929_;
v_data_920_ = v_data_934_;
goto v___jp_917_;
}
else
{
lean_object* v_data_935_; double v___x_936_; double v___x_937_; 
lean_dec_ref_known(v_data_934_, 3);
v_data_935_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_935_, 0, v_cls_895_);
lean_ctor_set(v_data_935_, 1, v___x_932_);
lean_ctor_set(v_data_935_, 2, v_tag_897_);
v___x_936_ = lean_unbox_float(v_fst_923_);
lean_dec(v_fst_923_);
lean_ctor_set_float(v_data_935_, sizeof(void*)*3, v___x_936_);
v___x_937_ = lean_unbox_float(v_snd_924_);
lean_dec(v_snd_924_);
lean_ctor_set_float(v_data_935_, sizeof(void*)*3 + 8, v___x_937_);
lean_ctor_set_uint8(v_data_935_, sizeof(void*)*3 + 16, v_collapsed_896_);
v___y_918_ = v___y_928_;
v___y_919_ = v_a_929_;
v_data_920_ = v_data_935_;
goto v___jp_917_;
}
}
v___jp_938_:
{
lean_object* v_ref_939_; lean_object* v___x_940_; 
v_ref_939_ = lean_ctor_get(v___y_912_, 2);
lean_inc(v___y_913_);
lean_inc_ref(v___y_912_);
lean_inc(v___y_911_);
lean_inc_ref(v___y_910_);
lean_inc(v___y_909_);
lean_inc_ref(v___y_908_);
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
lean_inc(v___y_905_);
lean_inc(v___y_904_);
lean_inc_ref(v___y_903_);
lean_inc(v_fst_915_);
v___x_940_ = lean_apply_13(v_msg_901_, v_fst_915_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, lean_box(0));
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_940_, 1);
v___y_928_ = v_ref_939_;
v_a_929_ = v_a_941_;
goto v___jp_927_;
}
else
{
lean_object* v___x_942_; 
lean_dec_ref_known(v___x_940_, 1);
v___x_942_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__2);
v___y_928_ = v_ref_939_;
v_a_929_ = v___x_942_;
goto v___jp_927_;
}
}
v___jp_943_:
{
if (v_clsEnabled_899_ == 0)
{
if (v___y_944_ == 0)
{
lean_object* v___x_945_; lean_object* v_traceState_946_; lean_object* v_env_947_; lean_object* v_nextMacroScope_948_; lean_object* v_ngen_949_; lean_object* v_auxDeclNGen_950_; lean_object* v_cache_951_; lean_object* v_recordedDeps_952_; lean_object* v_messages_953_; lean_object* v_infoState_954_; lean_object* v_snapshotTasks_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_974_; 
lean_dec(v_snd_924_);
lean_dec(v_fst_923_);
lean_dec_ref(v_msg_901_);
lean_dec_ref(v_tag_897_);
lean_dec(v_cls_895_);
v___x_945_ = lean_st_ref_take(v___y_913_);
v_traceState_946_ = lean_ctor_get(v___x_945_, 4);
v_env_947_ = lean_ctor_get(v___x_945_, 0);
v_nextMacroScope_948_ = lean_ctor_get(v___x_945_, 1);
v_ngen_949_ = lean_ctor_get(v___x_945_, 2);
v_auxDeclNGen_950_ = lean_ctor_get(v___x_945_, 3);
v_cache_951_ = lean_ctor_get(v___x_945_, 5);
v_recordedDeps_952_ = lean_ctor_get(v___x_945_, 6);
v_messages_953_ = lean_ctor_get(v___x_945_, 7);
v_infoState_954_ = lean_ctor_get(v___x_945_, 8);
v_snapshotTasks_955_ = lean_ctor_get(v___x_945_, 9);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_974_ == 0)
{
v___x_957_ = v___x_945_;
v_isShared_958_ = v_isSharedCheck_974_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_snapshotTasks_955_);
lean_inc(v_infoState_954_);
lean_inc(v_messages_953_);
lean_inc(v_recordedDeps_952_);
lean_inc(v_cache_951_);
lean_inc(v_traceState_946_);
lean_inc(v_auxDeclNGen_950_);
lean_inc(v_ngen_949_);
lean_inc(v_nextMacroScope_948_);
lean_inc(v_env_947_);
lean_dec(v___x_945_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_974_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
uint64_t v_tid_959_; lean_object* v_traces_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_973_; 
v_tid_959_ = lean_ctor_get_uint64(v_traceState_946_, sizeof(void*)*1);
v_traces_960_ = lean_ctor_get(v_traceState_946_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v_traceState_946_);
if (v_isSharedCheck_973_ == 0)
{
v___x_962_ = v_traceState_946_;
v_isShared_963_ = v_isSharedCheck_973_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_traces_960_);
lean_dec(v_traceState_946_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_973_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_964_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_900_, v_traces_960_);
lean_dec_ref(v_traces_960_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 0, v___x_964_);
v___x_966_ = v___x_962_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_964_);
lean_ctor_set_uint64(v_reuseFailAlloc_972_, sizeof(void*)*1, v_tid_959_);
v___x_966_ = v_reuseFailAlloc_972_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_968_; 
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 4, v___x_966_);
v___x_968_ = v___x_957_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_env_947_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v_nextMacroScope_948_);
lean_ctor_set(v_reuseFailAlloc_971_, 2, v_ngen_949_);
lean_ctor_set(v_reuseFailAlloc_971_, 3, v_auxDeclNGen_950_);
lean_ctor_set(v_reuseFailAlloc_971_, 4, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_971_, 5, v_cache_951_);
lean_ctor_set(v_reuseFailAlloc_971_, 6, v_recordedDeps_952_);
lean_ctor_set(v_reuseFailAlloc_971_, 7, v_messages_953_);
lean_ctor_set(v_reuseFailAlloc_971_, 8, v_infoState_954_);
lean_ctor_set(v_reuseFailAlloc_971_, 9, v_snapshotTasks_955_);
v___x_968_ = v_reuseFailAlloc_971_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = lean_st_ref_put(v___y_913_, v___x_968_);
v___x_970_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__7___redArg(v_fst_915_);
return v___x_970_;
}
}
}
}
}
else
{
goto v___jp_938_;
}
}
else
{
goto v___jp_938_;
}
}
v___jp_975_:
{
double v___x_977_; double v___x_978_; double v___x_979_; uint8_t v___x_980_; 
v___x_977_ = lean_unbox_float(v_snd_924_);
v___x_978_ = lean_unbox_float(v_fst_923_);
v___x_979_ = lean_float_sub(v___x_977_, v___x_978_);
v___x_980_ = lean_float_decLt(v___y_976_, v___x_979_);
v___y_944_ = v___x_980_;
goto v___jp_943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___boxed(lean_object** _args){
lean_object* v_cls_991_ = _args[0];
lean_object* v_collapsed_992_ = _args[1];
lean_object* v_tag_993_ = _args[2];
lean_object* v_opts_994_ = _args[3];
lean_object* v_clsEnabled_995_ = _args[4];
lean_object* v_oldTraces_996_ = _args[5];
lean_object* v_msg_997_ = _args[6];
lean_object* v_resStartStop_998_ = _args[7];
lean_object* v___y_999_ = _args[8];
lean_object* v___y_1000_ = _args[9];
lean_object* v___y_1001_ = _args[10];
lean_object* v___y_1002_ = _args[11];
lean_object* v___y_1003_ = _args[12];
lean_object* v___y_1004_ = _args[13];
lean_object* v___y_1005_ = _args[14];
lean_object* v___y_1006_ = _args[15];
lean_object* v___y_1007_ = _args[16];
lean_object* v___y_1008_ = _args[17];
lean_object* v___y_1009_ = _args[18];
lean_object* v___y_1010_ = _args[19];
_start:
{
uint8_t v_collapsed_boxed_1011_; uint8_t v_clsEnabled_boxed_1012_; lean_object* v_res_1013_; 
v_collapsed_boxed_1011_ = lean_unbox(v_collapsed_992_);
v_clsEnabled_boxed_1012_ = lean_unbox(v_clsEnabled_995_);
v_res_1013_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5(v_cls_991_, v_collapsed_boxed_1011_, v_tag_993_, v_opts_994_, v_clsEnabled_boxed_1012_, v_oldTraces_996_, v_msg_997_, v_resStartStop_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec_ref(v_opts_994_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___redArg(lean_object* v_cls_1017_, lean_object* v_msg_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_ref_1024_; lean_object* v___x_1025_; lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1071_; 
v_ref_1024_ = lean_ctor_get(v___y_1021_, 2);
v___x_1025_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1_spec__1(v_msg_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1071_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1071_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v_traceState_1031_; lean_object* v_env_1032_; lean_object* v_nextMacroScope_1033_; lean_object* v_ngen_1034_; lean_object* v_auxDeclNGen_1035_; lean_object* v_cache_1036_; lean_object* v_recordedDeps_1037_; lean_object* v_messages_1038_; lean_object* v_infoState_1039_; lean_object* v_snapshotTasks_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1070_; 
v___x_1030_ = lean_st_ref_take(v___y_1022_);
v_traceState_1031_ = lean_ctor_get(v___x_1030_, 4);
v_env_1032_ = lean_ctor_get(v___x_1030_, 0);
v_nextMacroScope_1033_ = lean_ctor_get(v___x_1030_, 1);
v_ngen_1034_ = lean_ctor_get(v___x_1030_, 2);
v_auxDeclNGen_1035_ = lean_ctor_get(v___x_1030_, 3);
v_cache_1036_ = lean_ctor_get(v___x_1030_, 5);
v_recordedDeps_1037_ = lean_ctor_get(v___x_1030_, 6);
v_messages_1038_ = lean_ctor_get(v___x_1030_, 7);
v_infoState_1039_ = lean_ctor_get(v___x_1030_, 8);
v_snapshotTasks_1040_ = lean_ctor_get(v___x_1030_, 9);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1042_ = v___x_1030_;
v_isShared_1043_ = v_isSharedCheck_1070_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_snapshotTasks_1040_);
lean_inc(v_infoState_1039_);
lean_inc(v_messages_1038_);
lean_inc(v_recordedDeps_1037_);
lean_inc(v_cache_1036_);
lean_inc(v_traceState_1031_);
lean_inc(v_auxDeclNGen_1035_);
lean_inc(v_ngen_1034_);
lean_inc(v_nextMacroScope_1033_);
lean_inc(v_env_1032_);
lean_dec(v___x_1030_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1070_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
uint64_t v_tid_1044_; lean_object* v_traces_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1069_; 
v_tid_1044_ = lean_ctor_get_uint64(v_traceState_1031_, sizeof(void*)*1);
v_traces_1045_ = lean_ctor_get(v_traceState_1031_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_traceState_1031_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1047_ = v_traceState_1031_;
v_isShared_1048_ = v_isSharedCheck_1069_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_traces_1045_);
lean_dec(v_traceState_1031_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1069_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; double v___x_1051_; uint8_t v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1049_ = lean_box(0);
v___x_1050_ = lean_box(0);
v___x_1051_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5___closed__0);
v___x_1052_ = 0;
v___x_1053_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___redArg___closed__0));
v___x_1054_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1054_, 0, v_cls_1017_);
lean_ctor_set(v___x_1054_, 1, v___x_1050_);
lean_ctor_set(v___x_1054_, 2, v___x_1053_);
lean_ctor_set_float(v___x_1054_, sizeof(void*)*3, v___x_1051_);
lean_ctor_set_float(v___x_1054_, sizeof(void*)*3 + 8, v___x_1051_);
lean_ctor_set_uint8(v___x_1054_, sizeof(void*)*3 + 16, v___x_1052_);
v___x_1055_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___redArg___closed__1));
v___x_1056_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v_a_1026_);
lean_ctor_set(v___x_1056_, 2, v___x_1055_);
lean_inc(v_ref_1024_);
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v_ref_1024_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = l_Lean_PersistentArray_push___redArg(v_traces_1045_, v___x_1057_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v___x_1058_);
v___x_1060_ = v___x_1047_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1058_);
lean_ctor_set_uint64(v_reuseFailAlloc_1068_, sizeof(void*)*1, v_tid_1044_);
v___x_1060_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1062_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 4, v___x_1060_);
v___x_1062_ = v___x_1042_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_env_1032_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_nextMacroScope_1033_);
lean_ctor_set(v_reuseFailAlloc_1067_, 2, v_ngen_1034_);
lean_ctor_set(v_reuseFailAlloc_1067_, 3, v_auxDeclNGen_1035_);
lean_ctor_set(v_reuseFailAlloc_1067_, 4, v___x_1060_);
lean_ctor_set(v_reuseFailAlloc_1067_, 5, v_cache_1036_);
lean_ctor_set(v_reuseFailAlloc_1067_, 6, v_recordedDeps_1037_);
lean_ctor_set(v_reuseFailAlloc_1067_, 7, v_messages_1038_);
lean_ctor_set(v_reuseFailAlloc_1067_, 8, v_infoState_1039_);
lean_ctor_set(v_reuseFailAlloc_1067_, 9, v_snapshotTasks_1040_);
v___x_1062_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1063_ = lean_st_ref_put(v___y_1022_, v___x_1062_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1049_);
v___x_1065_ = v___x_1028_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1049_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___redArg___boxed(lean_object* v_cls_1072_, lean_object* v_msg_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___redArg(v_cls_1072_, v_msg_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
return v_res_1079_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__5(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__2));
v___x_1090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__4));
v___x_1091_ = l_Lean_Name_append(v___x_1090_, v___x_1089_);
return v___x_1091_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__7(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__6));
v___x_1094_ = l_Lean_stringToMessageData(v___x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2(lean_object* v_as_1095_, size_t v_sz_1096_, size_t v_i_1097_, lean_object* v_b_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_a_1112_; uint8_t v___x_1116_; 
v___x_1116_ = lean_usize_dec_lt(v_i_1097_, v_sz_1096_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v_b_1098_);
return v___x_1117_;
}
else
{
lean_object* v_a_1118_; lean_object* v_toCold_1119_; lean_object* v_options_1120_; lean_object* v_fst_1121_; lean_object* v_snd_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1142_; 
v_a_1118_ = lean_array_uget(v_as_1095_, v_i_1097_);
v_toCold_1119_ = lean_ctor_get(v___y_1108_, 0);
v_options_1120_ = lean_ctor_get(v_toCold_1119_, 2);
v_fst_1121_ = lean_ctor_get(v_a_1118_, 0);
v_snd_1122_ = lean_ctor_get(v_a_1118_, 1);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_a_1118_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1124_ = v_a_1118_;
v_isShared_1125_ = v_isSharedCheck_1142_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_snd_1122_);
lean_inc(v_fst_1121_);
lean_dec(v_a_1118_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1142_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v_inheritedTraceOptions_1126_; uint8_t v_hasTrace_1127_; lean_object* v___x_1128_; 
v_inheritedTraceOptions_1126_ = lean_ctor_get(v_toCold_1119_, 11);
v_hasTrace_1127_ = lean_ctor_get_uint8(v_options_1120_, sizeof(void*)*1);
v___x_1128_ = lean_box(0);
if (v_hasTrace_1127_ == 0)
{
lean_del_object(v___x_1124_);
lean_dec(v_snd_1122_);
lean_dec(v_fst_1121_);
v_a_1112_ = v___x_1128_;
goto v___jp_1111_;
}
else
{
lean_object* v___x_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1129_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__2));
v___x_1130_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__5);
v___x_1131_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1126_, v_options_1120_, v___x_1130_);
if (v___x_1131_ == 0)
{
lean_del_object(v___x_1124_);
lean_dec(v_snd_1122_);
lean_dec(v_fst_1121_);
v_a_1112_ = v___x_1128_;
goto v___jp_1111_;
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1132_ = l_Lean_MessageData_ofName(v_fst_1121_);
v___x_1133_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__7);
if (v_isShared_1125_ == 0)
{
lean_ctor_set_tag(v___x_1124_, 7);
lean_ctor_set(v___x_1124_, 1, v___x_1133_);
lean_ctor_set(v___x_1124_, 0, v___x_1132_);
v___x_1135_ = v___x_1124_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1136_ = l_Nat_reprFast(v_snd_1122_);
v___x_1137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
v___x_1138_ = l_Lean_MessageData_ofFormat(v___x_1137_);
v___x_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1135_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___redArg(v___x_1129_, v___x_1139_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_dec_ref_known(v___x_1140_, 1);
v_a_1112_ = v___x_1128_;
goto v___jp_1111_;
}
else
{
return v___x_1140_;
}
}
}
}
}
}
v___jp_1111_:
{
size_t v___x_1113_; size_t v___x_1114_; 
v___x_1113_ = ((size_t)1ULL);
v___x_1114_ = lean_usize_add(v_i_1097_, v___x_1113_);
v_i_1097_ = v___x_1114_;
v_b_1098_ = v_a_1112_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___boxed(lean_object* v_as_1143_, lean_object* v_sz_1144_, lean_object* v_i_1145_, lean_object* v_b_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
size_t v_sz_boxed_1159_; size_t v_i_boxed_1160_; lean_object* v_res_1161_; 
v_sz_boxed_1159_ = lean_unbox_usize(v_sz_1144_);
lean_dec(v_sz_1144_);
v_i_boxed_1160_ = lean_unbox_usize(v_i_1145_);
lean_dec(v_i_1145_);
v_res_1161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2(v_as_1143_, v_sz_boxed_1159_, v_i_boxed_1160_, v_b_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec_ref(v_as_1143_);
return v_res_1161_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___redArg___lam__0(lean_object* v_a_1162_, lean_object* v_b_1163_){
_start:
{
lean_object* v_snd_1164_; lean_object* v_snd_1165_; uint8_t v___x_1166_; 
v_snd_1164_ = lean_ctor_get(v_b_1163_, 1);
v_snd_1165_ = lean_ctor_get(v_a_1162_, 1);
v___x_1166_ = lean_nat_dec_lt(v_snd_1164_, v_snd_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___redArg___lam__0___boxed(lean_object* v_a_1167_, lean_object* v_b_1168_){
_start:
{
uint8_t v_res_1169_; lean_object* v_r_1170_; 
v_res_1169_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___redArg___lam__0(v_a_1167_, v_b_1168_);
lean_dec_ref(v_b_1168_);
lean_dec_ref(v_a_1167_);
v_r_1170_ = lean_box(v_res_1169_);
return v_r_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6_spec__11___redArg(lean_object* v_hi_1171_, lean_object* v_pivot_1172_, lean_object* v_as_1173_, lean_object* v_i_1174_, lean_object* v_k_1175_){
_start:
{
uint8_t v___x_1176_; 
v___x_1176_ = lean_nat_dec_lt(v_k_1175_, v_hi_1171_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec(v_k_1175_);
v___x_1177_ = lean_array_fswap(v_as_1173_, v_i_1174_, v_hi_1171_);
v___x_1178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1178_, 0, v_i_1174_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
return v___x_1178_;
}
else
{
lean_object* v_snd_1179_; lean_object* v___x_1180_; lean_object* v_snd_1181_; uint8_t v___x_1182_; 
v_snd_1179_ = lean_ctor_get(v_pivot_1172_, 1);
v___x_1180_ = lean_array_fget_borrowed(v_as_1173_, v_k_1175_);
v_snd_1181_ = lean_ctor_get(v___x_1180_, 1);
v___x_1182_ = lean_nat_dec_lt(v_snd_1179_, v_snd_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = lean_unsigned_to_nat(1u);
v___x_1184_ = lean_nat_add(v_k_1175_, v___x_1183_);
lean_dec(v_k_1175_);
v_k_1175_ = v___x_1184_;
goto _start;
}
else
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1186_ = lean_array_fswap(v_as_1173_, v_i_1174_, v_k_1175_);
v___x_1187_ = lean_unsigned_to_nat(1u);
v___x_1188_ = lean_nat_add(v_i_1174_, v___x_1187_);
lean_dec(v_i_1174_);
v___x_1189_ = lean_nat_add(v_k_1175_, v___x_1187_);
lean_dec(v_k_1175_);
v_as_1173_ = v___x_1186_;
v_i_1174_ = v___x_1188_;
v_k_1175_ = v___x_1189_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6_spec__11___redArg___boxed(lean_object* v_hi_1191_, lean_object* v_pivot_1192_, lean_object* v_as_1193_, lean_object* v_i_1194_, lean_object* v_k_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6_spec__11___redArg(v_hi_1191_, v_pivot_1192_, v_as_1193_, v_i_1194_, v_k_1195_);
lean_dec_ref(v_pivot_1192_);
lean_dec(v_hi_1191_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___redArg(lean_object* v_n_1197_, lean_object* v_as_1198_, lean_object* v_lo_1199_, lean_object* v_hi_1200_){
_start:
{
lean_object* v___y_1202_; uint8_t v___x_1212_; 
v___x_1212_ = lean_nat_dec_lt(v_lo_1199_, v_hi_1200_);
if (v___x_1212_ == 0)
{
lean_dec(v_lo_1199_);
return v_as_1198_;
}
else
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v_mid_1215_; lean_object* v___y_1217_; lean_object* v___y_1223_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1213_ = lean_nat_add(v_lo_1199_, v_hi_1200_);
v___x_1214_ = lean_unsigned_to_nat(1u);
v_mid_1215_ = lean_nat_shiftr(v___x_1213_, v___x_1214_);
lean_dec(v___x_1213_);
v___x_1228_ = lean_array_fget_borrowed(v_as_1198_, v_mid_1215_);
v___x_1229_ = lean_array_fget_borrowed(v_as_1198_, v_lo_1199_);
v___x_1230_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___redArg___lam__0(v___x_1228_, v___x_1229_);
if (v___x_1230_ == 0)
{
v___y_1223_ = v_as_1198_;
goto v___jp_1222_;
}
else
{
lean_object* v___x_1231_; 
v___x_1231_ = lean_array_fswap(v_as_1198_, v_lo_1199_, v_mid_1215_);
v___y_1223_ = v___x_1231_;
goto v___jp_1222_;
}
v___jp_1216_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1218_ = lean_array_fget_borrowed(v___y_1217_, v_mid_1215_);
v___x_1219_ = lean_array_fget_borrowed(v___y_1217_, v_hi_1200_);
v___x_1220_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___redArg___lam__0(v___x_1218_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_dec(v_mid_1215_);
v___y_1202_ = v___y_1217_;
goto v___jp_1201_;
}
else
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_array_fswap(v___y_1217_, v_mid_1215_, v_hi_1200_);
lean_dec(v_mid_1215_);
v___y_1202_ = v___x_1221_;
goto v___jp_1201_;
}
}
v___jp_1222_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1224_ = lean_array_fget_borrowed(v___y_1223_, v_hi_1200_);
v___x_1225_ = lean_array_fget_borrowed(v___y_1223_, v_lo_1199_);
v___x_1226_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___redArg___lam__0(v___x_1224_, v___x_1225_);
if (v___x_1226_ == 0)
{
v___y_1217_ = v___y_1223_;
goto v___jp_1216_;
}
else
{
lean_object* v___x_1227_; 
v___x_1227_ = lean_array_fswap(v___y_1223_, v_lo_1199_, v_hi_1200_);
v___y_1217_ = v___x_1227_;
goto v___jp_1216_;
}
}
}
v___jp_1201_:
{
lean_object* v_pivot_1203_; lean_object* v___x_1204_; lean_object* v_fst_1205_; lean_object* v_snd_1206_; uint8_t v___x_1207_; 
v_pivot_1203_ = lean_array_fget(v___y_1202_, v_hi_1200_);
lean_inc_n(v_lo_1199_, 2);
v___x_1204_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6_spec__11___redArg(v_hi_1200_, v_pivot_1203_, v___y_1202_, v_lo_1199_, v_lo_1199_);
lean_dec(v_pivot_1203_);
v_fst_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_fst_1205_);
v_snd_1206_ = lean_ctor_get(v___x_1204_, 1);
lean_inc(v_snd_1206_);
lean_dec_ref(v___x_1204_);
v___x_1207_ = lean_nat_dec_le(v_hi_1200_, v_fst_1205_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1208_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___redArg(v_n_1197_, v_snd_1206_, v_lo_1199_, v_fst_1205_);
v___x_1209_ = lean_unsigned_to_nat(1u);
v___x_1210_ = lean_nat_add(v_fst_1205_, v___x_1209_);
lean_dec(v_fst_1205_);
v_as_1198_ = v___x_1208_;
v_lo_1199_ = v___x_1210_;
goto _start;
}
else
{
lean_dec(v_fst_1205_);
lean_dec(v_lo_1199_);
return v_snd_1206_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___redArg___boxed(lean_object* v_n_1232_, lean_object* v_as_1233_, lean_object* v_lo_1234_, lean_object* v_hi_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___redArg(v_n_1232_, v_as_1233_, v_lo_1234_, v_hi_1235_);
lean_dec(v_hi_1235_);
lean_dec(v_n_1232_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__7(lean_object* v_x_1237_, lean_object* v_x_1238_){
_start:
{
if (lean_obj_tag(v_x_1238_) == 0)
{
return v_x_1237_;
}
else
{
lean_object* v_key_1239_; lean_object* v_value_1240_; lean_object* v_tail_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v_key_1239_ = lean_ctor_get(v_x_1238_, 0);
v_value_1240_ = lean_ctor_get(v_x_1238_, 1);
v_tail_1241_ = lean_ctor_get(v_x_1238_, 2);
lean_inc(v_value_1240_);
lean_inc(v_key_1239_);
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v_key_1239_);
lean_ctor_set(v___x_1242_, 1, v_value_1240_);
v___x_1243_ = lean_array_push(v_x_1237_, v___x_1242_);
v_x_1237_ = v___x_1243_;
v_x_1238_ = v_tail_1241_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__7___boxed(lean_object* v_x_1245_, lean_object* v_x_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__7(v_x_1245_, v_x_1246_);
lean_dec(v_x_1246_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__8(lean_object* v_as_1248_, size_t v_i_1249_, size_t v_stop_1250_, lean_object* v_b_1251_){
_start:
{
uint8_t v___x_1252_; 
v___x_1252_ = lean_usize_dec_eq(v_i_1249_, v_stop_1250_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; size_t v___x_1255_; size_t v___x_1256_; 
v___x_1253_ = lean_array_uget_borrowed(v_as_1248_, v_i_1249_);
v___x_1254_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__7(v_b_1251_, v___x_1253_);
v___x_1255_ = ((size_t)1ULL);
v___x_1256_ = lean_usize_add(v_i_1249_, v___x_1255_);
v_i_1249_ = v___x_1256_;
v_b_1251_ = v___x_1254_;
goto _start;
}
else
{
return v_b_1251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__8___boxed(lean_object* v_as_1258_, lean_object* v_i_1259_, lean_object* v_stop_1260_, lean_object* v_b_1261_){
_start:
{
size_t v_i_boxed_1262_; size_t v_stop_boxed_1263_; lean_object* v_res_1264_; 
v_i_boxed_1262_ = lean_unbox_usize(v_i_1259_);
lean_dec(v_i_1259_);
v_stop_boxed_1263_ = lean_unbox_usize(v_stop_1260_);
lean_dec(v_stop_1260_);
v_res_1264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__8(v_as_1258_, v_i_boxed_1262_, v_stop_boxed_1263_, v_b_1261_);
lean_dec_ref(v_as_1258_);
return v_res_1264_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__10(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1285_ = lean_box(0);
v___x_1286_ = lean_unsigned_to_nat(16u);
v___x_1287_ = lean_mk_array(v___x_1286_, v___x_1285_);
return v___x_1287_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__11(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__10);
v___x_1289_ = lean_unsigned_to_nat(0u);
v___x_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
lean_ctor_set(v___x_1290_, 1, v___x_1288_);
return v___x_1290_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__12(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__11);
v___x_1292_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
lean_ctor_set(v___x_1292_, 2, v___x_1291_);
lean_ctor_set(v___x_1292_, 3, v___x_1291_);
return v___x_1292_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__14(void){
_start:
{
lean_object* v___x_1296_; double v___x_1297_; 
v___x_1296_ = lean_unsigned_to_nat(1000000000u);
v___x_1297_ = lean_float_of_nat(v___x_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg(lean_object* v_k_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v___f_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___f_1313_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__0));
v___x_1314_ = l_Lean_Meta_Tactic_BVDecide_bvNormalizeExt;
v___x_1315_ = l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(v___x_1314_, v_a_1311_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_config_1316_; lean_object* v_a_1317_; lean_object* v_maxSteps_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; lean_object* v___f_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___f_1328_; lean_object* v___f_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v_target_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v_config_1316_ = lean_ctor_get(v_a_1301_, 0);
v_a_1317_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1317_);
lean_dec_ref_known(v___x_1315_, 1);
v_maxSteps_1318_ = lean_ctor_get(v_config_1316_, 1);
v___x_1319_ = lean_unsigned_to_nat(2u);
lean_inc_n(v_maxSteps_1318_, 2);
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v_maxSteps_1318_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
v___x_1321_ = 1;
v___f_1322_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__6));
v___x_1323_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__7));
v___x_1324_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__9));
v___x_1325_ = lean_unsigned_to_nat(0u);
v___x_1326_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__12, &l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__12);
v___x_1327_ = lean_st_mk_ref(v___x_1326_);
lean_inc(v___x_1327_);
v___f_1328_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__7___boxed), 15, 3);
lean_closure_set(v___f_1328_, 0, v___x_1327_);
lean_closure_set(v___f_1328_, 1, v_a_1317_);
lean_closure_set(v___f_1328_, 2, v___x_1324_);
v___f_1329_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__8___boxed), 13, 2);
lean_closure_set(v___f_1329_, 0, v___x_1323_);
lean_closure_set(v___f_1329_, 1, v___f_1328_);
v___x_1330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___f_1322_);
lean_ctor_set(v___x_1330_, 1, v___f_1329_);
v___x_1331_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1331_, 0, v_maxSteps_1318_);
lean_ctor_set_uint8(v___x_1331_, sizeof(void*)*1, v___x_1321_);
v___x_1332_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__13));
v___x_1333_ = lean_st_ref_get(v_a_1302_);
v_target_1334_ = lean_ctor_get(v___x_1333_, 2);
lean_inc_ref(v_target_1334_);
lean_dec(v___x_1333_);
v___x_1335_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_1334_);
lean_dec_ref(v_target_1334_);
v___x_1336_ = lean_apply_4(v_k_1300_, v___x_1332_, v___x_1331_, v___x_1330_, v___x_1320_);
v___x_1337_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__0___redArg(v___x_1335_, v___x_1336_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v___y_1340_; lean_object* v_toCold_1357_; lean_object* v_options_1358_; uint8_t v_hasTrace_1359_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
v_toCold_1357_ = lean_ctor_get(v_a_1310_, 0);
v_options_1358_ = lean_ctor_get(v_toCold_1357_, 2);
v_hasTrace_1359_ = lean_ctor_get_uint8(v_options_1358_, sizeof(void*)*1);
if (v_hasTrace_1359_ == 0)
{
lean_dec(v___x_1327_);
return v___x_1337_;
}
else
{
lean_object* v_inheritedTraceOptions_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v_a_1368_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v_a_1384_; 
v_inheritedTraceOptions_1360_ = lean_ctor_get(v_toCold_1357_, 11);
v___x_1361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__2));
v___x_1362_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__5);
v___x_1363_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1360_, v_options_1358_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_dec(v___x_1327_);
return v___x_1337_;
}
else
{
lean_object* v___x_1393_; lean_object* v___y_1395_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1439_; lean_object* v_statistics_1445_; lean_object* v_size_1446_; lean_object* v_buckets_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
lean_inc(v_a_1338_);
lean_dec_ref_known(v___x_1337_, 1);
v___x_1393_ = lean_st_ref_get(v___x_1327_);
lean_dec(v___x_1327_);
v_statistics_1445_ = lean_ctor_get(v___x_1393_, 3);
lean_inc_ref(v_statistics_1445_);
lean_dec(v___x_1393_);
v_size_1446_ = lean_ctor_get(v_statistics_1445_, 0);
lean_inc(v_size_1446_);
v_buckets_1447_ = lean_ctor_get(v_statistics_1445_, 1);
lean_inc_ref(v_buckets_1447_);
lean_dec_ref(v_statistics_1445_);
v___x_1448_ = lean_mk_empty_array_with_capacity(v_size_1446_);
lean_dec(v_size_1446_);
v___x_1449_ = lean_array_get_size(v_buckets_1447_);
v___x_1450_ = lean_nat_dec_lt(v___x_1325_, v___x_1449_);
if (v___x_1450_ == 0)
{
lean_dec_ref(v_buckets_1447_);
v___y_1439_ = v___x_1448_;
goto v___jp_1438_;
}
else
{
size_t v___x_1451_; size_t v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = ((size_t)0ULL);
v___x_1452_ = lean_usize_of_nat(v___x_1449_);
v___x_1453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__8(v_buckets_1447_, v___x_1451_, v___x_1452_, v___x_1448_);
lean_dec_ref(v_buckets_1447_);
v___y_1439_ = v___x_1453_;
goto v___jp_1438_;
}
v___jp_1394_:
{
lean_object* v___x_1396_; size_t v_sz_1397_; size_t v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v_a_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1396_ = lean_box(0);
v_sz_1397_ = lean_array_size(v___y_1395_);
v___x_1398_ = ((size_t)0ULL);
v___x_1399_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___redArg___closed__0));
v___x_1400_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___redArg(v_a_1311_);
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref(v___x_1400_);
v___x_1402_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1403_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__4(v_options_1358_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = lean_io_mono_nanos_now();
v___x_1405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2(v___y_1395_, v_sz_1397_, v___x_1398_, v___x_1396_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
lean_dec_ref(v___y_1395_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v___x_1406_; 
lean_dec_ref_known(v___x_1405_, 1);
v___x_1406_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__15));
v___y_1365_ = v_a_1401_;
v___y_1366_ = v___x_1399_;
v___y_1367_ = v___x_1404_;
v_a_1368_ = v___x_1406_;
goto v___jp_1364_;
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
v_a_1407_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1405_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1405_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
lean_ctor_set_tag(v___x_1409_, 0);
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
v___y_1365_ = v_a_1401_;
v___y_1366_ = v___x_1399_;
v___y_1367_ = v___x_1404_;
v_a_1368_ = v___x_1412_;
goto v___jp_1364_;
}
}
}
}
else
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = lean_io_get_num_heartbeats();
v___x_1416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2(v___y_1395_, v_sz_1397_, v___x_1398_, v___x_1396_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
lean_dec_ref(v___y_1395_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v___x_1417_; 
lean_dec_ref_known(v___x_1416_, 1);
v___x_1417_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__15));
v___y_1381_ = v_a_1401_;
v___y_1382_ = v___x_1399_;
v___y_1383_ = v___x_1415_;
v_a_1384_ = v___x_1417_;
goto v___jp_1380_;
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1425_; 
v_a_1418_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1420_ = v___x_1416_;
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_a_1418_);
lean_dec(v___x_1416_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1425_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v___x_1423_; 
if (v_isShared_1421_ == 0)
{
lean_ctor_set_tag(v___x_1420_, 0);
v___x_1423_ = v___x_1420_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v_a_1418_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
v___y_1381_ = v_a_1401_;
v___y_1382_ = v___x_1399_;
v___y_1383_ = v___x_1415_;
v_a_1384_ = v___x_1423_;
goto v___jp_1380_;
}
}
}
}
}
v___jp_1426_:
{
lean_object* v___x_1431_; 
v___x_1431_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___redArg(v___y_1428_, v___y_1429_, v___y_1427_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec(v___y_1428_);
v___y_1395_ = v___x_1431_;
goto v___jp_1394_;
}
v___jp_1432_:
{
uint8_t v___x_1437_; 
v___x_1437_ = lean_nat_dec_le(v___y_1436_, v___y_1434_);
if (v___x_1437_ == 0)
{
lean_dec(v___y_1434_);
lean_inc(v___y_1436_);
v___y_1427_ = v___y_1436_;
v___y_1428_ = v___y_1433_;
v___y_1429_ = v___y_1435_;
v___y_1430_ = v___y_1436_;
goto v___jp_1426_;
}
else
{
v___y_1427_ = v___y_1436_;
v___y_1428_ = v___y_1433_;
v___y_1429_ = v___y_1435_;
v___y_1430_ = v___y_1434_;
goto v___jp_1426_;
}
}
v___jp_1438_:
{
lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1440_ = lean_array_get_size(v___y_1439_);
v___x_1441_ = lean_nat_dec_eq(v___x_1440_, v___x_1325_);
if (v___x_1441_ == 0)
{
lean_object* v___x_1442_; lean_object* v___x_1443_; uint8_t v___x_1444_; 
v___x_1442_ = lean_unsigned_to_nat(1u);
v___x_1443_ = lean_nat_sub(v___x_1440_, v___x_1442_);
v___x_1444_ = lean_nat_dec_le(v___x_1325_, v___x_1443_);
if (v___x_1444_ == 0)
{
lean_inc(v___x_1443_);
v___y_1433_ = v___x_1440_;
v___y_1434_ = v___x_1443_;
v___y_1435_ = v___y_1439_;
v___y_1436_ = v___x_1443_;
goto v___jp_1432_;
}
else
{
v___y_1433_ = v___x_1440_;
v___y_1434_ = v___x_1443_;
v___y_1435_ = v___y_1439_;
v___y_1436_ = v___x_1325_;
goto v___jp_1432_;
}
}
else
{
v___y_1395_ = v___y_1439_;
goto v___jp_1394_;
}
}
}
v___jp_1364_:
{
lean_object* v___x_1369_; double v___x_1370_; double v___x_1371_; double v___x_1372_; double v___x_1373_; double v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1369_ = lean_io_mono_nanos_now();
v___x_1370_ = lean_float_of_nat(v___y_1367_);
v___x_1371_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__14, &l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__14);
v___x_1372_ = lean_float_div(v___x_1370_, v___x_1371_);
v___x_1373_ = lean_float_of_nat(v___x_1369_);
v___x_1374_ = lean_float_div(v___x_1373_, v___x_1371_);
v___x_1375_ = lean_box_float(v___x_1372_);
v___x_1376_ = lean_box_float(v___x_1374_);
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v___x_1375_);
lean_ctor_set(v___x_1377_, 1, v___x_1376_);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v_a_1368_);
lean_ctor_set(v___x_1378_, 1, v___x_1377_);
lean_inc_ref(v___y_1366_);
v___x_1379_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5(v___x_1361_, v___x_1321_, v___y_1366_, v_options_1358_, v___x_1363_, v___y_1365_, v___f_1313_, v___x_1378_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1340_ = v___x_1379_;
goto v___jp_1339_;
}
v___jp_1380_:
{
lean_object* v___x_1385_; double v___x_1386_; double v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1385_ = lean_io_get_num_heartbeats();
v___x_1386_ = lean_float_of_nat(v___y_1383_);
v___x_1387_ = lean_float_of_nat(v___x_1385_);
v___x_1388_ = lean_box_float(v___x_1386_);
v___x_1389_ = lean_box_float(v___x_1387_);
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1388_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
v___x_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1391_, 0, v_a_1384_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
lean_inc_ref(v___y_1382_);
v___x_1392_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5(v___x_1361_, v___x_1321_, v___y_1382_, v_options_1358_, v___x_1363_, v___y_1381_, v___f_1313_, v___x_1391_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
v___y_1340_ = v___x_1392_;
goto v___jp_1339_;
}
}
v___jp_1339_:
{
if (lean_obj_tag(v___y_1340_) == 0)
{
lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
v_isSharedCheck_1347_ = !lean_is_exclusive(v___y_1340_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; 
v_unused_1348_ = lean_ctor_get(v___y_1340_, 0);
lean_dec(v_unused_1348_);
v___x_1342_ = v___y_1340_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_dec(v___y_1340_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v_a_1338_);
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1338_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec(v_a_1338_);
v_a_1349_ = lean_ctor_get(v___y_1340_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___y_1340_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___y_1340_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___y_1340_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
else
{
lean_dec(v___x_1327_);
return v___x_1337_;
}
}
else
{
lean_object* v_a_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1461_; 
lean_dec_ref(v_k_1300_);
v_a_1454_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1456_ = v___x_1315_;
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
else
{
lean_inc(v_a_1454_);
lean_dec(v___x_1315_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1461_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1459_; 
if (v_isShared_1457_ == 0)
{
v___x_1459_ = v___x_1456_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_a_1454_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___boxed(lean_object* v_k_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg(v_k_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules(lean_object* v_00_u03b1_1476_, lean_object* v_k_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg(v_k_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___boxed(lean_object* v_00_u03b1_1491_, lean_object* v_k_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules(v_00_u03b1_1491_, v_k_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1(lean_object* v_cls_1506_, lean_object* v_msg_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___redArg(v_cls_1506_, v_msg_1507_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___boxed(lean_object* v_cls_1521_, lean_object* v_msg_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1(v_cls_1521_, v_msg_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__7(lean_object* v_00_u03b1_1536_, lean_object* v_x_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v___x_1550_; 
v___x_1550_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__7___redArg(v_x_1537_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1551_, lean_object* v_x_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__7(v_00_u03b1_1551_, v_x_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6(lean_object* v_n_1566_, lean_object* v_as_1567_, lean_object* v_lo_1568_, lean_object* v_hi_1569_, lean_object* v_w_1570_, lean_object* v_hlo_1571_, lean_object* v_hhi_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___redArg(v_n_1566_, v_as_1567_, v_lo_1568_, v_hi_1569_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___boxed(lean_object* v_n_1574_, lean_object* v_as_1575_, lean_object* v_lo_1576_, lean_object* v_hi_1577_, lean_object* v_w_1578_, lean_object* v_hlo_1579_, lean_object* v_hhi_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6(v_n_1574_, v_as_1575_, v_lo_1576_, v_hi_1577_, v_w_1578_, v_hlo_1579_, v_hhi_1580_);
lean_dec(v_hi_1577_);
lean_dec(v_n_1574_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6(lean_object* v_oldTraces_1582_, lean_object* v_data_1583_, lean_object* v_ref_1584_, lean_object* v_msg_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6___redArg(v_oldTraces_1582_, v_data_1583_, v_ref_1584_, v_msg_1585_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6___boxed(lean_object* v_oldTraces_1599_, lean_object* v_data_1600_, lean_object* v_ref_1601_, lean_object* v_msg_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6(v_oldTraces_1599_, v_data_1600_, v_ref_1601_, v_msg_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6_spec__11(lean_object* v_n_1616_, lean_object* v_lo_1617_, lean_object* v_hi_1618_, lean_object* v_hhi_1619_, lean_object* v_pivot_1620_, lean_object* v_as_1621_, lean_object* v_i_1622_, lean_object* v_k_1623_, lean_object* v_ilo_1624_, lean_object* v_ik_1625_, lean_object* v_w_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6_spec__11___redArg(v_hi_1618_, v_pivot_1620_, v_as_1621_, v_i_1622_, v_k_1623_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6_spec__11___boxed(lean_object* v_n_1628_, lean_object* v_lo_1629_, lean_object* v_hi_1630_, lean_object* v_hhi_1631_, lean_object* v_pivot_1632_, lean_object* v_as_1633_, lean_object* v_i_1634_, lean_object* v_k_1635_, lean_object* v_ilo_1636_, lean_object* v_ik_1637_, lean_object* v_w_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6_spec__11(v_n_1628_, v_lo_1629_, v_hi_1630_, v_hhi_1631_, v_pivot_1632_, v_as_1633_, v_i_1634_, v_k_1635_, v_ilo_1636_, v_ik_1637_, v_w_1638_);
lean_dec_ref(v_pivot_1632_);
lean_dec(v_hi_1630_);
lean_dec(v_lo_1629_);
lean_dec(v_n_1628_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__0(lean_object* v_snd_1640_, lean_object* v_a_1641_, lean_object* v___x_1642_, lean_object* v_____r_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1656_ = lean_array_push(v_snd_1640_, v_a_1641_);
v___x_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1642_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__0___boxed(lean_object* v_snd_1660_, lean_object* v_a_1661_, lean_object* v___x_1662_, lean_object* v_____r_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__0(v_snd_1660_, v_a_1661_, v___x_1662_, v_____r_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
lean_dec(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__1(uint8_t v___x_1677_, lean_object* v___f_1678_, lean_object* v_____r_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; lean_object* v_caches_1693_; lean_object* v_typeAnalysis_1694_; lean_object* v_target_1695_; lean_object* v_hypotheses_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1706_; 
v___x_1692_ = lean_st_ref_take(v___y_1681_);
v_caches_1693_ = lean_ctor_get(v___x_1692_, 0);
v_typeAnalysis_1694_ = lean_ctor_get(v___x_1692_, 1);
v_target_1695_ = lean_ctor_get(v___x_1692_, 2);
v_hypotheses_1696_ = lean_ctor_get(v___x_1692_, 3);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1698_ = v___x_1692_;
v_isShared_1699_ = v_isSharedCheck_1706_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_hypotheses_1696_);
lean_inc(v_target_1695_);
lean_inc(v_typeAnalysis_1694_);
lean_inc(v_caches_1693_);
lean_dec(v___x_1692_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1706_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1700_ = lean_box(0);
if (v_isShared_1699_ == 0)
{
v___x_1702_ = v___x_1698_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_caches_1693_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_typeAnalysis_1694_);
lean_ctor_set(v_reuseFailAlloc_1705_, 2, v_target_1695_);
lean_ctor_set(v_reuseFailAlloc_1705_, 3, v_hypotheses_1696_);
v___x_1702_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_ctor_set_uint8(v___x_1702_, sizeof(void*)*4, v___x_1677_);
v___x_1703_ = lean_st_ref_put(v___y_1681_, v___x_1702_);
lean_inc(v___y_1690_);
lean_inc_ref(v___y_1689_);
lean_inc(v___y_1688_);
lean_inc_ref(v___y_1687_);
lean_inc(v___y_1686_);
lean_inc_ref(v___y_1685_);
lean_inc(v___y_1684_);
lean_inc_ref(v___y_1683_);
lean_inc(v___y_1682_);
lean_inc(v___y_1681_);
lean_inc_ref(v___y_1680_);
v___x_1704_ = lean_apply_13(v___f_1678_, v___x_1700_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, lean_box(0));
return v___x_1704_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__1___boxed(lean_object* v___x_1707_, lean_object* v___f_1708_, lean_object* v_____r_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
uint8_t v___x_22878__boxed_1722_; lean_object* v_res_1723_; 
v___x_22878__boxed_1722_ = lean_unbox(v___x_1707_);
v_res_1723_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__1(v___x_22878__boxed_1722_, v___f_1708_, v_____r_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
return v_res_1723_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0));
v___x_1726_ = l_Lean_stringToMessageData(v___x_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(lean_object* v_upperBound_1727_, lean_object* v___x_1728_, lean_object* v_dsimpMethods_1729_, lean_object* v_dsimpConfig_1730_, lean_object* v_simpMethods_1731_, lean_object* v_simpConfig_1732_, lean_object* v_a_1733_, lean_object* v_b_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v___y_1748_; uint8_t v___x_1770_; 
v___x_1770_ = lean_nat_dec_lt(v_a_1733_, v_upperBound_1727_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; 
lean_dec(v_a_1733_);
lean_dec_ref(v_simpConfig_1732_);
lean_dec_ref(v_simpMethods_1731_);
lean_dec_ref(v_dsimpConfig_1730_);
lean_dec_ref(v_dsimpMethods_1729_);
v___x_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1771_, 0, v_b_1734_);
return v___x_1771_;
}
else
{
lean_object* v_snd_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1856_; 
v_snd_1772_ = lean_ctor_get(v_b_1734_, 1);
v_isSharedCheck_1856_ = !lean_is_exclusive(v_b_1734_);
if (v_isSharedCheck_1856_ == 0)
{
lean_object* v_unused_1857_; 
v_unused_1857_ = lean_ctor_get(v_b_1734_, 0);
lean_dec(v_unused_1857_);
v___x_1774_ = v_b_1734_;
v_isShared_1775_ = v_isSharedCheck_1856_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_snd_1772_);
lean_dec(v_b_1734_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1856_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; lean_object* v___x_1779_; 
v___x_1776_ = lean_box(0);
v___x_1777_ = lean_array_fget_borrowed(v___x_1728_, v_a_1733_);
v___x_1778_ = 0;
lean_inc(v___x_1777_);
lean_inc_ref(v_dsimpConfig_1730_);
lean_inc_ref(v_dsimpMethods_1729_);
v___x_1779_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v___x_1778_, v_dsimpMethods_1729_, v_dsimpConfig_1730_, v___x_1777_, v___y_1736_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; uint8_t v___x_1781_; lean_object* v___x_1782_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
lean_dec_ref_known(v___x_1779_, 1);
v___x_1781_ = 0;
lean_inc_ref(v_simpConfig_1732_);
lean_inc_ref(v_simpMethods_1731_);
v___x_1782_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v___x_1781_, v_simpMethods_1731_, v_simpConfig_1732_, v_a_1780_, v___y_1736_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v_type_1784_; lean_object* v_value_1785_; uint8_t v___x_1786_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1782_, 1);
v_type_1784_ = lean_ctor_get(v_a_1783_, 1);
v_value_1785_ = lean_ctor_get(v_a_1783_, 2);
v___x_1786_ = l_Lean_Expr_isFalse(v_type_1784_);
if (v___x_1786_ == 0)
{
lean_object* v_type_1787_; lean_object* v___f_1788_; uint8_t v___x_1789_; 
lean_del_object(v___x_1774_);
v_type_1787_ = lean_ctor_get(v___x_1777_, 1);
lean_inc(v_a_1783_);
lean_inc(v_snd_1772_);
v___f_1788_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__0___boxed), 16, 3);
lean_closure_set(v___f_1788_, 0, v_snd_1772_);
lean_closure_set(v___f_1788_, 1, v_a_1783_);
lean_closure_set(v___f_1788_, 2, v___x_1776_);
v___x_1789_ = lean_expr_eqv(v_type_1787_, v_type_1784_);
if (v___x_1789_ == 0)
{
lean_object* v_toCold_1790_; lean_object* v_options_1791_; lean_object* v_inheritedTraceOptions_1792_; uint8_t v_hasTrace_1793_; 
lean_inc_ref(v_type_1784_);
lean_dec(v_a_1783_);
lean_dec(v_snd_1772_);
v_toCold_1790_ = lean_ctor_get(v___y_1744_, 0);
v_options_1791_ = lean_ctor_get(v_toCold_1790_, 2);
v_inheritedTraceOptions_1792_ = lean_ctor_get(v_toCold_1790_, 11);
v_hasTrace_1793_ = lean_ctor_get_uint8(v_options_1791_, sizeof(void*)*1);
if (v_hasTrace_1793_ == 0)
{
lean_dec_ref(v_type_1784_);
goto v___jp_1794_;
}
else
{
lean_object* v___x_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v___x_1797_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__2));
v___x_1798_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__5);
v___x_1799_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1792_, v_options_1791_, v___x_1798_);
if (v___x_1799_ == 0)
{
lean_dec_ref(v_type_1784_);
goto v___jp_1794_;
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_inc_ref(v_type_1787_);
v___x_1800_ = l_Lean_MessageData_ofExpr(v_type_1787_);
v___x_1801_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1);
v___x_1802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1800_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v___x_1803_ = l_Lean_MessageData_ofExpr(v_type_1784_);
v___x_1804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1802_);
lean_ctor_set(v___x_1804_, 1, v___x_1803_);
v___x_1805_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___redArg(v___x_1797_, v___x_1804_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1807_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
lean_dec_ref_known(v___x_1805_, 1);
v___x_1807_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__1(v___x_1770_, v___f_1788_, v_a_1806_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
v___y_1748_ = v___x_1807_;
goto v___jp_1747_;
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec_ref(v___f_1788_);
lean_dec(v_a_1733_);
lean_dec_ref(v_simpConfig_1732_);
lean_dec_ref(v_simpMethods_1731_);
lean_dec_ref(v_dsimpConfig_1730_);
lean_dec_ref(v_dsimpMethods_1729_);
v_a_1808_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1805_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1805_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
}
v___jp_1794_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = lean_box(0);
v___x_1796_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__1(v___x_1770_, v___f_1788_, v___x_1795_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
v___y_1748_ = v___x_1796_;
goto v___jp_1747_;
}
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
lean_dec_ref(v___f_1788_);
v___x_1816_ = lean_box(0);
v___x_1817_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__0(v_snd_1772_, v_a_1783_, v___x_1776_, v___x_1816_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
v___y_1748_ = v___x_1817_;
goto v___jp_1747_;
}
}
else
{
lean_object* v___x_1818_; 
lean_inc_ref(v_value_1785_);
lean_dec(v_a_1783_);
lean_dec(v_a_1733_);
lean_dec_ref(v_simpConfig_1732_);
lean_dec_ref(v_simpMethods_1731_);
lean_dec_ref(v_dsimpConfig_1730_);
lean_dec_ref(v_dsimpMethods_1729_);
v___x_1818_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_1785_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1830_; 
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1830_ == 0)
{
lean_object* v_unused_1831_; 
v_unused_1831_ = lean_ctor_get(v___x_1818_, 0);
lean_dec(v_unused_1831_);
v___x_1820_ = v___x_1818_;
v_isShared_1821_ = v_isSharedCheck_1830_;
goto v_resetjp_1819_;
}
else
{
lean_dec(v___x_1818_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1830_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1822_ = lean_box(v___x_1770_);
v___x_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 0, v___x_1823_);
v___x_1825_ = v___x_1774_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_snd_1772_);
v___x_1825_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1827_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1825_);
v___x_1827_ = v___x_1820_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_del_object(v___x_1774_);
lean_dec(v_snd_1772_);
v_a_1832_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1818_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1818_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_del_object(v___x_1774_);
lean_dec(v_snd_1772_);
lean_dec(v_a_1733_);
lean_dec_ref(v_simpConfig_1732_);
lean_dec_ref(v_simpMethods_1731_);
lean_dec_ref(v_dsimpConfig_1730_);
lean_dec_ref(v_dsimpMethods_1729_);
v_a_1840_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1782_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1782_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_del_object(v___x_1774_);
lean_dec(v_snd_1772_);
lean_dec(v_a_1733_);
lean_dec_ref(v_simpConfig_1732_);
lean_dec_ref(v_simpMethods_1731_);
lean_dec_ref(v_dsimpConfig_1730_);
lean_dec_ref(v_dsimpMethods_1729_);
v_a_1848_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1779_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1779_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
}
v___jp_1747_:
{
if (lean_obj_tag(v___y_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1761_; 
v_a_1749_ = lean_ctor_get(v___y_1748_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___y_1748_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1751_ = v___y_1748_;
v_isShared_1752_ = v_isSharedCheck_1761_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___y_1748_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1761_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
if (lean_obj_tag(v_a_1749_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1755_; 
lean_dec(v_a_1733_);
lean_dec_ref(v_simpConfig_1732_);
lean_dec_ref(v_simpMethods_1731_);
lean_dec_ref(v_dsimpConfig_1730_);
lean_dec_ref(v_dsimpMethods_1729_);
v_a_1753_ = lean_ctor_get(v_a_1749_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v_a_1749_, 1);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v_a_1753_);
v___x_1755_ = v___x_1751_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1753_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
lean_del_object(v___x_1751_);
v_a_1757_ = lean_ctor_get(v_a_1749_, 0);
lean_inc(v_a_1757_);
lean_dec_ref_known(v_a_1749_, 1);
v___x_1758_ = lean_unsigned_to_nat(1u);
v___x_1759_ = lean_nat_add(v_a_1733_, v___x_1758_);
lean_dec(v_a_1733_);
v_a_1733_ = v___x_1759_;
v_b_1734_ = v_a_1757_;
goto _start;
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec(v_a_1733_);
lean_dec_ref(v_simpConfig_1732_);
lean_dec_ref(v_simpMethods_1731_);
lean_dec_ref(v_dsimpConfig_1730_);
lean_dec_ref(v_dsimpMethods_1729_);
v_a_1762_ = lean_ctor_get(v___y_1748_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___y_1748_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___y_1748_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___y_1748_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_1858_ = _args[0];
lean_object* v___x_1859_ = _args[1];
lean_object* v_dsimpMethods_1860_ = _args[2];
lean_object* v_dsimpConfig_1861_ = _args[3];
lean_object* v_simpMethods_1862_ = _args[4];
lean_object* v_simpConfig_1863_ = _args[5];
lean_object* v_a_1864_ = _args[6];
lean_object* v_b_1865_ = _args[7];
lean_object* v___y_1866_ = _args[8];
lean_object* v___y_1867_ = _args[9];
lean_object* v___y_1868_ = _args[10];
lean_object* v___y_1869_ = _args[11];
lean_object* v___y_1870_ = _args[12];
lean_object* v___y_1871_ = _args[13];
lean_object* v___y_1872_ = _args[14];
lean_object* v___y_1873_ = _args[15];
lean_object* v___y_1874_ = _args[16];
lean_object* v___y_1875_ = _args[17];
lean_object* v___y_1876_ = _args[18];
lean_object* v___y_1877_ = _args[19];
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v_upperBound_1858_, v___x_1859_, v_dsimpMethods_1860_, v_dsimpConfig_1861_, v_simpMethods_1862_, v_simpConfig_1863_, v_a_1864_, v_b_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec_ref(v___x_1859_);
lean_dec(v_upperBound_1858_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(lean_object* v_dsimpMethods_1879_, lean_object* v_dsimpConfig_1880_, lean_object* v_simpMethods_1881_, lean_object* v_simpConfig_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v___x_1895_; lean_object* v_hypotheses_1896_; lean_object* v___x_1897_; lean_object* v_newHyps_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1895_ = lean_st_ref_get(v___y_1884_);
v_hypotheses_1896_ = lean_ctor_get(v___x_1895_, 3);
lean_inc_ref(v_hypotheses_1896_);
lean_dec(v___x_1895_);
v___x_1897_ = lean_array_get_size(v_hypotheses_1896_);
v_newHyps_1898_ = lean_mk_empty_array_with_capacity(v___x_1897_);
v___x_1899_ = lean_unsigned_to_nat(0u);
v___x_1900_ = lean_box(0);
v___x_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
lean_ctor_set(v___x_1901_, 1, v_newHyps_1898_);
v___x_1902_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v___x_1897_, v_hypotheses_1896_, v_dsimpMethods_1879_, v_dsimpConfig_1880_, v_simpMethods_1881_, v_simpConfig_1882_, v___x_1899_, v___x_1901_, v___y_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec_ref(v_hypotheses_1896_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1932_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1905_ = v___x_1902_;
v_isShared_1906_ = v_isSharedCheck_1932_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1902_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1932_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v_fst_1907_; 
v_fst_1907_ = lean_ctor_get(v_a_1903_, 0);
if (lean_obj_tag(v_fst_1907_) == 0)
{
lean_object* v_snd_1908_; lean_object* v___x_1909_; lean_object* v_caches_1910_; lean_object* v_typeAnalysis_1911_; lean_object* v_target_1912_; uint8_t v_didChange_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1926_; 
v_snd_1908_ = lean_ctor_get(v_a_1903_, 1);
lean_inc(v_snd_1908_);
lean_dec(v_a_1903_);
v___x_1909_ = lean_st_ref_take(v___y_1884_);
v_caches_1910_ = lean_ctor_get(v___x_1909_, 0);
v_typeAnalysis_1911_ = lean_ctor_get(v___x_1909_, 1);
v_target_1912_ = lean_ctor_get(v___x_1909_, 2);
v_didChange_1913_ = lean_ctor_get_uint8(v___x_1909_, sizeof(void*)*4);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1926_ == 0)
{
lean_object* v_unused_1927_; 
v_unused_1927_ = lean_ctor_get(v___x_1909_, 3);
lean_dec(v_unused_1927_);
v___x_1915_ = v___x_1909_;
v_isShared_1916_ = v_isSharedCheck_1926_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_target_1912_);
lean_inc(v_typeAnalysis_1911_);
lean_inc(v_caches_1910_);
lean_dec(v___x_1909_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1926_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 3, v_snd_1908_);
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_caches_1910_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_typeAnalysis_1911_);
lean_ctor_set(v_reuseFailAlloc_1925_, 2, v_target_1912_);
lean_ctor_set(v_reuseFailAlloc_1925_, 3, v_snd_1908_);
lean_ctor_set_uint8(v_reuseFailAlloc_1925_, sizeof(void*)*4, v_didChange_1913_);
v___x_1918_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1919_; uint8_t v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1919_ = lean_st_ref_put(v___y_1884_, v___x_1918_);
v___x_1920_ = 0;
v___x_1921_ = lean_box(v___x_1920_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 0, v___x_1921_);
v___x_1923_ = v___x_1905_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
else
{
lean_object* v_val_1928_; lean_object* v___x_1930_; 
lean_inc_ref(v_fst_1907_);
lean_dec(v_a_1903_);
v_val_1928_ = lean_ctor_get(v_fst_1907_, 0);
lean_inc(v_val_1928_);
lean_dec_ref_known(v_fst_1907_, 1);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 0, v_val_1928_);
v___x_1930_ = v___x_1905_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_val_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
v_a_1933_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1902_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1902_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___boxed(lean_object* v_dsimpMethods_1941_, lean_object* v_dsimpConfig_1942_, lean_object* v_simpMethods_1943_, lean_object* v_simpConfig_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(v_dsimpMethods_1941_, v_dsimpConfig_1942_, v_simpMethods_1943_, v_simpConfig_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0(lean_object* v_upperBound_1968_, lean_object* v___x_1969_, lean_object* v_dsimpMethods_1970_, lean_object* v_dsimpConfig_1971_, lean_object* v_simpMethods_1972_, lean_object* v_simpConfig_1973_, lean_object* v_inst_1974_, lean_object* v_R_1975_, lean_object* v_a_1976_, lean_object* v_b_1977_, lean_object* v_c_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v___x_1991_; 
v___x_1991_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v_upperBound_1968_, v___x_1969_, v_dsimpMethods_1970_, v_dsimpConfig_1971_, v_simpMethods_1972_, v_simpConfig_1973_, v_a_1976_, v_b_1977_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_1992_ = _args[0];
lean_object* v___x_1993_ = _args[1];
lean_object* v_dsimpMethods_1994_ = _args[2];
lean_object* v_dsimpConfig_1995_ = _args[3];
lean_object* v_simpMethods_1996_ = _args[4];
lean_object* v_simpConfig_1997_ = _args[5];
lean_object* v_inst_1998_ = _args[6];
lean_object* v_R_1999_ = _args[7];
lean_object* v_a_2000_ = _args[8];
lean_object* v_b_2001_ = _args[9];
lean_object* v_c_2002_ = _args[10];
lean_object* v___y_2003_ = _args[11];
lean_object* v___y_2004_ = _args[12];
lean_object* v___y_2005_ = _args[13];
lean_object* v___y_2006_ = _args[14];
lean_object* v___y_2007_ = _args[15];
lean_object* v___y_2008_ = _args[16];
lean_object* v___y_2009_ = _args[17];
lean_object* v___y_2010_ = _args[18];
lean_object* v___y_2011_ = _args[19];
lean_object* v___y_2012_ = _args[20];
lean_object* v___y_2013_ = _args[21];
lean_object* v___y_2014_ = _args[22];
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0(v_upperBound_1992_, v___x_1993_, v_dsimpMethods_1994_, v_dsimpConfig_1995_, v_simpMethods_1996_, v_simpConfig_1997_, v_inst_1998_, v_R_1999_, v_a_2000_, v_b_2001_, v_c_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec_ref(v___x_1993_);
lean_dec(v_upperBound_1992_);
return v_res_2015_;
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

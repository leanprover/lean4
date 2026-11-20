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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpControl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_Simp_evalGround___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteDsimproc___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_evalGround___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Tactic_BVDecide_bvNormalizeExt;
lean_object* l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
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
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofProp"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__3_value),LEAN_SCALAR_PTR_LITERAL(189, 0, 62, 153, 37, 253, 54, 88)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__4_value),LEAN_SCALAR_PTR_LITERAL(153, 71, 30, 209, 57, 12, 129, 48)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
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
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),((lean_object*)(((size_t)(65536) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__6_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_evalGround___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__6_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__7_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__7_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__9;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__10;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__11;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(255) << 1) | 1)),((lean_object*)(((size_t)(65536) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__12_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__8___boxed, .m_arity = 13, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__12_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__4_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__13_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__1_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__15;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__16_value;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5(uint8_t v___x_412_, lean_object* v_e_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_424_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___closed__5));
v___x_425_ = lean_unsigned_to_nat(1u);
v___x_426_ = l_Lean_Expr_isAppOfArity(v_e_413_, v___x_424_, v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Meta_Sym_Simp_simpControl(v_e_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_, v___y_422_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_456_; 
v_a_428_ = lean_ctor_get(v___x_427_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_456_ == 0)
{
v___x_430_ = v___x_427_;
v_isShared_431_ = v_isSharedCheck_456_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_427_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_456_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
if (lean_obj_tag(v_a_428_) == 0)
{
uint8_t v_contextDependent_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_442_; 
v_contextDependent_432_ = lean_ctor_get_uint8(v_a_428_, 1);
v_isSharedCheck_442_ = !lean_is_exclusive(v_a_428_);
if (v_isSharedCheck_442_ == 0)
{
v___x_434_ = v_a_428_;
v_isShared_435_ = v_isSharedCheck_442_;
goto v_resetjp_433_;
}
else
{
lean_dec(v_a_428_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_442_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_441_, 1, v_contextDependent_432_);
v___x_437_ = v_reuseFailAlloc_441_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_439_; 
lean_ctor_set_uint8(v___x_437_, 0, v___x_426_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_437_);
v___x_439_ = v___x_430_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
else
{
lean_object* v_e_x27_443_; lean_object* v_proof_444_; uint8_t v_contextDependent_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_455_; 
v_e_x27_443_ = lean_ctor_get(v_a_428_, 0);
v_proof_444_ = lean_ctor_get(v_a_428_, 1);
v_contextDependent_445_ = lean_ctor_get_uint8(v_a_428_, sizeof(void*)*2 + 1);
v_isSharedCheck_455_ = !lean_is_exclusive(v_a_428_);
if (v_isSharedCheck_455_ == 0)
{
v___x_447_ = v_a_428_;
v_isShared_448_ = v_isSharedCheck_455_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_proof_444_);
lean_inc(v_e_x27_443_);
lean_dec(v_a_428_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_455_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_e_x27_443_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_proof_444_);
lean_ctor_set_uint8(v_reuseFailAlloc_454_, sizeof(void*)*2 + 1, v_contextDependent_445_);
v___x_450_ = v_reuseFailAlloc_454_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_452_; 
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*2, v___x_426_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_450_);
v___x_452_ = v___x_430_;
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
}
else
{
return v___x_427_;
}
}
else
{
uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec_ref(v_e_413_);
v___x_457_ = 0;
v___x_458_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_458_, 0, v___x_412_);
lean_ctor_set_uint8(v___x_458_, 1, v___x_457_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
return v___x_459_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5___boxed(lean_object* v___x_460_, lean_object* v_e_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
uint8_t v___x_178302__boxed_472_; lean_object* v_res_473_; 
v___x_178302__boxed_472_ = lean_unbox(v___x_460_);
v_res_473_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__5(v___x_178302__boxed_472_, v_e_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6(lean_object* v_val_474_, lean_object* v_a_475_, lean_object* v___x_476_, lean_object* v_x_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v___x_489_; 
lean_inc_ref(v___y_478_);
v___x_489_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteSimproc(v_val_474_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
if (lean_obj_tag(v_a_490_) == 0)
{
uint8_t v_done_491_; 
v_done_491_ = lean_ctor_get_uint8(v_a_490_, 0);
if (v_done_491_ == 0)
{
uint8_t v_contextDependent_492_; lean_object* v___x_493_; 
lean_dec_ref_known(v___x_489_, 1);
v_contextDependent_492_ = lean_ctor_get_uint8(v_a_490_, 1);
lean_dec_ref_known(v_a_490_, 0);
v___x_493_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_475_, v___x_476_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; uint8_t v___y_496_; 
v_a_494_ = lean_ctor_get(v___x_493_, 0);
if (v_contextDependent_492_ == 0)
{
return v___x_493_;
}
else
{
if (lean_obj_tag(v_a_494_) == 0)
{
uint8_t v_contextDependent_506_; 
v_contextDependent_506_ = lean_ctor_get_uint8(v_a_494_, 1);
v___y_496_ = v_contextDependent_506_;
goto v___jp_495_;
}
else
{
uint8_t v_contextDependent_507_; 
v_contextDependent_507_ = lean_ctor_get_uint8(v_a_494_, sizeof(void*)*2 + 1);
v___y_496_ = v_contextDependent_507_;
goto v___jp_495_;
}
}
v___jp_495_:
{
if (v___y_496_ == 0)
{
lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_504_; 
lean_inc(v_a_494_);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_504_ == 0)
{
lean_object* v_unused_505_; 
v_unused_505_ = lean_ctor_get(v___x_493_, 0);
lean_dec(v_unused_505_);
v___x_498_ = v___x_493_;
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
else
{
lean_dec(v___x_493_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_504_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_500_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_494_);
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_500_);
v___x_502_ = v___x_498_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
else
{
return v___x_493_;
}
}
}
else
{
return v___x_493_;
}
}
else
{
lean_dec_ref_known(v_a_490_, 0);
lean_dec_ref(v___y_478_);
lean_dec_ref(v___x_476_);
return v___x_489_;
}
}
else
{
uint8_t v_done_508_; 
v_done_508_ = lean_ctor_get_uint8(v_a_490_, sizeof(void*)*2);
if (v_done_508_ == 0)
{
lean_object* v_e_x27_509_; lean_object* v_proof_510_; uint8_t v_contextDependent_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_561_; 
lean_dec_ref_known(v___x_489_, 1);
v_e_x27_509_ = lean_ctor_get(v_a_490_, 0);
v_proof_510_ = lean_ctor_get(v_a_490_, 1);
v_contextDependent_511_ = lean_ctor_get_uint8(v_a_490_, sizeof(void*)*2 + 1);
v_isSharedCheck_561_ = !lean_is_exclusive(v_a_490_);
if (v_isSharedCheck_561_ == 0)
{
v___x_513_ = v_a_490_;
v_isShared_514_ = v_isSharedCheck_561_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_proof_510_);
lean_inc(v_e_x27_509_);
lean_dec(v_a_490_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_561_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; 
lean_inc_ref(v_e_x27_509_);
v___x_515_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_475_, v___x_476_, v_e_x27_509_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_560_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_560_ == 0)
{
v___x_518_ = v___x_515_;
v_isShared_519_ = v_isSharedCheck_560_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_560_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
if (lean_obj_tag(v_a_516_) == 0)
{
uint8_t v_done_520_; uint8_t v_contextDependent_521_; uint8_t v___y_523_; 
lean_dec_ref(v___y_478_);
v_done_520_ = lean_ctor_get_uint8(v_a_516_, 0);
v_contextDependent_521_ = lean_ctor_get_uint8(v_a_516_, 1);
lean_dec_ref_known(v_a_516_, 0);
if (v_contextDependent_511_ == 0)
{
v___y_523_ = v_contextDependent_521_;
goto v___jp_522_;
}
else
{
v___y_523_ = v_contextDependent_511_;
goto v___jp_522_;
}
v___jp_522_:
{
lean_object* v___x_525_; 
if (v_isShared_514_ == 0)
{
v___x_525_ = v___x_513_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_e_x27_509_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_proof_510_);
v___x_525_ = v_reuseFailAlloc_529_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_527_; 
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*2, v_done_520_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*2 + 1, v___y_523_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_525_);
v___x_527_ = v___x_518_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
else
{
lean_object* v_e_x27_530_; lean_object* v_proof_531_; uint8_t v_done_532_; uint8_t v_contextDependent_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_559_; 
lean_del_object(v___x_518_);
lean_del_object(v___x_513_);
v_e_x27_530_ = lean_ctor_get(v_a_516_, 0);
v_proof_531_ = lean_ctor_get(v_a_516_, 1);
v_done_532_ = lean_ctor_get_uint8(v_a_516_, sizeof(void*)*2);
v_contextDependent_533_ = lean_ctor_get_uint8(v_a_516_, sizeof(void*)*2 + 1);
v_isSharedCheck_559_ = !lean_is_exclusive(v_a_516_);
if (v_isSharedCheck_559_ == 0)
{
v___x_535_ = v_a_516_;
v_isShared_536_ = v_isSharedCheck_559_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_proof_531_);
lean_inc(v_e_x27_530_);
lean_dec(v_a_516_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_559_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; 
lean_inc_ref(v_e_x27_530_);
v___x_537_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_478_, v_e_x27_509_, v_proof_510_, v_e_x27_530_, v_proof_531_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_550_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_550_ == 0)
{
v___x_540_ = v___x_537_;
v_isShared_541_ = v_isSharedCheck_550_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_537_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_550_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
uint8_t v___y_543_; 
if (v_contextDependent_511_ == 0)
{
v___y_543_ = v_contextDependent_533_;
goto v___jp_542_;
}
else
{
v___y_543_ = v_contextDependent_511_;
goto v___jp_542_;
}
v___jp_542_:
{
lean_object* v___x_545_; 
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 1, v_a_538_);
v___x_545_ = v___x_535_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_e_x27_530_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_a_538_);
lean_ctor_set_uint8(v_reuseFailAlloc_549_, sizeof(void*)*2, v_done_532_);
v___x_545_ = v_reuseFailAlloc_549_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_547_; 
lean_ctor_set_uint8(v___x_545_, sizeof(void*)*2 + 1, v___y_543_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v___x_545_);
v___x_547_ = v___x_540_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_545_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
lean_del_object(v___x_535_);
lean_dec_ref(v_e_x27_530_);
v_a_551_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_537_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_537_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_513_);
lean_dec_ref(v_proof_510_);
lean_dec_ref(v_e_x27_509_);
lean_dec_ref(v___y_478_);
return v___x_515_;
}
}
}
else
{
lean_dec_ref_known(v_a_490_, 2);
lean_dec_ref(v___y_478_);
lean_dec_ref(v___x_476_);
return v___x_489_;
}
}
}
else
{
lean_dec_ref(v___y_478_);
lean_dec_ref(v___x_476_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___boxed(lean_object* v_val_562_, lean_object* v_a_563_, lean_object* v___x_564_, lean_object* v_x_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6(v_val_562_, v_a_563_, v___x_564_, v_x_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v_a_563_);
lean_dec(v_val_562_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__7(lean_object* v___x_578_, lean_object* v___f_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_box(0);
v___x_592_ = l___private_Lean_Meta_Sym_Simp_EvalGround_0__Lean_Meta_Sym_Simp_evalGroundCore___redArg(v___y_580_, v___x_578_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
if (lean_obj_tag(v_a_593_) == 0)
{
uint8_t v_done_594_; 
v_done_594_ = lean_ctor_get_uint8(v_a_593_, 0);
if (v_done_594_ == 0)
{
uint8_t v_contextDependent_595_; lean_object* v___x_596_; 
lean_dec_ref_known(v___x_592_, 1);
v_contextDependent_595_ = lean_ctor_get_uint8(v_a_593_, 1);
lean_dec_ref_known(v_a_593_, 0);
v___x_596_ = lean_apply_12(v___f_579_, v___x_591_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, lean_box(0));
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; uint8_t v___y_599_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
if (v_contextDependent_595_ == 0)
{
lean_dec(v_a_597_);
return v___x_596_;
}
else
{
if (lean_obj_tag(v_a_597_) == 0)
{
uint8_t v_contextDependent_609_; 
v_contextDependent_609_ = lean_ctor_get_uint8(v_a_597_, 1);
v___y_599_ = v_contextDependent_609_;
goto v___jp_598_;
}
else
{
uint8_t v_contextDependent_610_; 
v_contextDependent_610_ = lean_ctor_get_uint8(v_a_597_, sizeof(void*)*2 + 1);
v___y_599_ = v_contextDependent_610_;
goto v___jp_598_;
}
}
v___jp_598_:
{
if (v___y_599_ == 0)
{
lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_607_; 
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_607_ == 0)
{
lean_object* v_unused_608_; 
v_unused_608_ = lean_ctor_get(v___x_596_, 0);
lean_dec(v_unused_608_);
v___x_601_ = v___x_596_;
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
else
{
lean_dec(v___x_596_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_607_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_603_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_597_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_603_);
v___x_605_ = v___x_601_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
else
{
lean_dec(v_a_597_);
return v___x_596_;
}
}
}
else
{
return v___x_596_;
}
}
else
{
lean_dec_ref_known(v_a_593_, 0);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec_ref(v___f_579_);
return v___x_592_;
}
}
else
{
uint8_t v_done_611_; 
v_done_611_ = lean_ctor_get_uint8(v_a_593_, sizeof(void*)*2);
if (v_done_611_ == 0)
{
lean_object* v_e_x27_612_; lean_object* v_proof_613_; uint8_t v_contextDependent_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_664_; 
lean_dec_ref_known(v___x_592_, 1);
v_e_x27_612_ = lean_ctor_get(v_a_593_, 0);
v_proof_613_ = lean_ctor_get(v_a_593_, 1);
v_contextDependent_614_ = lean_ctor_get_uint8(v_a_593_, sizeof(void*)*2 + 1);
v_isSharedCheck_664_ = !lean_is_exclusive(v_a_593_);
if (v_isSharedCheck_664_ == 0)
{
v___x_616_ = v_a_593_;
v_isShared_617_ = v_isSharedCheck_664_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_proof_613_);
lean_inc(v_e_x27_612_);
lean_dec(v_a_593_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_664_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; 
lean_inc(v___y_589_);
lean_inc_ref(v___y_588_);
lean_inc(v___y_587_);
lean_inc_ref(v___y_586_);
lean_inc(v___y_585_);
lean_inc_ref(v___y_584_);
lean_inc_ref(v_e_x27_612_);
v___x_618_ = lean_apply_12(v___f_579_, v___x_591_, v_e_x27_612_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, lean_box(0));
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_663_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_663_ == 0)
{
v___x_621_ = v___x_618_;
v_isShared_622_ = v_isSharedCheck_663_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_618_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_663_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
if (lean_obj_tag(v_a_619_) == 0)
{
uint8_t v_done_623_; uint8_t v_contextDependent_624_; uint8_t v___y_626_; 
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec_ref(v___y_580_);
v_done_623_ = lean_ctor_get_uint8(v_a_619_, 0);
v_contextDependent_624_ = lean_ctor_get_uint8(v_a_619_, 1);
lean_dec_ref_known(v_a_619_, 0);
if (v_contextDependent_614_ == 0)
{
v___y_626_ = v_contextDependent_624_;
goto v___jp_625_;
}
else
{
v___y_626_ = v_contextDependent_614_;
goto v___jp_625_;
}
v___jp_625_:
{
lean_object* v___x_628_; 
if (v_isShared_617_ == 0)
{
v___x_628_ = v___x_616_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_e_x27_612_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_proof_613_);
v___x_628_ = v_reuseFailAlloc_632_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_630_; 
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*2, v_done_623_);
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*2 + 1, v___y_626_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_628_);
v___x_630_ = v___x_621_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
else
{
lean_object* v_e_x27_633_; lean_object* v_proof_634_; uint8_t v_done_635_; uint8_t v_contextDependent_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_662_; 
lean_del_object(v___x_621_);
lean_del_object(v___x_616_);
v_e_x27_633_ = lean_ctor_get(v_a_619_, 0);
v_proof_634_ = lean_ctor_get(v_a_619_, 1);
v_done_635_ = lean_ctor_get_uint8(v_a_619_, sizeof(void*)*2);
v_contextDependent_636_ = lean_ctor_get_uint8(v_a_619_, sizeof(void*)*2 + 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v_a_619_);
if (v_isSharedCheck_662_ == 0)
{
v___x_638_ = v_a_619_;
v_isShared_639_ = v_isSharedCheck_662_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_proof_634_);
lean_inc(v_e_x27_633_);
lean_dec(v_a_619_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_662_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; 
lean_inc_ref(v_e_x27_633_);
v___x_640_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v___y_580_, v_e_x27_612_, v_proof_613_, v_e_x27_633_, v_proof_634_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_653_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_653_ == 0)
{
v___x_643_ = v___x_640_;
v_isShared_644_ = v_isSharedCheck_653_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_640_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_653_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
uint8_t v___y_646_; 
if (v_contextDependent_614_ == 0)
{
v___y_646_ = v_contextDependent_636_;
goto v___jp_645_;
}
else
{
v___y_646_ = v_contextDependent_614_;
goto v___jp_645_;
}
v___jp_645_:
{
lean_object* v___x_648_; 
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 1, v_a_641_);
v___x_648_ = v___x_638_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_e_x27_633_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_a_641_);
lean_ctor_set_uint8(v_reuseFailAlloc_652_, sizeof(void*)*2, v_done_635_);
v___x_648_ = v_reuseFailAlloc_652_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_650_; 
lean_ctor_set_uint8(v___x_648_, sizeof(void*)*2 + 1, v___y_646_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_648_);
v___x_650_ = v___x_643_;
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
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_del_object(v___x_638_);
lean_dec_ref(v_e_x27_633_);
v_a_654_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_640_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_640_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_616_);
lean_dec_ref(v_proof_613_);
lean_dec_ref(v_e_x27_612_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec_ref(v___y_580_);
return v___x_618_;
}
}
}
else
{
lean_dec_ref_known(v_a_593_, 2);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec_ref(v___f_579_);
return v___x_592_;
}
}
}
else
{
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec_ref(v___f_579_);
return v___x_592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__7___boxed(lean_object* v___x_665_, lean_object* v___f_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__7(v___x_665_, v___f_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec_ref(v___x_665_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__8(lean_object* v___x_679_, lean_object* v___f_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_box(0);
v___x_693_ = l_Lean_Meta_Sym_DSimp_evalGround___redArg(v___x_679_, v___y_681_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
if (lean_obj_tag(v_a_694_) == 0)
{
uint8_t v_done_695_; 
v_done_695_ = lean_ctor_get_uint8(v_a_694_, 0);
lean_dec_ref_known(v_a_694_, 0);
if (v_done_695_ == 0)
{
lean_object* v___x_696_; 
lean_dec_ref_known(v___x_693_, 1);
v___x_696_ = lean_apply_12(v___f_680_, v___x_692_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, lean_box(0));
return v___x_696_;
}
else
{
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec_ref(v___f_680_);
return v___x_693_;
}
}
else
{
uint8_t v_done_697_; 
lean_dec_ref(v___y_681_);
v_done_697_ = lean_ctor_get_uint8(v_a_694_, sizeof(void*)*1);
if (v_done_697_ == 0)
{
lean_object* v_e_x27_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_716_; 
lean_dec_ref_known(v___x_693_, 1);
v_e_x27_698_ = lean_ctor_get(v_a_694_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v_a_694_);
if (v_isSharedCheck_716_ == 0)
{
v___x_700_ = v_a_694_;
v_isShared_701_ = v_isSharedCheck_716_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_e_x27_698_);
lean_dec(v_a_694_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_716_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; 
lean_inc_ref(v_e_x27_698_);
v___x_702_ = lean_apply_12(v___f_680_, v___x_692_, v_e_x27_698_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, lean_box(0));
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
if (lean_obj_tag(v_a_703_) == 0)
{
lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_714_; 
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; 
v_unused_715_ = lean_ctor_get(v___x_702_, 0);
lean_dec(v_unused_715_);
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_714_;
goto v_resetjp_704_;
}
else
{
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_714_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
uint8_t v_done_707_; lean_object* v___x_709_; 
v_done_707_ = lean_ctor_get_uint8(v_a_703_, 0);
lean_dec_ref_known(v_a_703_, 0);
if (v_isShared_701_ == 0)
{
v___x_709_ = v___x_700_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_e_x27_698_);
v___x_709_ = v_reuseFailAlloc_713_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_711_; 
lean_ctor_set_uint8(v___x_709_, sizeof(void*)*1, v_done_707_);
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
}
else
{
lean_dec_ref_known(v_a_703_, 1);
lean_del_object(v___x_700_);
lean_dec_ref(v_e_x27_698_);
return v___x_702_;
}
}
else
{
lean_del_object(v___x_700_);
lean_dec_ref(v_e_x27_698_);
return v___x_702_;
}
}
}
else
{
lean_dec_ref_known(v_a_694_, 1);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___f_680_);
return v___x_693_;
}
}
}
else
{
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec_ref(v___f_680_);
return v___x_693_;
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
lean_inc(v___y_919_);
v___x_921_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6___redArg(v_oldTraces_900_, v_data_920_, v___y_919_, v___y_918_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
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
v___y_918_ = v_a_929_;
v___y_919_ = v___y_928_;
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
v___y_918_ = v_a_929_;
v___y_919_ = v___y_928_;
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
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__9(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1283_ = lean_box(0);
v___x_1284_ = lean_unsigned_to_nat(16u);
v___x_1285_ = lean_mk_array(v___x_1284_, v___x_1283_);
return v___x_1285_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__10(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1286_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__9, &l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__9);
v___x_1287_ = lean_unsigned_to_nat(0u);
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
lean_ctor_set(v___x_1288_, 1, v___x_1286_);
return v___x_1288_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__11(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__10, &l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__10);
v___x_1290_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
lean_ctor_set(v___x_1290_, 2, v___x_1289_);
lean_ctor_set(v___x_1290_, 3, v___x_1289_);
return v___x_1290_;
}
}
static double _init_l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__15(void){
_start:
{
lean_object* v___x_1300_; double v___x_1301_; 
v___x_1300_ = lean_unsigned_to_nat(1000000000u);
v___x_1301_ = lean_float_of_nat(v___x_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg(lean_object* v_k_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_){
_start:
{
lean_object* v___f_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___f_1317_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__0));
v___x_1318_ = l_Lean_Meta_Tactic_BVDecide_bvNormalizeExt;
v___x_1319_ = l_Lean_Meta_Sym_Simp_SymSimpExtension_getTheorems___redArg(v___x_1318_, v_a_1315_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v_config_1320_; lean_object* v_a_1321_; lean_object* v_maxSteps_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; lean_object* v___f_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___f_1332_; lean_object* v___f_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v_target_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v_config_1320_ = lean_ctor_get(v_a_1305_, 0);
v_a_1321_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1321_);
lean_dec_ref_known(v___x_1319_, 1);
v_maxSteps_1322_ = lean_ctor_get(v_config_1320_, 1);
v___x_1323_ = lean_unsigned_to_nat(2u);
lean_inc_n(v_maxSteps_1322_, 2);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v_maxSteps_1322_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
v___x_1325_ = 1;
v___f_1326_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__5));
v___x_1327_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__6));
v___x_1328_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__8));
v___x_1329_ = lean_unsigned_to_nat(0u);
v___x_1330_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__11, &l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__11);
v___x_1331_ = lean_st_mk_ref(v___x_1330_);
lean_inc(v___x_1331_);
v___f_1332_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__6___boxed), 15, 3);
lean_closure_set(v___f_1332_, 0, v___x_1331_);
lean_closure_set(v___f_1332_, 1, v_a_1321_);
lean_closure_set(v___f_1332_, 2, v___x_1328_);
v___f_1333_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___lam__7___boxed), 13, 2);
lean_closure_set(v___f_1333_, 0, v___x_1327_);
lean_closure_set(v___f_1333_, 1, v___f_1332_);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___f_1326_);
lean_ctor_set(v___x_1334_, 1, v___f_1333_);
v___x_1335_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1335_, 0, v_maxSteps_1322_);
lean_ctor_set_uint8(v___x_1335_, sizeof(void*)*1, v___x_1325_);
v___x_1336_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__14));
v___x_1337_ = lean_st_ref_get(v_a_1306_);
v_target_1338_ = lean_ctor_get(v___x_1337_, 2);
lean_inc_ref(v_target_1338_);
lean_dec(v___x_1337_);
v___x_1339_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_1338_);
lean_dec_ref(v_target_1338_);
v___x_1340_ = lean_apply_4(v_k_1304_, v___x_1336_, v___x_1335_, v___x_1334_, v___x_1324_);
v___x_1341_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__0___redArg(v___x_1339_, v___x_1340_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___y_1344_; lean_object* v_toCold_1361_; lean_object* v_options_1362_; uint8_t v_hasTrace_1363_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_toCold_1361_ = lean_ctor_get(v_a_1314_, 0);
v_options_1362_ = lean_ctor_get(v_toCold_1361_, 2);
v_hasTrace_1363_ = lean_ctor_get_uint8(v_options_1362_, sizeof(void*)*1);
if (v_hasTrace_1363_ == 0)
{
lean_dec(v___x_1331_);
return v___x_1341_;
}
else
{
lean_object* v_inheritedTraceOptions_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; uint8_t v___x_1367_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v_a_1372_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v_a_1388_; 
v_inheritedTraceOptions_1364_ = lean_ctor_get(v_toCold_1361_, 11);
v___x_1365_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__2));
v___x_1366_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__5);
v___x_1367_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1364_, v_options_1362_, v___x_1366_);
if (v___x_1367_ == 0)
{
lean_dec(v___x_1331_);
return v___x_1341_;
}
else
{
lean_object* v___x_1397_; lean_object* v___y_1399_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1443_; lean_object* v_statistics_1449_; lean_object* v_size_1450_; lean_object* v_buckets_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
lean_inc(v_a_1342_);
lean_dec_ref_known(v___x_1341_, 1);
v___x_1397_ = lean_st_ref_get(v___x_1331_);
lean_dec(v___x_1331_);
v_statistics_1449_ = lean_ctor_get(v___x_1397_, 3);
lean_inc_ref(v_statistics_1449_);
lean_dec(v___x_1397_);
v_size_1450_ = lean_ctor_get(v_statistics_1449_, 0);
lean_inc(v_size_1450_);
v_buckets_1451_ = lean_ctor_get(v_statistics_1449_, 1);
lean_inc_ref(v_buckets_1451_);
lean_dec_ref(v_statistics_1449_);
v___x_1452_ = lean_mk_empty_array_with_capacity(v_size_1450_);
lean_dec(v_size_1450_);
v___x_1453_ = lean_array_get_size(v_buckets_1451_);
v___x_1454_ = lean_nat_dec_lt(v___x_1329_, v___x_1453_);
if (v___x_1454_ == 0)
{
lean_dec_ref(v_buckets_1451_);
v___y_1443_ = v___x_1452_;
goto v___jp_1442_;
}
else
{
size_t v___x_1455_; size_t v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = ((size_t)0ULL);
v___x_1456_ = lean_usize_of_nat(v___x_1453_);
v___x_1457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__8(v_buckets_1451_, v___x_1455_, v___x_1456_, v___x_1452_);
lean_dec_ref(v_buckets_1451_);
v___y_1443_ = v___x_1457_;
goto v___jp_1442_;
}
v___jp_1398_:
{
lean_object* v___x_1400_; size_t v_sz_1401_; size_t v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v_a_1405_; lean_object* v___x_1406_; uint8_t v___x_1407_; 
v___x_1400_ = lean_box(0);
v_sz_1401_ = lean_array_size(v___y_1399_);
v___x_1402_ = ((size_t)0ULL);
v___x_1403_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___redArg___closed__0));
v___x_1404_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__3___redArg(v_a_1315_);
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref(v___x_1404_);
v___x_1406_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1407_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__4(v_options_1362_, v___x_1406_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_io_mono_nanos_now();
v___x_1409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2(v___y_1399_, v_sz_1401_, v___x_1402_, v___x_1400_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
lean_dec_ref(v___y_1399_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v___x_1410_; 
lean_dec_ref_known(v___x_1409_, 1);
v___x_1410_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__16));
v___y_1369_ = v___x_1403_;
v___y_1370_ = v___x_1408_;
v___y_1371_ = v_a_1405_;
v_a_1372_ = v___x_1410_;
goto v___jp_1368_;
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
v_a_1411_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1409_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1409_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set_tag(v___x_1413_, 0);
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
v___y_1369_ = v___x_1403_;
v___y_1370_ = v___x_1408_;
v___y_1371_ = v_a_1405_;
v_a_1372_ = v___x_1416_;
goto v___jp_1368_;
}
}
}
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
v___x_1419_ = lean_io_get_num_heartbeats();
v___x_1420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2(v___y_1399_, v_sz_1401_, v___x_1402_, v___x_1400_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
lean_dec_ref(v___y_1399_);
if (lean_obj_tag(v___x_1420_) == 0)
{
lean_object* v___x_1421_; 
lean_dec_ref_known(v___x_1420_, 1);
v___x_1421_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__16));
v___y_1385_ = v___x_1419_;
v___y_1386_ = v___x_1403_;
v___y_1387_ = v_a_1405_;
v_a_1388_ = v___x_1421_;
goto v___jp_1384_;
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
v_a_1422_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1420_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1420_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set_tag(v___x_1424_, 0);
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
v___y_1385_ = v___x_1419_;
v___y_1386_ = v___x_1403_;
v___y_1387_ = v_a_1405_;
v_a_1388_ = v___x_1427_;
goto v___jp_1384_;
}
}
}
}
}
v___jp_1430_:
{
lean_object* v___x_1435_; 
v___x_1435_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___redArg(v___y_1433_, v___y_1432_, v___y_1431_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec(v___y_1433_);
v___y_1399_ = v___x_1435_;
goto v___jp_1398_;
}
v___jp_1436_:
{
uint8_t v___x_1441_; 
v___x_1441_ = lean_nat_dec_le(v___y_1440_, v___y_1437_);
if (v___x_1441_ == 0)
{
lean_dec(v___y_1437_);
lean_inc(v___y_1440_);
v___y_1431_ = v___y_1440_;
v___y_1432_ = v___y_1438_;
v___y_1433_ = v___y_1439_;
v___y_1434_ = v___y_1440_;
goto v___jp_1430_;
}
else
{
v___y_1431_ = v___y_1440_;
v___y_1432_ = v___y_1438_;
v___y_1433_ = v___y_1439_;
v___y_1434_ = v___y_1437_;
goto v___jp_1430_;
}
}
v___jp_1442_:
{
lean_object* v___x_1444_; uint8_t v___x_1445_; 
v___x_1444_ = lean_array_get_size(v___y_1443_);
v___x_1445_ = lean_nat_dec_eq(v___x_1444_, v___x_1329_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1446_ = lean_unsigned_to_nat(1u);
v___x_1447_ = lean_nat_sub(v___x_1444_, v___x_1446_);
v___x_1448_ = lean_nat_dec_le(v___x_1329_, v___x_1447_);
if (v___x_1448_ == 0)
{
lean_inc(v___x_1447_);
v___y_1437_ = v___x_1447_;
v___y_1438_ = v___y_1443_;
v___y_1439_ = v___x_1444_;
v___y_1440_ = v___x_1447_;
goto v___jp_1436_;
}
else
{
v___y_1437_ = v___x_1447_;
v___y_1438_ = v___y_1443_;
v___y_1439_ = v___x_1444_;
v___y_1440_ = v___x_1329_;
goto v___jp_1436_;
}
}
else
{
v___y_1399_ = v___y_1443_;
goto v___jp_1398_;
}
}
}
v___jp_1368_:
{
lean_object* v___x_1373_; double v___x_1374_; double v___x_1375_; double v___x_1376_; double v___x_1377_; double v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1373_ = lean_io_mono_nanos_now();
v___x_1374_ = lean_float_of_nat(v___y_1370_);
v___x_1375_ = lean_float_once(&l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__15, &l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___closed__15);
v___x_1376_ = lean_float_div(v___x_1374_, v___x_1375_);
v___x_1377_ = lean_float_of_nat(v___x_1373_);
v___x_1378_ = lean_float_div(v___x_1377_, v___x_1375_);
v___x_1379_ = lean_box_float(v___x_1376_);
v___x_1380_ = lean_box_float(v___x_1378_);
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1379_);
lean_ctor_set(v___x_1381_, 1, v___x_1380_);
v___x_1382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1382_, 0, v_a_1372_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
lean_inc_ref(v___y_1369_);
v___x_1383_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5(v___x_1365_, v___x_1325_, v___y_1369_, v_options_1362_, v___x_1367_, v___y_1371_, v___f_1317_, v___x_1382_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
v___y_1344_ = v___x_1383_;
goto v___jp_1343_;
}
v___jp_1384_:
{
lean_object* v___x_1389_; double v___x_1390_; double v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1389_ = lean_io_get_num_heartbeats();
v___x_1390_ = lean_float_of_nat(v___y_1385_);
v___x_1391_ = lean_float_of_nat(v___x_1389_);
v___x_1392_ = lean_box_float(v___x_1390_);
v___x_1393_ = lean_box_float(v___x_1391_);
v___x_1394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1392_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1395_, 0, v_a_1388_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
lean_inc_ref(v___y_1386_);
v___x_1396_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5(v___x_1365_, v___x_1325_, v___y_1386_, v_options_1362_, v___x_1367_, v___y_1387_, v___f_1317_, v___x_1395_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_);
v___y_1344_ = v___x_1396_;
goto v___jp_1343_;
}
}
v___jp_1343_:
{
if (lean_obj_tag(v___y_1344_) == 0)
{
lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
v_isSharedCheck_1351_ = !lean_is_exclusive(v___y_1344_);
if (v_isSharedCheck_1351_ == 0)
{
lean_object* v_unused_1352_; 
v_unused_1352_ = lean_ctor_get(v___y_1344_, 0);
lean_dec(v_unused_1352_);
v___x_1346_ = v___y_1344_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_dec(v___y_1344_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v_a_1342_);
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1342_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
lean_dec(v_a_1342_);
v_a_1353_ = lean_ctor_get(v___y_1344_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___y_1344_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___y_1344_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___y_1344_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
else
{
lean_dec(v___x_1331_);
return v___x_1341_;
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec_ref(v_k_1304_);
v_a_1458_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1319_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1319_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg___boxed(lean_object* v_k_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_, lean_object* v_a_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg(v_k_1466_, v_a_1467_, v_a_1468_, v_a_1469_, v_a_1470_, v_a_1471_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
lean_dec(v_a_1475_);
lean_dec_ref(v_a_1474_);
lean_dec(v_a_1473_);
lean_dec_ref(v_a_1472_);
lean_dec(v_a_1471_);
lean_dec_ref(v_a_1470_);
lean_dec(v_a_1469_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules(lean_object* v_00_u03b1_1480_, lean_object* v_k_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___redArg(v_k_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules___boxed(lean_object* v_00_u03b1_1495_, lean_object* v_k_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules(v_00_u03b1_1495_, v_k_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1(lean_object* v_cls_1510_, lean_object* v_msg_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___redArg(v_cls_1510_, v_msg_1511_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___boxed(lean_object* v_cls_1525_, lean_object* v_msg_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1(v_cls_1525_, v_msg_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__7(lean_object* v_00_u03b1_1540_, lean_object* v_x_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__7___redArg(v_x_1541_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1555_, lean_object* v_x_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__7(v_00_u03b1_1555_, v_x_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6(lean_object* v_n_1570_, lean_object* v_as_1571_, lean_object* v_lo_1572_, lean_object* v_hi_1573_, lean_object* v_w_1574_, lean_object* v_hlo_1575_, lean_object* v_hhi_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___redArg(v_n_1570_, v_as_1571_, v_lo_1572_, v_hi_1573_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6___boxed(lean_object* v_n_1578_, lean_object* v_as_1579_, lean_object* v_lo_1580_, lean_object* v_hi_1581_, lean_object* v_w_1582_, lean_object* v_hlo_1583_, lean_object* v_hhi_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6(v_n_1578_, v_as_1579_, v_lo_1580_, v_hi_1581_, v_w_1582_, v_hlo_1583_, v_hhi_1584_);
lean_dec(v_hi_1581_);
lean_dec(v_n_1578_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6(lean_object* v_oldTraces_1586_, lean_object* v_data_1587_, lean_object* v_ref_1588_, lean_object* v_msg_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6___redArg(v_oldTraces_1586_, v_data_1587_, v_ref_1588_, v_msg_1589_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6___boxed(lean_object* v_oldTraces_1603_, lean_object* v_data_1604_, lean_object* v_ref_1605_, lean_object* v_msg_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__5_spec__6(v_oldTraces_1603_, v_data_1604_, v_ref_1605_, v_msg_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6_spec__11(lean_object* v_n_1620_, lean_object* v_lo_1621_, lean_object* v_hi_1622_, lean_object* v_hhi_1623_, lean_object* v_pivot_1624_, lean_object* v_as_1625_, lean_object* v_i_1626_, lean_object* v_k_1627_, lean_object* v_ilo_1628_, lean_object* v_ik_1629_, lean_object* v_w_1630_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6_spec__11___redArg(v_hi_1622_, v_pivot_1624_, v_as_1625_, v_i_1626_, v_k_1627_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6_spec__11___boxed(lean_object* v_n_1632_, lean_object* v_lo_1633_, lean_object* v_hi_1634_, lean_object* v_hhi_1635_, lean_object* v_pivot_1636_, lean_object* v_as_1637_, lean_object* v_i_1638_, lean_object* v_k_1639_, lean_object* v_ilo_1640_, lean_object* v_ik_1641_, lean_object* v_w_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__6_spec__11(v_n_1632_, v_lo_1633_, v_hi_1634_, v_hhi_1635_, v_pivot_1636_, v_as_1637_, v_i_1638_, v_k_1639_, v_ilo_1640_, v_ik_1641_, v_w_1642_);
lean_dec_ref(v_pivot_1636_);
lean_dec(v_hi_1634_);
lean_dec(v_lo_1633_);
lean_dec(v_n_1632_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__0(lean_object* v_snd_1644_, lean_object* v_a_1645_, lean_object* v___x_1646_, lean_object* v_____r_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1660_ = lean_array_push(v_snd_1644_, v_a_1645_);
v___x_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1646_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
v___x_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
v___x_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1663_, 0, v___x_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__0___boxed(lean_object* v_snd_1664_, lean_object* v_a_1665_, lean_object* v___x_1666_, lean_object* v_____r_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__0(v_snd_1664_, v_a_1665_, v___x_1666_, v_____r_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
lean_dec(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__1(uint8_t v___x_1681_, lean_object* v___f_1682_, lean_object* v_____r_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v___x_1696_; lean_object* v_caches_1697_; lean_object* v_typeAnalysis_1698_; lean_object* v_target_1699_; lean_object* v_hypotheses_1700_; lean_object* v_eprBvProblem_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1711_; 
v___x_1696_ = lean_st_ref_take(v___y_1685_);
v_caches_1697_ = lean_ctor_get(v___x_1696_, 0);
v_typeAnalysis_1698_ = lean_ctor_get(v___x_1696_, 1);
v_target_1699_ = lean_ctor_get(v___x_1696_, 2);
v_hypotheses_1700_ = lean_ctor_get(v___x_1696_, 3);
v_eprBvProblem_1701_ = lean_ctor_get(v___x_1696_, 4);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1703_ = v___x_1696_;
v_isShared_1704_ = v_isSharedCheck_1711_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_eprBvProblem_1701_);
lean_inc(v_hypotheses_1700_);
lean_inc(v_target_1699_);
lean_inc(v_typeAnalysis_1698_);
lean_inc(v_caches_1697_);
lean_dec(v___x_1696_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1711_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1705_; lean_object* v___x_1707_; 
v___x_1705_ = lean_box(0);
if (v_isShared_1704_ == 0)
{
v___x_1707_ = v___x_1703_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_caches_1697_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_typeAnalysis_1698_);
lean_ctor_set(v_reuseFailAlloc_1710_, 2, v_target_1699_);
lean_ctor_set(v_reuseFailAlloc_1710_, 3, v_hypotheses_1700_);
lean_ctor_set(v_reuseFailAlloc_1710_, 4, v_eprBvProblem_1701_);
v___x_1707_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
lean_ctor_set_uint8(v___x_1707_, sizeof(void*)*5, v___x_1681_);
v___x_1708_ = lean_st_ref_put(v___y_1685_, v___x_1707_);
lean_inc(v___y_1694_);
lean_inc_ref(v___y_1693_);
lean_inc(v___y_1692_);
lean_inc_ref(v___y_1691_);
lean_inc(v___y_1690_);
lean_inc_ref(v___y_1689_);
lean_inc(v___y_1688_);
lean_inc_ref(v___y_1687_);
lean_inc(v___y_1686_);
lean_inc(v___y_1685_);
lean_inc_ref(v___y_1684_);
v___x_1709_ = lean_apply_13(v___f_1682_, v___x_1705_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, lean_box(0));
return v___x_1709_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__1___boxed(lean_object* v___x_1712_, lean_object* v___f_1713_, lean_object* v_____r_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
uint8_t v___x_23020__boxed_1727_; lean_object* v_res_1728_; 
v___x_23020__boxed_1727_ = lean_unbox(v___x_1712_);
v_res_1728_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__1(v___x_23020__boxed_1727_, v___f_1713_, v_____r_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
return v_res_1728_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1730_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__0));
v___x_1731_ = l_Lean_stringToMessageData(v___x_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(lean_object* v_upperBound_1732_, lean_object* v___x_1733_, lean_object* v_dsimpMethods_1734_, lean_object* v_dsimpConfig_1735_, lean_object* v_simpMethods_1736_, lean_object* v_simpConfig_1737_, lean_object* v_a_1738_, lean_object* v_b_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v___y_1753_; uint8_t v___x_1775_; 
v___x_1775_ = lean_nat_dec_lt(v_a_1738_, v_upperBound_1732_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; 
lean_dec(v_a_1738_);
lean_dec_ref(v_simpConfig_1737_);
lean_dec_ref(v_simpMethods_1736_);
lean_dec_ref(v_dsimpConfig_1735_);
lean_dec_ref(v_dsimpMethods_1734_);
v___x_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1776_, 0, v_b_1739_);
return v___x_1776_;
}
else
{
lean_object* v_snd_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1861_; 
v_snd_1777_ = lean_ctor_get(v_b_1739_, 1);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_b_1739_);
if (v_isSharedCheck_1861_ == 0)
{
lean_object* v_unused_1862_; 
v_unused_1862_ = lean_ctor_get(v_b_1739_, 0);
lean_dec(v_unused_1862_);
v___x_1779_ = v_b_1739_;
v_isShared_1780_ = v_isSharedCheck_1861_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_snd_1777_);
lean_dec(v_b_1739_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1861_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; uint8_t v___x_1783_; lean_object* v___x_1784_; 
v___x_1781_ = lean_box(0);
v___x_1782_ = lean_array_fget_borrowed(v___x_1733_, v_a_1738_);
v___x_1783_ = 0;
lean_inc(v___x_1782_);
lean_inc_ref(v_dsimpConfig_1735_);
lean_inc_ref(v_dsimpMethods_1734_);
v___x_1784_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_dsimpHyp___redArg(v___x_1783_, v_dsimpMethods_1734_, v_dsimpConfig_1735_, v___x_1782_, v___y_1741_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; uint8_t v___x_1786_; lean_object* v___x_1787_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref_known(v___x_1784_, 1);
v___x_1786_ = 0;
lean_inc_ref(v_simpConfig_1737_);
lean_inc_ref(v_simpMethods_1736_);
v___x_1787_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_simpHyp___redArg(v___x_1786_, v_simpMethods_1736_, v_simpConfig_1737_, v_a_1785_, v___y_1741_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v_type_1789_; lean_object* v_value_1790_; uint8_t v___x_1791_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v___x_1787_, 1);
v_type_1789_ = lean_ctor_get(v_a_1788_, 1);
v_value_1790_ = lean_ctor_get(v_a_1788_, 2);
v___x_1791_ = l_Lean_Expr_isFalse(v_type_1789_);
if (v___x_1791_ == 0)
{
lean_object* v_type_1792_; lean_object* v___f_1793_; uint8_t v___x_1794_; 
lean_del_object(v___x_1779_);
v_type_1792_ = lean_ctor_get(v___x_1782_, 1);
lean_inc(v_a_1788_);
lean_inc(v_snd_1777_);
v___f_1793_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__0___boxed), 16, 3);
lean_closure_set(v___f_1793_, 0, v_snd_1777_);
lean_closure_set(v___f_1793_, 1, v_a_1788_);
lean_closure_set(v___f_1793_, 2, v___x_1781_);
v___x_1794_ = lean_expr_eqv(v_type_1792_, v_type_1789_);
if (v___x_1794_ == 0)
{
lean_object* v_toCold_1795_; lean_object* v_options_1796_; lean_object* v_inheritedTraceOptions_1797_; uint8_t v_hasTrace_1798_; 
lean_inc_ref(v_type_1789_);
lean_dec(v_a_1788_);
lean_dec(v_snd_1777_);
v_toCold_1795_ = lean_ctor_get(v___y_1749_, 0);
v_options_1796_ = lean_ctor_get(v_toCold_1795_, 2);
v_inheritedTraceOptions_1797_ = lean_ctor_get(v_toCold_1795_, 11);
v_hasTrace_1798_ = lean_ctor_get_uint8(v_options_1796_, sizeof(void*)*1);
if (v_hasTrace_1798_ == 0)
{
lean_dec_ref(v_type_1789_);
goto v___jp_1799_;
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v___x_1802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__2));
v___x_1803_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__2___closed__5);
v___x_1804_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1797_, v_options_1796_, v___x_1803_);
if (v___x_1804_ == 0)
{
lean_dec_ref(v_type_1789_);
goto v___jp_1799_;
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_inc_ref(v_type_1792_);
v___x_1805_ = l_Lean_MessageData_ofExpr(v_type_1792_);
v___x_1806_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___closed__1);
v___x_1807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1805_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = l_Lean_MessageData_ofExpr(v_type_1789_);
v___x_1809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1807_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_Normalize_withRewriteRules_spec__1___redArg(v___x_1802_, v___x_1809_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1812_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_a_1811_);
lean_dec_ref_known(v___x_1810_, 1);
v___x_1812_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__1(v___x_1775_, v___f_1793_, v_a_1811_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
v___y_1753_ = v___x_1812_;
goto v___jp_1752_;
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec_ref(v___f_1793_);
lean_dec(v_a_1738_);
lean_dec_ref(v_simpConfig_1737_);
lean_dec_ref(v_simpMethods_1736_);
lean_dec_ref(v_dsimpConfig_1735_);
lean_dec_ref(v_dsimpMethods_1734_);
v_a_1813_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1810_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1810_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
}
v___jp_1799_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = lean_box(0);
v___x_1801_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__1(v___x_1775_, v___f_1793_, v___x_1800_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
v___y_1753_ = v___x_1801_;
goto v___jp_1752_;
}
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_dec_ref(v___f_1793_);
v___x_1821_ = lean_box(0);
v___x_1822_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___lam__0(v_snd_1777_, v_a_1788_, v___x_1781_, v___x_1821_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
v___y_1753_ = v___x_1822_;
goto v___jp_1752_;
}
}
else
{
lean_object* v___x_1823_; 
lean_inc_ref(v_value_1790_);
lean_dec(v_a_1788_);
lean_dec(v_a_1738_);
lean_dec_ref(v_simpConfig_1737_);
lean_dec_ref(v_simpMethods_1736_);
lean_dec_ref(v_dsimpConfig_1735_);
lean_dec_ref(v_dsimpMethods_1734_);
v___x_1823_ = l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_closeTarget___redArg(v_value_1790_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1835_; 
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1835_ == 0)
{
lean_object* v_unused_1836_; 
v_unused_1836_ = lean_ctor_get(v___x_1823_, 0);
lean_dec(v_unused_1836_);
v___x_1825_ = v___x_1823_;
v_isShared_1826_ = v_isSharedCheck_1835_;
goto v_resetjp_1824_;
}
else
{
lean_dec(v___x_1823_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1835_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1827_ = lean_box(v___x_1775_);
v___x_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1828_);
v___x_1830_ = v___x_1779_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1828_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_snd_1777_);
v___x_1830_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1832_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1830_);
v___x_1832_ = v___x_1825_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1830_);
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
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
lean_del_object(v___x_1779_);
lean_dec(v_snd_1777_);
v_a_1837_ = lean_ctor_get(v___x_1823_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1823_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1823_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_del_object(v___x_1779_);
lean_dec(v_snd_1777_);
lean_dec(v_a_1738_);
lean_dec_ref(v_simpConfig_1737_);
lean_dec_ref(v_simpMethods_1736_);
lean_dec_ref(v_dsimpConfig_1735_);
lean_dec_ref(v_dsimpMethods_1734_);
v_a_1845_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1787_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1787_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_a_1845_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_del_object(v___x_1779_);
lean_dec(v_snd_1777_);
lean_dec(v_a_1738_);
lean_dec_ref(v_simpConfig_1737_);
lean_dec_ref(v_simpMethods_1736_);
lean_dec_ref(v_dsimpConfig_1735_);
lean_dec_ref(v_dsimpMethods_1734_);
v_a_1853_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1784_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1784_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
v___jp_1752_:
{
if (lean_obj_tag(v___y_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1766_; 
v_a_1754_ = lean_ctor_get(v___y_1753_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___y_1753_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1756_ = v___y_1753_;
v_isShared_1757_ = v_isSharedCheck_1766_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___y_1753_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1766_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
if (lean_obj_tag(v_a_1754_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1760_; 
lean_dec(v_a_1738_);
lean_dec_ref(v_simpConfig_1737_);
lean_dec_ref(v_simpMethods_1736_);
lean_dec_ref(v_dsimpConfig_1735_);
lean_dec_ref(v_dsimpMethods_1734_);
v_a_1758_ = lean_ctor_get(v_a_1754_, 0);
lean_inc(v_a_1758_);
lean_dec_ref_known(v_a_1754_, 1);
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v_a_1758_);
v___x_1760_ = v___x_1756_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
lean_del_object(v___x_1756_);
v_a_1762_ = lean_ctor_get(v_a_1754_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v_a_1754_, 1);
v___x_1763_ = lean_unsigned_to_nat(1u);
v___x_1764_ = lean_nat_add(v_a_1738_, v___x_1763_);
lean_dec(v_a_1738_);
v_a_1738_ = v___x_1764_;
v_b_1739_ = v_a_1762_;
goto _start;
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec(v_a_1738_);
lean_dec_ref(v_simpConfig_1737_);
lean_dec_ref(v_simpMethods_1736_);
lean_dec_ref(v_dsimpConfig_1735_);
lean_dec_ref(v_dsimpMethods_1734_);
v_a_1767_ = lean_ctor_get(v___y_1753_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___y_1753_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___y_1753_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___y_1753_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1772_; 
if (v_isShared_1770_ == 0)
{
v___x_1772_ = v___x_1769_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1767_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_upperBound_1863_ = _args[0];
lean_object* v___x_1864_ = _args[1];
lean_object* v_dsimpMethods_1865_ = _args[2];
lean_object* v_dsimpConfig_1866_ = _args[3];
lean_object* v_simpMethods_1867_ = _args[4];
lean_object* v_simpConfig_1868_ = _args[5];
lean_object* v_a_1869_ = _args[6];
lean_object* v_b_1870_ = _args[7];
lean_object* v___y_1871_ = _args[8];
lean_object* v___y_1872_ = _args[9];
lean_object* v___y_1873_ = _args[10];
lean_object* v___y_1874_ = _args[11];
lean_object* v___y_1875_ = _args[12];
lean_object* v___y_1876_ = _args[13];
lean_object* v___y_1877_ = _args[14];
lean_object* v___y_1878_ = _args[15];
lean_object* v___y_1879_ = _args[16];
lean_object* v___y_1880_ = _args[17];
lean_object* v___y_1881_ = _args[18];
lean_object* v___y_1882_ = _args[19];
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v_upperBound_1863_, v___x_1864_, v_dsimpMethods_1865_, v_dsimpConfig_1866_, v_simpMethods_1867_, v_simpConfig_1868_, v_a_1869_, v_b_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec_ref(v___x_1864_);
lean_dec(v_upperBound_1863_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(lean_object* v_dsimpMethods_1884_, lean_object* v_dsimpConfig_1885_, lean_object* v_simpMethods_1886_, lean_object* v_simpConfig_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v___x_1900_; lean_object* v_hypotheses_1901_; lean_object* v___x_1902_; lean_object* v_newHyps_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1900_ = lean_st_ref_get(v___y_1889_);
v_hypotheses_1901_ = lean_ctor_get(v___x_1900_, 3);
lean_inc_ref(v_hypotheses_1901_);
lean_dec(v___x_1900_);
v___x_1902_ = lean_array_get_size(v_hypotheses_1901_);
v_newHyps_1903_ = lean_mk_empty_array_with_capacity(v___x_1902_);
v___x_1904_ = lean_unsigned_to_nat(0u);
v___x_1905_ = lean_box(0);
v___x_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
lean_ctor_set(v___x_1906_, 1, v_newHyps_1903_);
v___x_1907_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v___x_1902_, v_hypotheses_1901_, v_dsimpMethods_1884_, v_dsimpConfig_1885_, v_simpMethods_1886_, v_simpConfig_1887_, v___x_1904_, v___x_1906_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec_ref(v_hypotheses_1901_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1938_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1910_ = v___x_1907_;
v_isShared_1911_ = v_isSharedCheck_1938_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1907_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1938_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v_fst_1912_; 
v_fst_1912_ = lean_ctor_get(v_a_1908_, 0);
if (lean_obj_tag(v_fst_1912_) == 0)
{
lean_object* v_snd_1913_; lean_object* v___x_1914_; lean_object* v_caches_1915_; lean_object* v_typeAnalysis_1916_; lean_object* v_target_1917_; uint8_t v_didChange_1918_; lean_object* v_eprBvProblem_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1932_; 
v_snd_1913_ = lean_ctor_get(v_a_1908_, 1);
lean_inc(v_snd_1913_);
lean_dec(v_a_1908_);
v___x_1914_ = lean_st_ref_take(v___y_1889_);
v_caches_1915_ = lean_ctor_get(v___x_1914_, 0);
v_typeAnalysis_1916_ = lean_ctor_get(v___x_1914_, 1);
v_target_1917_ = lean_ctor_get(v___x_1914_, 2);
v_didChange_1918_ = lean_ctor_get_uint8(v___x_1914_, sizeof(void*)*5);
v_eprBvProblem_1919_ = lean_ctor_get(v___x_1914_, 4);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; 
v_unused_1933_ = lean_ctor_get(v___x_1914_, 3);
lean_dec(v_unused_1933_);
v___x_1921_ = v___x_1914_;
v_isShared_1922_ = v_isSharedCheck_1932_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_eprBvProblem_1919_);
lean_inc(v_target_1917_);
lean_inc(v_typeAnalysis_1916_);
lean_inc(v_caches_1915_);
lean_dec(v___x_1914_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1932_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 3, v_snd_1913_);
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_caches_1915_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_typeAnalysis_1916_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_target_1917_);
lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_snd_1913_);
lean_ctor_set(v_reuseFailAlloc_1931_, 4, v_eprBvProblem_1919_);
lean_ctor_set_uint8(v_reuseFailAlloc_1931_, sizeof(void*)*5, v_didChange_1918_);
v___x_1924_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1925_; uint8_t v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1929_; 
v___x_1925_ = lean_st_ref_put(v___y_1889_, v___x_1924_);
v___x_1926_ = 0;
v___x_1927_ = lean_box(v___x_1926_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v___x_1927_);
v___x_1929_ = v___x_1910_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
else
{
lean_object* v_val_1934_; lean_object* v___x_1936_; 
lean_inc_ref(v_fst_1912_);
lean_dec(v_a_1908_);
v_val_1934_ = lean_ctor_get(v_fst_1912_, 0);
lean_inc(v_val_1934_);
lean_dec_ref_known(v_fst_1912_, 1);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v_val_1934_);
v___x_1936_ = v___x_1910_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_val_1934_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
v_a_1939_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1907_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1907_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0___boxed(lean_object* v_dsimpMethods_1947_, lean_object* v_dsimpConfig_1948_, lean_object* v_simpMethods_1949_, lean_object* v_simpConfig_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass___lam__0(v_dsimpMethods_1947_, v_dsimpConfig_1948_, v_simpMethods_1949_, v_simpConfig_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
return v_res_1963_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0(lean_object* v_upperBound_1974_, lean_object* v___x_1975_, lean_object* v_dsimpMethods_1976_, lean_object* v_dsimpConfig_1977_, lean_object* v_simpMethods_1978_, lean_object* v_simpConfig_1979_, lean_object* v_inst_1980_, lean_object* v_R_1981_, lean_object* v_a_1982_, lean_object* v_b_1983_, lean_object* v_c_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___redArg(v_upperBound_1974_, v___x_1975_, v_dsimpMethods_1976_, v_dsimpConfig_1977_, v_simpMethods_1978_, v_simpConfig_1979_, v_a_1982_, v_b_1983_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0___boxed(lean_object** _args){
lean_object* v_upperBound_1998_ = _args[0];
lean_object* v___x_1999_ = _args[1];
lean_object* v_dsimpMethods_2000_ = _args[2];
lean_object* v_dsimpConfig_2001_ = _args[3];
lean_object* v_simpMethods_2002_ = _args[4];
lean_object* v_simpConfig_2003_ = _args[5];
lean_object* v_inst_2004_ = _args[6];
lean_object* v_R_2005_ = _args[7];
lean_object* v_a_2006_ = _args[8];
lean_object* v_b_2007_ = _args[9];
lean_object* v_c_2008_ = _args[10];
lean_object* v___y_2009_ = _args[11];
lean_object* v___y_2010_ = _args[12];
lean_object* v___y_2011_ = _args[13];
lean_object* v___y_2012_ = _args[14];
lean_object* v___y_2013_ = _args[15];
lean_object* v___y_2014_ = _args[16];
lean_object* v___y_2015_ = _args[17];
lean_object* v___y_2016_ = _args[18];
lean_object* v___y_2017_ = _args[19];
lean_object* v___y_2018_ = _args[20];
lean_object* v___y_2019_ = _args[21];
lean_object* v___y_2020_ = _args[22];
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Tactic_BVDecide_Normalize_rewriteRulesPass_spec__0(v_upperBound_1998_, v___x_1999_, v_dsimpMethods_2000_, v_dsimpConfig_2001_, v_simpMethods_2002_, v_simpConfig_2003_, v_inst_2004_, v_R_2005_, v_a_2006_, v_b_2007_, v_c_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec_ref(v___x_1999_);
lean_dec(v_upperBound_1998_);
return v_res_2021_;
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
